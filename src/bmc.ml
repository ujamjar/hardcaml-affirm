(* Bounded Model Checking for HardCaml circuits with LTL property checking.
  
   The main API function is 'run ~k ltl' which will iteratively run
   bounded model checking for 0, then 1, up to 'k' time steps against the 
   property specification given by 'ltl'.

   Note; the LTL formula is not negated by the functions here and should
   be passed negated in order to prove properties or find counter-examples.

   Note; the circuit which is extracted is derived only from the atomic
   propositions in the LTL formula.

   Implementation notes:

   * 'unroll's circuit for k time steps.
   * connects register(state) inputs/outputs between adjacent time steps.
   * generates transition propositions ('and' of 'xnor' of state between steps)
   * generates atomic propositions for each step
   * compiles a bounded path for the LTL formula
     * deals with cases both with and without loops seperately (as per Biere paper)
   * generates a sat problem and runs a solver
   * iterates to next time step
*)



module Init_state(B : HardCaml.Comb.S)(B_sim : HardCaml.Comb.S) = struct

  open HardCaml.Signal.Types

  let init_state signal = 
    match signal with
    | Signal_reg(_, r) as s ->
      (* pick reset or clear value as init value XXX revisit this! *)
      if r.reg_reset_value <> Signal_empty then B.const (const_value r.reg_reset_value)
      else if r.reg_clear_value <> Signal_empty then B.const (const_value r.reg_clear_value)
      else B.zero (width s)
    | _ -> failwith "expecting register"


  let init_from_sim sim signal = 
    try 
      let v = !(sim.HardCaml.Cyclesim.Api.sim_lookup_signal (uid signal)) in
      B.const (B_sim.to_bstr v)
    with _ -> 
      init_state signal

end

module Unroller(B : HardCaml.Comb.S) = struct

  open HardCaml 
  open Signal.Types 

  module I = Init_state(B)(HardCaml.Bits.Comb.IntbitsList)

  let is_input s = 
    is_wire s && deps s = [ Signal_empty ]

  let rec search1' set pre post arg signal = 
      if UidSet.mem (uid signal) set then
          (arg, set)
      else
          let set = UidSet.add (uid signal) set in
          let arg = pre arg signal in
          let arg,set = search' set pre post arg (deps signal) in
          let arg = post arg signal in
          arg, set
  and search' set pre post arg signals =
      List.fold_left (fun (arg,set) s -> search1' set pre post arg s) (arg,set) signals

  let search1 pre post arg signal = fst (search1' UidSet.empty pre post arg signal)
  let search pre post arg signal = fst (search' UidSet.empty pre post arg signal)

  let id x _ = x

  let find_elements outputs set =
    search' set
      (fun (regs, mems, consts, inputs, remaining) signal ->
        if signal = Signal_empty then
          (regs, mems, consts, inputs ,remaining)
        else if is_reg signal then
          (signal::regs, mems, consts, inputs ,remaining)
        else if is_const signal then
          (regs, mems, signal::consts, inputs ,remaining)
        else if is_input signal then
          (regs, mems, consts, signal::inputs ,remaining)
        else if is_mem signal then
          (regs, signal::mems, consts, inputs, remaining)
        else
          (regs, mems, consts, inputs ,signal::remaining)) 
      id ([],[],[],[],[]) outputs

  let find_regs_and_ready outputs = 
    search
      (fun (regs, inps, consts) signal -> 
        if is_reg signal then (signal::regs, inps, consts)
        else if is_const signal then (regs, inps, signal::consts)
        else if is_input signal then (regs, signal::inps, consts)
        else (regs, inps, consts))
      (fun x _ -> x) ([],[],[]) outputs

  let find_remaining outputs set = 
    search' set
      (fun remaining signal -> 
        if not (is_reg signal) && 
           not (is_const signal) && 
           not (is_input signal) then
          signal::remaining
        else 
          remaining)
      id [] outputs

  let schedule s x ready = 
    let set = List.fold_left (fun set s -> UidSet.add (uid s) set) UidSet.empty x in
    let remaining = fst @@ find_remaining s set in
    Cyclesim.scheduler deps remaining ready

  let copy_names step to_ from_ = 
    let pre step name = Printf.sprintf "__%.4i_%s_%Li" step name (uid from_) in
    if from_ = Signal_empty then to_
    else
      let name = String.concat "_" @@
        match names from_ with
        | [] -> ["uid"]
        | _ as l -> l
      in
      B.(--) to_ (pre step name)
      
  let create_signal map signal = 
    let s = List.map (fun s -> UidMap.find (uid s) map) (deps signal) in
    let a = function a::_ -> a | _ -> failwith "arg a" in
    let b = function [_;b] -> b | _ -> failwith "arg b" in
    match signal with
    | Signal_empty -> B.empty
    | Signal_const(_,c) -> B.const c
    | Signal_select(_,h,l) -> B.select (a s) h l
    | Signal_reg _ -> failwith "unexpected register"
    | Signal_mem _ -> failwith "memories not supported"
    | Signal_inst(s,_,_)  -> failwith "unexpected instantiation"
    | Signal_op(_,op) -> begin
        match op with
        | Signal_add  -> B.(+:) (a s) (b s)
        | Signal_sub  -> B.(-:) (a s) (b s)
        | Signal_mulu -> B.( *: ) (a s) (b s)
        | Signal_muls -> B.( *+ ) (a s) (b s)
        | Signal_and  -> B.(&:) (a s) (b s)
        | Signal_or   -> B.(|:) (a s) (b s)
        | Signal_xor  -> B.(^:) (a s) (b s)
        | Signal_eq   -> B.(==:) (a s) (b s)
        | Signal_not  -> B.(~:) (a s) 
        | Signal_lt   -> B.(<:) (a s) (b s)
        | Signal_cat  -> B.concat s
        | Signal_mux  -> B.mux (a s) (List.tl s)
    end
    | Signal_wire(_,t) -> 
      let w = B.wire (HardCaml.Signal.Comb.width signal) in
      begin if (!t <> Signal_empty) then B.(<==) w (a s) end;
      w

  let reduce_and l = match l with [] -> B.vdd | _ -> B.reduce B.(&:) l 

  let unroller ?(verbose=false) ?(init_state=I.init_state) ~k props = 

    let open Printf in

    let regs, inputs, consts = find_regs_and_ready props in
    let ready = regs @ inputs @ consts in

    let () = if verbose then printf "find_regs_and_ready\n" in

    let create_signal_map step map signal = 
      let s = create_signal map signal in
      let s = copy_names step s signal in
      UidMap.add (uid signal) s map
    in

    let create_input step signal = 
      let w = B.wire (width signal) in
      copy_names step w signal
    in

    (* maps generated (once) for inputs/registers at each step *)
    let step_map k signals = 
      let x = Array.init (k+1) (fun i -> None) in
      (fun k ->
         match x.(k) with
         | None -> 
           let y = List.map (fun x -> uid x, create_input k x) signals in
           x.(k) <- Some(y);
           y
         | Some(x) -> x)
    in

    let inputs' = step_map k inputs in
    let regs' = step_map k regs in
    let consts' = List.map (fun x -> uid x, create_signal UidMap.empty x) consts in
    let add_signals signals map = 
      List.fold_left 
        (fun map (uid,signal) -> UidMap.add uid signal map) 
        map signals 
    in

    let () = if verbose then printf "create maps\n" in

    let sched_regs = schedule regs [] ready in
    let () = if verbose then printf "sched_regs\n" in
    let show_string s = if verbose then printf "..%s\n" (to_string s) in
    List.iter show_string sched_regs;
    let sched_props = schedule props regs ready in
    let () = if verbose then printf "sched_props\n" in
    List.iter show_string sched_props;

    let () = if verbose then printf "schedule\n" in

    (* initialisation *)
    let trans_0 =
      reduce_and @@
        List.map2 (fun (_,reg_in) reg -> B.(reg_in ==: init_state reg)) (regs' 0) regs
    in

    let () = if verbose then printf "trans_0\n" in

    let trans_i step = 
      let () = if verbose then printf "trans_i %i\n" step in
      let map = add_signals (inputs' (step-1)) @@ 
                add_signals (regs' (step-1)) @@
                add_signals consts' @@
                UidMap.empty
      in
      let map = List.fold_left (create_signal_map (step-1)) map sched_regs in
      (* XXX think we probably need to look up the data input here. XXX *)
      let get_reg_data s = List.hd (deps s) in
      let regs = List.map (fun r -> UidMap.find (uid (get_reg_data r)) map) regs in
      reduce_and @@
        List.map2 (fun (_,reg_in) reg -> B.(reg_in ==: reg)) (regs' step) regs
    in

    let props_i step = 
      (if verbose then printf "props_i %i\n" step);
      let map = add_signals (inputs' step) @@ 
                add_signals (regs' step) @@
                add_signals consts' @@
                UidMap.empty
      in
      let map = List.fold_left (create_signal_map step) map sched_props in
      (* XXX think we probably need to look up the data input here. XXX *)
      List.map (fun p -> uid p, UidMap.find (uid p) map) props
    in

    let rec f step = 
      if step > k then []
      else begin
        let () = if verbose then printf "step=%i\n" step in
        (trans_i step, props_i step) :: f (step+1)
      end
    in

    let x = let x = (trans_0, props_i 0) in x :: f 1 in
    let trans = List.map fst x in
    let props = List.map snd x in

    let loop = 
      let s = List.rev @@ Array.to_list @@ Array.init (k+1) regs' in
      let k = List.hd s in
      let s = List.rev @@ List.tl s in
      List.map
        (fun s ->
          reduce_and @@
            List.map2
              (fun (u0,s0) (u1,s1) ->
                assert (u0=u1);
                B.(s0 ==: s1)) 
              k s) 
        s
    in

    let () = if verbose then printf "loop\n" in

    trans, loop, Array.of_list props

end

module Unroller_signal = Unroller(HardCaml.Signal.Comb)

type loop = [`none|`all|`offset of int]

module LTL = struct

  (* LTL properties.
   
    We'll take a LTL formula built from properties (single bits) compiled
    as part of the circuit.

    We'll be given an array of property sets for each time step.  If k=0 then we get
    1 set of properties, k=1 gives 2 sets and so on.

    Next we should build the combinatorial logic representing the LTL formula

  *)

  (* an association list from the uid of the (original) property to the computed
     propery 'value' at this step *)
  type prop_set = (HardCaml.Signal.Types.uid * HardCaml.Signal.Comb.t) list
  
  type prop_steps = prop_set array (* length=k+1 *)

  module M = Map.Make(struct
      type t = int * Props.LTL.path
      let compare = compare
  end)

  let loop map f l h = 
    let rec loop map lst l = 
      if l > h then map, List.rev lst 
      else 
        let map, x = f map l in
        loop map (x::lst) (l+1) 
    in
    loop map [] l 

  let scan f p = 
    let rec scan f l p = 
      match p with 
      | [] -> l 
      | h :: t -> scan f (h :: List.map (fun p -> f p h) l) t 
    in
    List.rev @@ scan f [] p 

  let compile_no_loop ~map ~props ~ltl = 
    let open HardCaml.Signal in
    let open Comb in

    let ltl = Props.LTL.nnf ltl in
    let k = Array.length props - 1 in

    let rec g map i ltl = 
      if i>k then map, gnd
      else if M.mem (i,ltl) map then map, M.find (i,ltl) map
      else
        let n x = output (Printf.sprintf "__%.4i_-" i ^ Props.LTL.to_string ltl) x in
        let add map x = M.add (i,ltl) x map, n x in
        let add2 f a b = 
          let map, a = g map i a in
          let map, b = g map i b in
          add map (f a b)
        in
        (* recursively generate propositions over time steps *)
        match ltl with
        | Props.LTL.True -> map, vdd
        | Props.LTL.Not Props.LTL.True -> map, gnd
        | Props.LTL.P p -> add map @@ List.assoc (Types.uid p) props.(i)
        | Props.LTL.Pn p -> add map @@ ~: (List.assoc (Types.uid p) props.(i))
        | Props.LTL.And(a,b) -> add2 (&:) a b
        | Props.LTL.Or(a,b) -> add2 (|:) a b
        | Props.LTL.X p -> 
          let map, p = g map (i+1) p in
          add map p

        (* XXX TODO *)
        | Props.LTL.U(a,b) -> failwith "U"
        | Props.LTL.R(a,b) -> failwith "R"

        | Props.LTL.F p -> 
          let map, x = loop map (fun map i -> g map i p) i k in
          add map @@ reduce (|:) x
        | Props.LTL.G p -> map, gnd 
        | Props.LTL.Not _ -> failwith "not in negated normal form"
    in
    g map 0 ltl

  let compile_loop ~map ~props ~ltl ~l = 
    let open HardCaml.Signal in
    let open Comb in
    let very_very_verbose = false in

    let ltl = Props.LTL.nnf ltl in
    let k = Array.length props - 1 in

    let succ i = if i < k then i+1 else l in 

    let rec g map i ltl = 
      let indent i = String.concat "" @@ Array.to_list @@ Array.init i (fun _ -> " ") in
      let get_min_idx i =  
        match ltl with
        | Props.LTL.G _ | Props.LTL.F _ -> min i l 
        | _ -> i
      in
      if M.mem (get_min_idx i,ltl) map then 
        let x = M.find (get_min_idx i,ltl) map in
        let () = 
          if very_very_verbose then
            Printf.printf "%s[%i] MEM %s --> %Li (%s)\n" 
              (indent i) i (Props.LTL.to_string ltl) (Types.uid x) 
              (to_string (List.hd (Types.deps x))) 
        in
        map, x
      else
        let n i x = output (Printf.sprintf "__%.4i_@" i ^ Props.LTL.to_string ltl) x in
        let addi map i x' = 
          let x = n i x' in
          let () = 
            if very_very_verbose then
              Printf.printf "%s[%i] ADD %s --> %Li (%s)\n" 
                (indent i) i (Props.LTL.to_string ltl) (Types.uid x) (to_string x') 
          in
          M.add (i,ltl) x map, x 
        in
        let add map x = addi map i x in
        let add2 f a b = 
          let map, a = g map i a in
          let map, b = g map i b in
          add map (f a b)
        in
        let create_temporal_loops f p = 
          let map, ps = loop map (fun map i -> g map i p) 0 k in
          let ps = scan f ps in
          fst @@ List.fold_left 
            (fun (map,i) p -> (fst @@ addi map i p), i+1) (map,0) ps 
        in
        (* recursively generate propositions over time steps *)
        match ltl with
        | Props.LTL.True -> 
          map, vdd
        | Props.LTL.Not Props.LTL.True -> 
          map, gnd
        | Props.LTL.P p -> 
          add map @@ List.assoc (Types.uid p) props.(i)
        | Props.LTL.Pn p -> 
          add map @@ ~: (List.assoc (Types.uid p) props.(i))
        | Props.LTL.And(a,b) -> 
          add2 (&:) a b
        | Props.LTL.Or(a,b) -> 
          add2 (|:) a b
        | Props.LTL.X p -> 
          let map, p = g map (succ i) p in
          add map p

        (* XXX TODO *)
        | Props.LTL.U(a,b) -> failwith "U"
        | Props.LTL.R(a,b) -> failwith "R"

        | Props.LTL.F p -> 
          g (create_temporal_loops (|:) p) i ltl
     
        | Props.LTL.G p -> 
          g (create_temporal_loops (&:) p) i ltl

        | Props.LTL.Not _ -> failwith "not in negated normal form"
    in

    g map 0 ltl

  let rec get_loop ?(loop=`all) ~loop_k ~k () = 
    let open HardCaml.Signal.Comb in
    let rec f k l = 
      if k=0 then gnd 
      else
        match l with
        | [] -> failwith "get_loop: ltl property loop too long"
        | h::t -> h |: f (k-1) t 
    in
    match loop with 
    | `none -> vdd
    | `all -> f k loop_k
    | `offset(x) when x < 0      -> List.nth loop_k (k+x)
    | `offset(x) (*when x >= 0*) -> List.nth loop_k (x)

  let compile ~props ~ltl ~loop_k ~k = 
    let open HardCaml.Signal.Comb in
    let loop_k_all = get_loop ~loop:`all ~loop_k ~k () in
    let loop_k = 
      let loop_k = output "loop_k" (concat @@ List.rev loop_k) in
      Array.init (width loop_k) (bit loop_k)
    in
    (* note; tried passing the map between the compilation steps but this
       doesn't work (the loop conditions are wrong - or at least the formula
       above them are).

       Still, theres a lot we should be able to share in this logic. *)
    let map, props_loop = 
      let map, props = loop M.empty
          (fun map l ->
            let map, x = compile_loop ~map:M.empty ~props ~ltl ~l in
            map, loop_k.(l) &: x) 0 k
      in
      map, reduce (|:) props
    in
    let props_no_loop = 
      let _, x = compile_no_loop ~map:M.empty ~props ~ltl in
      (~: loop_k_all) &: x
    in
    props_no_loop |: props_loop

end

let format_results = function
  | `unsat -> `unsat
  | `sat(k,s) -> 
    let is_prefixed s = 
      let is_num n = n >= '0' && n <= '9' in
      try
        s.[0] = '_' &&
        s.[1] = '_' &&
        is_num s.[2] && 
        is_num s.[3] && 
        is_num s.[4] && 
        is_num s.[5] && 
        s.[6] = '_' 
      with _ -> false
    in
    let get_cycle s = int_of_string (String.sub s 2 4) in
    let get_name s = String.sub s 7 (String.length s - 7) in
    let prefixed, other = List.partition (fun (x,_) -> is_prefixed x) s in
    let prefixed = List.map (fun (s,v) -> get_name s, get_cycle s, v) prefixed in
    let prefixed = List.sort compare prefixed in
    let prefixed = Sat.partition (fun (n,_,_) (m,_,_) -> m=n) prefixed in
    let prefixed = List.map 
        (function
          | [] -> "?", [||]
          | ((n,_,_)::_) as p ->
            let max_c = List.fold_left (fun m (_,c,_) -> max m c) 0 p in
            let p = List.map (fun (_,c,v) -> c,v) p in
            n, Array.init (max_c+1) (fun i -> try List.assoc i p with _ -> "?"))
        prefixed
    in
    `sat(k, prefixed @ List.map (fun (s,v) -> s, [|v|]) other)

let transform_regs ~reset ~clear ~enable ltl = 
  let open HardCaml.Signal.Types in
  let props1 = Props.LTL.atomic_propositions ltl in
  let props2 = Transform_state.(transform (to_muxes ~reset ~clear ~enable)) props1 in
  let props = List.map2 (fun p1 p2 -> uid p1, p2) props1 props2 in
  Props.LTL.map_atomic_propositions (fun x -> List.assoc (uid x) props) ltl

let compile ?(verbose=false) ?init_state ~k ltl = 
  let open HardCaml.Signal.Comb in
  let atomic_props = Props.LTL.atomic_propositions ltl in

  let clauses, loop_k, props = Unroller_signal.unroller ?init_state ~k:(k+1) atomic_props in
  let props = Array.init (Array.length props - 1) (Array.get props) in (* drop final property *)
  let () = 
    if verbose then begin
      Printf.printf "k = %i\n" k;
      Printf.printf "  ltl     = %s\n" Props.LTL.(to_string ltl);
      Printf.printf "  nnf     = %s\n" Props.LTL.(to_string @@ nnf ltl);
      Printf.printf "  clauses = %i\n" (List.length clauses);
      Printf.printf "  props   = %i\n" (Array.length props);
      Printf.printf "  loop_k  = %i\n%!" (List.length loop_k)
    end
  in
  let props = LTL.compile ~props ~ltl ~loop_k ~k in
  Unroller_signal.reduce_and clauses &: props

type bmc_result = (int * ((string * string array) list)) Sattools.Result.t

let run1 ?(verbose=false) ?init_state ~k ltl = 
  let cnf = Sat.convert @@ compile ~verbose ?init_state ~k ltl in
  let () = if verbose then Printf.printf "  vars    = %i\n%!" (Sat.nvars cnf) in
  let () = if verbose then Printf.printf "  terms   = %i\n%!" (Sat.nterms cnf) in
  let map = Sat.name_map Sat.M.empty cnf in
  match Sat.report map @@ Sat.run cnf with
  | `unsat -> `unsat
  | `sat l -> format_results @@ `sat(k, l)

let print ?init_state ~k ltl = 
  HardCaml.Rtl.Verilog.write print_string @@ HardCaml.Circuit.make "bmc" 
    [ HardCaml.Signal.Comb.output "proposition" @@ compile ~k ?init_state ltl ]

let run ?verbose ?init_state ~k ltl = 
  (* run tests from 0..k *)
  let rec f i =
    if i>k then `unsat
    else 
      match run1 ?verbose ~k:i ?init_state ltl with
      | `unsat -> f (i+1)
      | `sat l -> `sat l
  in
  f 0
 
open HardCaml

type bmc = 
  {
    run : ?verbose:bool -> int -> bmc_result;
    run1 : ?verbose:bool -> int -> bmc_result;
  }

module Gen(I : Interface.S)(O : Interface.S) = struct

  let make name logic ltl = 
    let inputs = I.(map (fun (n,b) -> Signal.Comb.input n b) t) in 
    let outputs = logic inputs in

    (* get ltl property *)
    let ltl = ltl I.(map Props.LTL.p inputs) O.(map Props.LTL.p outputs) in

    let run ?(verbose=false) k = run ~verbose ~k ltl in
    let run1 ?(verbose=false) k = run1 ~verbose ~k ltl in
    { run; run1 }

end

module Gen_with_sim(B : Comb.S)(I : Interface.S)(O : Interface.S) = struct

  module S = Cyclesim.Make(B)
  module Cs = Cyclesim.Api
  module Init = Init_state(Signal.Comb)(B)

  type sim = 
    {
      sim : S.cyclesim;
      inputs : B.t ref I.t;
      outputs : B.t ref O.t;
      next : B.t ref O.t;
    }

  let make name logic ltl = 
    let inputs = I.(map (fun (n,b) -> Signal.Comb.input n b) t) in 
    let outputs = logic inputs in
    let circuit = Circuit.make name 
      (O.to_list (O.map2 (fun (n,_) s -> Signal.Comb.output n s) O.t outputs))
    in

    (* simulator *)
    let sim = S.make 
      ~internal:(Some(fun s -> Signal.Types.names s <> []))
      circuit 
    in
    let sim_inputs = I.(map (fun (n,b) -> try Cs.in_port sim n with _ -> ref B.(zero b)) t) in
    let sim_outputs = O.(map (fun (n,b) -> try Cs.out_port sim n with _ -> ref B.(zero b)) t) in
    let sim_next = O.(map (fun (n,b) -> try Cs.out_port_next sim n with _ -> ref B.(zero b)) t) in

    (* get ltl property *)
    let ltl = ltl I.(map Props.LTL.p inputs) O.(map Props.LTL.p outputs) in

    let run ?(verbose=false) k = 
      let init_state = Init.init_from_sim sim in
      run ~init_state ~k ltl 
    in
    let run1 ?(verbose=false) k = 
      let init_state = Init.init_from_sim sim in
      run1 ~init_state ~k ltl 
    in
    { run; run1 },
    {
      sim;
      inputs = sim_inputs;
      outputs = sim_outputs;
      next = sim_next;
    }

end



