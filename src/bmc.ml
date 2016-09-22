(* Bounded Model Checking for HardCaml circuits with LTL property checking.
  
   The main API function is 'run ~k ltl' which will iteratively run
   bounded model checking for 0, then 1, up to 'k' time steps against the 
   property specification given by 'ltl'.

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

module Copy = HardCaml.Transform.CopyTransform

(* convert a register with reset/clear/enable, to a simple flipflop by
 * pushing the logic into muxes on the front end *)
let simple_reg find r d q = 
  let open HardCaml.Signal.Types in
  let open HardCaml.Signal.Comb in
  let open HardCaml.Signal.Seq in
  let open HardCaml.Utils in
  let reg_clock = (find << uid) r.reg_clock in
  let reg_reset = (find << uid) r.reg_reset in
  let reg_reset_value = (find << uid) r.reg_reset_value in
  let reg_clear = (find << uid) r.reg_clear in
  let reg_clear_value = (find << uid) r.reg_clear_value in
  let reg_enable = (find << uid) r.reg_enable in

  (* add default of zero for clear/reset *)
  let zero = zero (width d) in
  let def v = if v=empty then zero else v in
  let reg_reset_value = def reg_reset_value in
  let reg_clear_value = def reg_clear_value in

  (* enable *)
  let is_const_1 x = try const_value x = "1" with _ -> false in
  let d = 
    if reg_enable = empty then d
    else if is_const_1 reg_enable then d 
    else mux2 reg_enable d q 
  in
  (* clear *)
  let d = if reg_clear <> empty then mux2 reg_clear reg_clear_value d else d in
  (* reset *)
  let d  = if reg_reset <> empty then mux2 reg_reset reg_reset_value d else d in

  (* build register *)
  { r with 
    reg_clock; 
    reg_reset=empty; reg_reset_value;
    reg_clear=empty; reg_clear_value;
    reg_enable=empty; 
  }, d

(* Convert registers to simple registers *)
module SimplifyRegs = 
struct 

  open HardCaml.Signal.Types
  open HardCaml.Signal.Comb
  open HardCaml.Signal.Seq

  let transform find signal = 
    let dep n = find (uid (List.nth (deps signal) n)) in
    match signal with
    | Signal_reg(id,r) -> 
        let q = wire (width signal) in
        let spec, d = simple_reg find r (dep 0) q in
        q <== reg spec empty d;
        List.fold_left (--) q (names signal)
    | _ -> Copy.transform find signal

end

module Unroller(B : HardCaml.Comb.S) = struct

  (* Simplify and fix some problems.
   
     We need to generate the transition function, and properties.  

     The transition function is generated for the registers
     within the circuit.  The properties are outputs of the circuit.

     I_{i} = Inputs at step i

     S_{i} = Value of registers (state) at step i.

     S_{0} = initial state - derived from reset/clear or user specified.

     T_{i} = transition function from step i-1 to i.  It is a function
             of I_{i} and S_{i-1}

     P_{i} = properties at step i.  A function of I_{i} and S_{i}.

  *)

  open HardCaml 
  open Signal.Types 

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

  let init_value = function
    | Signal_reg(_, r) as s ->
      (* pick reset or clear value as init value XXX revisit this! *)
      if r.reg_reset_value <> Signal_empty then B.const (const_value r.reg_reset_value)
      else if r.reg_clear_value <> Signal_empty then B.const (const_value r.reg_clear_value)
      else B.zero (width s)
    | _ -> failwith "expecting register"

  let reduce_and l = match l with [] -> B.vdd | _ -> B.reduce B.(&:) l 

  let unroller ?(verbose=false) ~k props = 

    let open Printf in

    (* simplify register enable/clear etc *)
    (*let props = Transform.rewrite_signals SimplifyRegs.transform props in*)

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
        List.map2 (fun (_,reg_in) reg -> B.(reg_in ==: init_value reg)) (regs' 0) regs
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

  let compile_no_loop ~props ~ltl = 
    let open HardCaml.Signal in
    let open Comb in

    let ltl = Props.LTL.nnf ltl in
    let k = Array.length props - 1 in

    let rec g i ltl = 
      if i>k then gnd
      else
        (* recursively generate propositions over time steps *)
        match ltl with
        | Props.LTL.True -> vdd
        | Props.LTL.Not Props.LTL.True -> gnd
        | Props.LTL.P p -> List.assoc (Types.uid p) props.(i)
        | Props.LTL.Pn p -> ~: (List.assoc (Types.uid p) props.(i))
        | Props.LTL.And(a,b) -> ((f i a) &: (f i b)) 
        | Props.LTL.Or(a,b) -> ((f i a) |: (f i b)) 
        | Props.LTL.X p -> f (i+1) p 

        (* XXX TODO *)
        | Props.LTL.U(a,b) -> failwith "U"
        | Props.LTL.R(a,b) -> failwith "R"

        | Props.LTL.F p -> 
          let rec x j = 
            if j>k then gnd
            else f j p |: x (j+1)
          in
          x i 
        | Props.LTL.G p -> gnd 
        | Props.LTL.Not _ -> failwith "not in negated normal form"

    and f i ltl = output ("noloop:"^Props.LTL.to_string ltl) (g i ltl) in

    f 0 ltl

  let compile_loop ~props ~ltl ~l = 
    let open HardCaml.Signal in
    let open Comb in

    let ltl = Props.LTL.nnf ltl in
    let k = Array.length props - 1 in

    let rec loop f l h = if l > h then [] else f l :: loop f (l+1) h in
    let succ i = if i < k then i+1 else l in (* ??? *)

    let rec g i ltl = 
      if i>k then gnd
      else
        (* recursively generate propositions over time steps *)
        match ltl with
        | Props.LTL.True -> vdd
        | Props.LTL.Not Props.LTL.True -> gnd
        | Props.LTL.P p -> List.assoc (Types.uid p) props.(i)
        | Props.LTL.Pn p -> ~: (List.assoc (Types.uid p) props.(i))
        | Props.LTL.And(a,b) -> ((f i a) &: (f i b)) 
        | Props.LTL.Or(a,b) -> ((f i a) |: (f i b)) 
        | Props.LTL.X p -> f (succ i) p 

        (* XXX TODO *)
        | Props.LTL.U(a,b) -> failwith "U"
        | Props.LTL.R(a,b) -> failwith "R"

        (* what if the loops are empty? *)
        | Props.LTL.F p -> reduce (|:) (loop (fun i -> f i p) (min l i) k)
        | Props.LTL.G p -> reduce (&:) (loop (fun i -> f i p) (min l i) k)
        | Props.LTL.Not _ -> failwith "not in negated normal form"
    and f i ltl = output ("loop:"^Props.LTL.to_string ltl) (g i ltl) in

    f 0 ltl

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
    let prefixed = Dimacs.partition (fun (n,_,_) (m,_,_) -> m=n) prefixed in
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

let compile ?(verbose=false) ?(loop=`all) ~k ltl = 
  let open HardCaml.Signal.Comb in
  let atomic_props = Props.LTL.atomic_propositions ltl in
  let clauses, loop_k, props = Unroller_signal.unroller ~k:(k+1) atomic_props in
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
  let loop_k_all = get_loop ~loop ~loop_k ~k () in
  let loop_k = 
    let loop_k = output "loop_k" (concat @@ List.rev loop_k) in
    Array.init (width loop_k) (bit loop_k)
  in
  let props_no_loop = loop_k_all &: LTL.compile_no_loop ~props ~ltl in
  let props_loop = 
    reduce (|:) @@
    Array.to_list @@
    Array.init (k+1) (fun l -> loop_k.(l) &: LTL.compile_loop ~props ~ltl ~l) 
  in
  Unroller_signal.reduce_and clauses &: (props_no_loop |: props_loop)

let run1 ?(verbose=false) ?(loop=`all) ~k ltl = 
  let cnf = Dimacs.convert @@ compile ~verbose ~loop ~k ltl in
  let () = if verbose then Printf.printf "  vars    = %i\n%!" (Sat.nvars cnf) in
  let () = if verbose then Printf.printf "  terms   = %i\n%!" (Sat.nterms cnf) in
  let map = Sat.name_map Sat.M.empty cnf in
  Dimacs.report map @@ Dimacs.run cnf

let run ?verbose ~k ltl = 
  (* run tests from 0..k *)
  let rec f i =
    if i>k then `unsat
    else 
      match run1 ?verbose ~loop:`all ~k:i ltl with
      | `unsat -> f (i+1)
      | `sat l -> format_results @@ `sat(i, l)
  in
  f 0
   

