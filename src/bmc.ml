(* Bounded Model Checking.
 
  Invariant checking with BMC
  ---------------------------
  
  AG P (property P is always true).

  I0 & &[ S(i,i+1) ] & |[ ~Pi ]
       i=0..k-1        i=0..k

  where
    I0 = initial state
    S(i,i+1) = transistion relation from state i to i+1
    Pi = property in cycle i

  note; &[..] |[..] represent conjunction/disjunction over the given bounds

  In context of hardware

    I0 = initial value of the registers
    S(i,i+1) = function of inputs + registers to next value of registers 
    Pi = a property built from the combinatorial logic at the current time step

  A couple of properties
    - This formula can be satisfied if and only if there exists a reachable state in 
      cycle i (i<=k) which contradicts the property Pi.
    - You can focus on a specific cycle by restricting the disjunction over Pi (|[ ~Pi ])
 
  Description above adapted from 
  http://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/BMC/description.html

  Loops
  -----

  There is an interesting modification to the above which allows us to look
  at. and prove. properties over infinite paths.  The idea is we end up with
  a sequence of states {S0 S1 ... Sl ... Sk} where Sl to Sk repeats.
  We can check this with some extra logic which compares states for equality ie
  if Sk <==> Sl we will repeat the loop infinitely.

  The more complex bit is actually choosing a temporal logic and deriving the
  appropriate properties in a bounded form and this also seems to affect the 
  loop check complexity.

  note; how similar is this to runtime verification/monitoring using temportal 
        logics?  It appears to be much the same problem at first glance.

  Implementation
  --------------

  Given a circuit we have basically only one thing to do;

  - Remove all registers and replace them with inputs and outputs
  - Trace the register I/O pairs so we can connect them up across states
  - a related detail - registers must be transformed to a simple form
    without clear/enable (reset is handled by I0 I think) etc
      if (reset) d <= r;
      else d <= q;
  
*)

let verbose = false 

(* this is copied from the HardCaml.Transform module and modified very slightly
 * to add a suffix to all wire names (specifically for the inputs and outputs)
 * so the stages can be differentiated in the combined (unrolled) circuit. *)
module CustomTransform = struct

  open HardCaml.Utils
  open HardCaml.Signal.Types
  open HardCaml.Signal.Comb

  let rewrite suffix fn id_to_sig outputs = 
    let idv k v = k in
    let set_of_map f map = UidMap.fold (fun k v s -> UidSet.add (f k v) s) map UidSet.empty in 
    let set_of_list f l = List.fold_left (fun s v -> UidSet.add (f v) s) UidSet.empty [] in

    let copy_names s t = 
      List.fold_left (fun t n -> t -- (n ^ suffix)) t (names s)
    in

    let partition compare set = 
      UidSet.fold (fun k (tr,fl) -> 
        if compare k then UidSet.add k tr, fl
        else tr, UidSet.add k fl) set (UidSet.empty,UidSet.empty)
    in

    let find uid = UidMap.find uid id_to_sig in
    
    (*let partition_const = partition (find >> is_const) in*)
    let partition_wire = partition (find >> is_wire) in

    let partition_ready ready remaining = 
      let ready s = 
        let s = find s in (* look up the signal *)
        let dep_set = set_of_list uid (deps s) in
        UidSet.subset dep_set ready
      in
      let new_ready, not_ready = partition ready remaining in
      if UidSet.cardinal new_ready = 0 then failwith "Could not schedule anything"
      else new_ready, not_ready
    in

    let all_set = set_of_map idv id_to_sig in
    let wire_set,remaining_set = partition_wire all_set in
    let ready_set = wire_set in

    (* copy wires (must be done this way to break combinatorial dependancies *)
    let map = 
      UidSet.fold (fun uid map ->
        let signal = find uid in
        match signal with
        | Signal_wire(_) -> UidMap.add uid (copy_names signal (wire (width signal))) map
        | _ -> failwith "unexpected signal"
      ) ready_set UidMap.empty
    in

    (* now recursively rewrite nodes as they become ready *)
    let rec rewrite map ready remaining = 
      if UidSet.cardinal remaining = 0 then map
      else
        let find_new map uid = UidMap.find uid map in
        let new_ready, new_remaining = partition_ready ready remaining in
        (* rewrite the ready nodes *)
        let map = 
          UidSet.fold (fun uid map ->
            let old_signal = find uid in
            let new_signal = fn (find_new map) old_signal in
            UidMap.add uid new_signal map
          ) new_ready map
        in
        rewrite map (UidSet.union ready new_ready) new_remaining
    in

    let map = rewrite map ready_set remaining_set in

    (* reattach all wires *)
    UidSet.iter (fun uid' ->
        let o = UidMap.find uid' id_to_sig in
        let n = UidMap.find uid' map in
        match o with 
        | Signal_wire(id,d) -> 
            if !d <> empty then
                let d = UidMap.find (uid !d) map in
                n <== d
        | _ -> failwith "expecting a wire") wire_set;

    (* find new outputs *)
    let outputs = 
      List.map (fun signal -> UidMap.find (uid signal) map) 
        outputs
    in
    outputs

  let rewrite_signals suffix fn signals = 
    let id_to_sig = HardCaml.Circuit.search
      (fun map signal -> UidMap.add (uid signal) signal map)
      HardCaml.Circuit.id UidMap.empty signals
    in
    rewrite suffix fn id_to_sig signals

end

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

module Unroll = struct
  open HardCaml.Signal.Types
  open HardCaml.Signal.Comb
  open HardCaml.Signal.Seq
  open HardCaml.Utils

  let (==>:) a b = (~: a) |: b

  let prefix = "__reg"

  type step = 
    {
      step : int; (* note; at step=0 we initialise *)
      prev : (uid * t) list; (* registers from previous stage *)
      mutable cur : (uid * t) list; (* registers for next stage *)
      mutable clause : t list;
    }

  let transform st find signal = 
    let dep n = find (uid (List.nth (deps signal) n)) in
    match signal with
    | Signal_reg(id,r) -> begin
      let name s = (* try to give a 'very' unique-ish name *)
        prefix ^ 
          (try List.hd (names s) ^ "_" ^ Int64.to_string (uid s) 
          with _ -> "_" ^ Int64.to_string (uid s)) ^ 
            "_bmcstep_" ^ string_of_int st.step 
      in

      (* next state *)
      let q_cur = input (name signal) (width signal) in
      st.cur <- (uid signal, q_cur) :: st.cur;

      (* initialise *)
      if st.step = 0 then begin
          st.clause <- (r.reg_reset_value ==: q_cur) :: st.clause;
          List.fold_left (--) q_cur (names signal) 
      (* step *)
      end else begin
        let q_prev = 
          try List.assoc (uid signal) st.prev
          with Not_found -> failwith "couldn't find register from previous step"
        in
        (* generate implication clause *)
        let d = dep 0 in
        st.clause <- (d ==: q_cur) :: st.clause;
        List.fold_left (--) q_prev (names signal)
      end
    end
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
    let a = function [a] -> a | [a;_] -> a | _ -> failwith "arg a" in
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

  let unroller ~k props = 

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

    let reduce_and l = match l with [] -> B.vdd | _ -> B.reduce B.(&:) l in

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
    let trans = reduce_and (List.map fst x) in
    let props = List.map snd x in

    let loop = 
      let s = List.rev @@ Array.to_list @@ Array.init (k+1) regs' in
      let k = List.hd s in
      let s = List.rev @@ List.tl s in
      List.mapi (fun i s -> B.output ("loop_" ^ string_of_int i) s) @@
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

  let compile ~props ~loop_k ~ltl = 
    let open HardCaml.Signal in
    let open Comb in

    let ltl = Props.LTL.nnf ltl in
    let depth = Props.LTL.depth ltl in
    let k = Array.length props - 1 - depth in

    let _true = const "1" -- "prop_t" in
    let _false = const "1" -- "prop_f" in

    let rec f i ltl = 
      if i>(k+depth) then failwith "compiling LTL formulate: i>(k+depth)"
      else
        (* recursively generate propositions over time steps *)
        match ltl with
        | Props.LTL.True -> _true
        | Props.LTL.Not Props.LTL.True -> _false
        | Props.LTL.P p -> List.assoc (Types.uid p) props.(i)
        | Props.LTL.Pn p -> ~: (List.assoc (Types.uid p) props.(i))
        | Props.LTL.And(a,b) -> ((f i a) &: (f i b)) -- "prop_and"
        | Props.LTL.Or(a,b) -> ((f i a) |: (f i b)) -- "prop_or"
        | Props.LTL.X p -> f (i+1) p -- "prop_x"
        | Props.LTL.U(a,b) -> (* a holds until b; b, ab, aab, aaab etc. *)
          let rec u j a' = (* from i..j *)
            if j>k then gnd
            else (a' &: (f j b)) |: (u (j+1) (a' &: (f j a)))
          in
          (u i vdd) -- "prop_u"
        | Props.LTL.R(a,b) -> (* b holds until a&b, or b always *)
          let rec r j b' = (* from i..j - returns the accumulated b variable *)
            if j>k then gnd, b'
            else 
              let a = f j a in
              let b = f j b &: b' in
              let r', b' = r (j+1) b in
              (a &: b) |: r', b'
          in
          let r, b' = r i vdd in
          (r |: (b' &: loop_k)) -- "prop_r"
        | Props.LTL.F p -> (* p is finally (eventually) true *)
          let rec x j = 
            if j>k then gnd
            else f j p |: x (j+1)
          in
          x i -- "prop_f"
        | Props.LTL.G p -> (* p is globally (always) true *)
          let rec x j = 
            if j>k then vdd
            else f j p &: x (j+1)
          in
          (x i &: loop_k) -- "prop_g"
        | Props.LTL.Not _ -> failwith "not in negated normal form"
    in
    f 0 ltl

end

(* unroll for k cycles *)
let unroll ~k circ = 
  let open HardCaml in
  let open Signal.Comb in

  (* 1. simplify regs *)
  let outputs' = Transform.rewrite_signals SimplifyRegs.transform circ in

  (* 2. unroll circuit 'k+1' times where k=0 is for initialisation *)
  let open HardCaml in
  let rec f step prev clause outputs states = 
    if step > k then 
      clause, outputs, states
    else begin
      let st = Unroll.({ step; prev; cur=[]; clause=[] }) in
      let outputs' = 
        CustomTransform.rewrite_signals ("_bmcstep_" ^ string_of_int step)
          Unroll.(transform st) outputs' 
      in
      let outputs' = List.map2 (fun o o' -> Signal.Types.uid o, o') circ outputs' in
      f (step+1) st.Unroll.cur (st.Unroll.clause :: clause) 
        (outputs' :: outputs) (st.Unroll.cur :: states)
    end
  in
  let c,o,s = f 0 [] [] [] [] in
  let c = 
    let reduce_and l = if l=[] then vdd else reduce (&:) l in
    reduce_and (List.map reduce_and c)
  in
  (* loop clause: Exists_{i=0..k-1} state.(i) = state.(k) *)
  let loop_k = 
    let k = List.hd s in
    let s = List.rev @@ List.tl s in
    List.map
      (fun s ->
        List.fold_left2 
          (fun acc (u0,s0) (u1,s1) ->
            assert (u0=u1);
            acc &: (s0 ==: s1)) 
          vdd k s) 
      s
  in
  let props = Array.of_list @@ List.rev @@ o in
  c, loop_k, props

type loop = [`none|`all|`offset of int]

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

let compile ?(loop=`all) ~k ltl = 
  let atomic_props = Props.LTL.atomic_propositions ltl in
  let depth = Props.LTL.depth ltl in
  let clauses, loop_k, props = Unroller_signal.unroller ~k:(k+depth) atomic_props in
  let () = 
    if verbose then begin
      Printf.printf "k = %i\n" k;
      Printf.printf "  %s\n" Props.LTL.(to_string ltl);
      Printf.printf "  %s\n" Props.LTL.(to_string @@ nnf ltl);
      Printf.printf "  ltl depth = %i\n" depth;
      Printf.printf "  props = %i\n" (Array.length props);
      Printf.printf "  loop_k = %i\n" (List.length loop_k)
    end
  in
  let loop_k = get_loop ~loop ~loop_k ~k () in
  let () = if verbose then Printf.printf "got loop\n%!" in
  let props = LTL.compile ~props ~loop_k ~ltl in
  let () = if verbose then Printf.printf "compiled property\n%!" in
  HardCaml.Signal.Comb.(clauses &: props)

let run1 ?(loop=`all) ~k ltl = 
  let cnf = Dimacs.convert @@ compile ~loop ~k ltl in
  let map = Sat.name_map Sat.M.empty cnf in
  Dimacs.report map @@ Dimacs.run cnf

let run ~k ltl = 
  (* run tests from 0..k *)
  let rec f i =
    if i>k then `unsat
    else 
      match run1 ~loop:`all ~k:i ltl with
      | `unsat -> f (i+1)
      | `sat l -> `sat(i, l)
  in
  f 0
   
(*******************************************************************)

