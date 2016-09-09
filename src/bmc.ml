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
  let d = if reg_enable <> empty then mux2 reg_enable d q else d in
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
      mutable clause : t;
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
      let q' = input (name signal) (width signal) in
      st.cur <- (uid signal, q') :: st.cur;

      (* initialise *)
      if st.step = 0 then begin
        let v = const_value r.reg_reset_value in
        st.clause <- (q' ==: r.reg_reset_value) &: st.clause;
        List.fold_left (--) (const v) (names signal)
      (* step *)
      end else begin
        let q = 
          try List.assoc (uid signal) st.prev
          with Not_found -> failwith "couldn't find register from previous step"
        in
        (* generate implication clause *)
        st.clause <- ((dep 0) ==: q') &: st.clause;
        List.fold_left (--) q (names signal)
      end
    end
    | _ -> Copy.transform find signal

end

module LTL = struct

  (* LTL properties.
   
    We'll take a LTL formula built from properties (single bits) compiled
    as part of the circuit.

    We'll be given an array of property sets for each time step.  If k=0 then we get
    1 set of properties, k=2 give 2 sets and so on.

    Next we should build the combinatorial logic representing the LTL formula

  *)

  (* an association list from the uid of the (original) property to the computed
     propery 'value' at this step *)
  type prop_set = (HardCaml.Signal.Types.uid * HardCaml.Signal.Comb.t) list
  
  type prop_steps = prop_set array (* length=k+1 *)

  let compile ~props ~loop_k ~ltl = 
    let open HardCaml.Signal in
    let open Comb in

    let k = Array.length props - 1 in
    let rec f i ltl = 
      if i>k then vdd (* XXX ??? *)
      else
        (* recursively generate propositions over time steps 
         * XXX add F and G? *)
        match ltl with
        | Props.LTL.True -> vdd (* XXX ??? *)
        | Props.LTL.Not Props.LTL.True -> gnd
        | Props.LTL.P p -> List.assoc (Types.uid p) props.(i)
        | Props.LTL.Pn p -> ~: (List.assoc (Types.uid p) props.(i))
        | Props.LTL.And(a,b) -> (f i a) &: (f i b)
        | Props.LTL.Or(a,b) -> (f i a) |: (f i b)
        | Props.LTL.X p -> f (i+1) p
        | Props.LTL.U(a,b) -> (* a holds until b; b, ab, aab, aaab etc. *)
          let rec u j a' = (* from i..j *)
            if j>k then gnd
            else (a' &: (f j b)) |: (u (j+1) (a' &: (f j a)))
          in
          u i vdd
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
          r |: (b' &: loop_k)
        | Props.LTL.Not _ -> failwith "not in negated normal form"
    in
    f 0 (Props.LTL.nnf ltl)

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
      let st = Unroll.({ step; prev; cur=[]; clause }) in
      let outputs' = 
        CustomTransform.rewrite_signals ("_bmcstep_" ^ string_of_int step)
          Unroll.(transform st) outputs' 
      in
      let outputs' = List.map2 (fun o o' -> Signal.Types.uid o, o') circ outputs' in
      f (step+1) st.Unroll.cur st.Unroll.clause (outputs' :: outputs) (st.Unroll.cur :: states)
    end
  in
  let c,o,s = f 0 [] vdd [] [] in
  let loop_k = 
    let k = List.hd s in
    let s = List.tl s in
    List.fold_left 
      (fun acc s ->
        acc |: 
          List.fold_left2 
            (fun acc (u0,s0) (u1,s1) ->
              assert (u0=u1);
              acc &: (s0 ==: s1)) 
            vdd k s) 
      vdd s
  in
  c, loop_k, Array.of_list @@ List.rev @@ o

let compile_ltl ~k ~ltl = 
  let atomic_props = Props.LTL.atomic_propositions ltl in
  let clauses, loop_k, props = unroll ~k atomic_props in
  let props = LTL.compile ~props ~loop_k ~ltl in
  HardCaml.Signal.Comb.(clauses &: props)


