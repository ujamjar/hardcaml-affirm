open HardCaml
open Signal.Types
open Signal.Comb
open Signal.Seq

module Copy = Transform.CopyTransform

type transform = (uid -> t) -> register -> t -> t -> register * t

(* Convert registers to simple registers *)

let transform_regs simple_reg find signal = 
  let dep n = find (uid (List.nth (deps signal) n)) in
  match signal with
  | Signal_reg(id,r) -> 
      let q = wire (width signal) in
      let spec, d = simple_reg find r (dep 0) q in
      q <== reg spec empty d;
      List.fold_left (--) q (names signal)
  | _ -> Copy.transform find signal

(* convert a register with reset/clear/enable, to a simple flipflop by
 * pushing the logic into muxes on the front end *)
let to_muxes ~reset ~clear ~enable find r d q = 
  let open HardCaml.Utils in
  let reg_clock = (find << uid) r.reg_clock in
  let reg_reset = if reset then (find << uid) r.reg_reset else empty in
  let reg_reset_value = (find << uid) r.reg_reset_value in
  let reg_clear = if clear then (find << uid) r.reg_clear else empty in
  let reg_clear_value = (find << uid) r.reg_clear_value in
  let reg_enable = if enable then (find << uid) r.reg_enable else empty in

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

let transform transform outputs = 
  HardCaml.Transform.rewrite_signals (transform_regs transform) outputs 



