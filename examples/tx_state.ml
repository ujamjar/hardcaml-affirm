(* In this example we define the circuit using hardcaml interfaces
   and use the Transform_state module to include the register enable.

   We then test that for a simple register its output value on the
   next clock cycle is equal to its input.  This is obviously true
   so long as the enable is also high.

   The first formula (ltl) will fail while the 2nd (ltl_en) will pass.
*)

open HardCaml
open Signal.Comb
open Signal.Seq
open HardCamlAffirm

module I = struct
  type 'a t = { 
    en : 'a[@bits 1]; 
    d : 'a[@bits 1]; 
  }[@@deriving hardcaml]
end
module P = struct
  type 'a t = { 
    i : 'a I.t; 
    q : 'a[@bits 1]; 
  }[@@deriving hardcaml]
end
module T = Transform_state.Make(I)(P)

let f i = { P.q = reg r_full i.I.en i.I.d; 
            i = i }
let o = 
  P.(map2 (fun (n,_) o -> output n o) t) @@
  T.transform 
    (Transform_state.to_muxes ~enable:true ~clear:false ~reset:false) 
    f I.(map (fun (n,b) -> input n b) t)

open Props.LTL
open P
open I

let p = P.map (fun x -> p x) o
let ltl = g (p.i.d ==: (X p.q))
let ltl_en = g (p.i.en ==>: (p.i.d ==: (X p.q)))

let () = Waves.run @@ Bmc.run ~verbose:true ~k:10 (~: ltl)
let () = Waves.run @@ Bmc.run ~verbose:true ~k:10 (~: ltl_en)

