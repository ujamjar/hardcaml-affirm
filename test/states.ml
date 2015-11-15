(* Create a simple state machine that cycles though states 0..3
 * on application of a start signal.
 *
 * Check that all states are reachable. *)

#require "hardcaml";;
#directory "_build/src";;
#load "HardCamlAffirm.cma";;

open HardCamlAffirm

open HardCaml.Signal.Comb
open HardCaml.Signal.Seq

let sm start = 
  let open HardCaml.Signal.Guarded in

  let state = g_reg r_sync enable 2 in

  let () = 
    compile [
      g_switch (state#q) [
        consti 2 0, [
          g_when start [
            state $==. 1;
          ]
        ];
        consti 2 1, [
          state $==. 2;
        ];
        consti 2 2, [
          state $==. 3; (* for example; set this to 0 and the check fails *)
        ];              (* as state=3 is unreachable *)
        consti 2 3, [
          state $==. 0;
        ];
      ]
    ]
  in

  state#q -- "state"

(* there exist paths to every state *)
let prop state = 
  let st n = Props.CTL.(ef (p (state ==:. n))) in
  `CTL Props.CTL.(ef (st 0 &: st 1 &: st 2 &: st 3))

let state = sm (input "start" 1)
let circ = NuSMV.make "test" [] [ prop state ]
let () = NuSMV.write print_string circ

