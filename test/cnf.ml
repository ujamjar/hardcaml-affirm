(* test cnf conversion *)
#require "hardcaml";;
#directory "_build/src";;
#load "HardCamlAffirm.cma";;

open Printf
open HardCamlAffirm
open HardCaml
open Signal.Comb

let test n = 
  (* DUT *)
  let a, b = input "a" 3, input "b" 3 in
  let c = output "c" ((ue a +: ue b) ==:. n) in
  let circ = Circuit.make "test" [c] in

  (* Convert to CNF *)
  let cnf = Dimacs.cnf_of_circuit circ in

  (* Run MiniSAT *)
  Dimacs.Minisat.(report stdout cnf @@ run "dimacs" "out" cnf)

let () = test 14 (* SAT: 7+7=14 *)
let () = test 15 (* UNSAT: 14 is max possible *)

