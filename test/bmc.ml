
#require "hardcaml";;
#directory "_build/src";;
#load "HardCamlAffirm.cma";;

open HardCamlAffirm

open HardCaml
open Signal.Comb
open Signal.Seq

module Satish = struct

  let r1 = input "r1" 1
  let r2 = input "r2" 1 
  let g1 = reg r_async empty r1
  let g2 = reg Signal.Types.({r_async with reg_clear_value=vdd}) empty ((~: r1) &: (~: g1) &: r2)

  let circ = Circuit.make "satish" [
    output "g1_o" (g1 -- "g1");
    output "g2_o" (g2 -- "g2");
  ]

end

module Addable = struct

  let a = input "a" 2
  let b = input "b" 2
  let c = (reg r_none empty (a +: b)) -- "addable"
  let prop = output "prop" (c <>:. 3)
  let circ = Circuit.make "addable" [prop]

end

(* property G r1 ==> X g1 & XX g1 
   negated  F r1 & (~ X g1 & ~ XX g1*)

let circ = Addable.circ
let k = try int_of_string Sys.argv.(1) with _ -> 1

(* unroll *)
let circ = Bmc.unroll k circ

(* add properties *)
let circ = 
  Circuit.make "my_proposition" @@
    [ output "bmc_sat_proposition" (reduce (&:) (Circuit.outputs circ)) ]

(* print circuit *)
let () = Rtl.Verilog.write print_string @@ circ

(* minisatify *)

let () = 
  let cnf = Dimacs.cnf_of_circuit circ in
  Dimacs.Minisat.(report stdout cnf @@ run "test.cnf" "test.out" cnf)


