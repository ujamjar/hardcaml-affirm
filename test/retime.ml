(* A retimed circuit - registers are moved around, but the functionality is the same *)

#require "hardcaml";;
#directory "_build/src";;
#load "HardCamlAffirm.cma";;

open HardCamlAffirm

open HardCaml.Signal.Comb
open HardCaml.Signal.Seq

let reg = reg r_full empty

let t0 a b = 
  let r0 = reg (a +: b) -- "r0" in
  let r1 = reg r0 -- "r1" in
  r1

let t1 a b = 
  let a0 = reg a -- "a0" in
  let b0 = reg b -- "b0" in
  let s1 = reg (a0 +: b0) in
  s1

let prop = 
  let a, b = input "a" 8, input "b" 8 in
  output "prop" ((t0 a b) ==: (t1 a b))

let circ = NuSMV.make "testme" [] [ 
  `LTL Props.LTL.(g (p prop));
  `CTL Props.CTL.(ag (p prop));
]

let () = NuSMV.write print_string circ

