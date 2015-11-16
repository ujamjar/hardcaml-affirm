(* verification with muxes - check the conversion to NuSMV cases. 
 
   For (a 'op' b) generates a rom which implements the same function
   and compares them.
*)

#require "hardcaml";;
#directory "_build/src";;
#load "HardCamlAffirm.cma";;

open HardCamlAffirm

open HardCaml.Signal.Comb
open HardCaml.Signal.Seq

module B = HardCaml.Bits.Comb.IntbitsList

let binop (op,bop) w = 
  let a, b = input "a" w, input "b" w in
  let mask = (1 lsl w) - 1 in
  output "prop"
    ((op a b) ==: (* the operator ... *)
        (mux_init (b @: a) (1 lsl (w*2))  (* ... and the rom version *)
          (fun i -> 
            let a, b = i land mask, (i lsr w) in (* indices *)
            let c = bop (B.consti w a) (B.consti w b) in (* values *)
            constibl c)))

let gen prop = 
  let circ = NuSMV.make "test" [] [`CTL Props.CTL.(ag (p prop))] in
  NuSMV.write print_string circ

(*let () = gen (binop ((&:),B.(&:)) 2)*)
let () = gen (binop ((+:),B.(+:)) 4)

