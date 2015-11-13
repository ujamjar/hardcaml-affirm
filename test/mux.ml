(* verification with muxes. *)

#require "hardcaml";;
#mod_use "src/NuSMV.ml";;

open HardCaml.Signal.Comb
module B = HardCaml.Bits.Comb.IntbitsList

let binop ((op:t->t->t),(bop:B.t->B.t->B.t)) w : t = 
  let a, b = input "a" w, input "b" w in
  let mask = (1 lsl w) - 1 in
  output "prop"
    ((op a b) ==: 
        (mux_init (b @: a) (1 lsl (w*2)) 
          (fun i -> 
            let a, b = i land mask, (i lsr w) in
            let c = bop (B.consti w a) (B.consti w b) in
            constibl c)))

let gen x = NuSMV.write print_string (HardCaml.Circuit.make "test" [x])

(*let () = gen (binop ((&:),B.(&:)) 2)*)
let () = gen (binop ((+:),B.(+:)) 4)


