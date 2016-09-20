(* example from
 
 https://www.youtube.com/watch?v=qXGKvMrF7XA
  satish Kashyap; Lect-24 Bounded Model Checking

*)

#require "hardcaml-bloop";;
#directory "_build/src";;
#load "HardCamlAffirm.cma";;

open HardCamlBloop
open Gates.Comb

let slice a n = Array.to_list @@ Array.init n (Array.get a)
let reduces op a n = reduce op @@ slice a n
let sat s = Sat.(report @@ of_signal s)

let (==>) a b = (~: a) |: b
let (<==>) a b = ~: (a ^: b) (* ~: (a ^: b) *)

let k = 4 
let input name bits = 
  let x = input name bits in
  Array.init bits (bit x)

let r1 = input "r1" k
let r2 = input "r2" k
let g1 = input "g1" k
let g2 = input "g2" k

let g1' r1 = r1
let g2' r1 r2 g1 = r2 &: (~: r1) &: (~: g1)

(* if r1 is high, g1 is high in next 2 clocks.
   property: G(r1 => Xg1 & XXg1)
   negated : F(r1 & (~Xg1 | ~XXg1)) *)

let i = g2.(0) &: (~: (g1.(0)))

let t i = (g1' r1.(i) ==> g1.(i+1)) &: 
          (g2' r1.(i) r2.(i) g1.(i) ==> g2.(i+1))

let z1 = r1.(0) &: (~: (g1.(1)))
let () = sat (i &: reduce (&:) [t 0; t 1] &: z1)

let z2 = (r1.(0) &: (~: (g1.(1)) |: ~: (g1.(2)))) |: (r1.(1) &: ~: (g1.(2)))
let () = sat (i &: reduce (&:) [t 0; t 1; t 2] &: z2)

open HardCaml.Signal.Comb
open HardCaml.Signal.Seq

let test k = 

  let r1 = input "r1" 1 in
  let r2 = input "r2" 1 in

  let g1' = output "g1" @@ reg r_none empty r1  in
  let g2' = output "g2" @@ reg r_none empty (r2 &: (~: r1) &: (~: g1')) in

  let open Props.LTL in

  let r1 = p r1 in
  let g1, g2 = p g1', p g2' in

  let ltl = g (r1 ==>: ((x g1) &: (x (x g1)))) in
  let ltl2 = f (r1 &: ((x (~: g1)) |: (x (x (~: g1))))) in
  let ltl3 = r1 ==>: x g1 in
  let ltl4 = g (~: g1) in

  let result = Bmc.run ~k (~: ltl) in
  let () = 
    Printf.printf "generating verilog...\n";
    Rtl.Verilog.write print_string @@
    Circuit.make "bmc" [ output "prop" @@ Bmc.compile ~k (~: ltl) ]
  in
  result

