(* example from
 
 https://www.youtube.com/watch?v=qXGKvMrF7XA
  satish Kashyap; Lect-24 Bounded Model Checking

*)

#require "hardcaml-bloop";;

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

