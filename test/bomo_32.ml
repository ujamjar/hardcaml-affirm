#require "hardcaml-bloop";;

open HardCamlBloop
open Gates.Comb

let slice a n = Array.to_list @@ Array.init n (Array.get a)
let reduces op a n = reduce op @@ slice a n
let sat s = Sat.(report @@ of_signal s)

let (==>) a b = (~: a) |: b
let (<==>) a b = ~: (a ^: b) (* ~: (a ^: b) *)

let a, b = input "a" 10, input "b" 10
let a = Array.init 10 (bit a)
let b = Array.init 10 (bit b)

let bmc k i t p = 
  let t = Array.init (k-1) (fun i -> t i (i+1)) in
  let p = Array.init k p in
  i &: reduces (&:) t (k-1) &: reduces (|:) p k

(* safety *)

let i = (~: (a.(0))) &: (~: (b.(0)))

let t i j = 
  (a.(j) <==> (~: (a.(i)))) &: 
  (b.(j) <==> (a.(i) ^: b.(i)))

let p i = a.(i) &: b.(i)

let () = sat @@ bmc 3 i t p
let () = sat @@ bmc 4 i t p

(* liveness *)

(* AF ( b & a) - always finally (must eventually reach) a=1,b=1
 
   counter property

   EG ( ~b | ~a ) - exists globally (exists 1 path somewhere) where
                    a=0 or b=0 (so can never meet above criteria)
*)

let t i j = (t i j |: ( b.(i) &: (~: (a.(i))) &: b.(j) &: (~: (a.(j))) )) 
let p i = (~: (a.(i))) |: (~: (b.(i)))
let loop k = 
  reduce (|:) @@
  Array.to_list @@
  Array.init (k-1) (fun i -> (a.(i) <==> a.(k-1)) &: (b.(i) <==> b.(k-1)))

let () = sat (bmc 2 i t p &: loop 2)
let () = sat (bmc 3 i t p &: loop 3) (* no problem to here *)
let () = sat (bmc 4 i t p &: loop 4) (* find an issue now *)

