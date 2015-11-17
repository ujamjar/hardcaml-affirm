(* Tseitin transformations playground *)

#require "hardcaml";;

open HardCaml.Api.B

let (~.) a = ~: a

let eval x = 
  List.fold_left (fun a b -> a &: (List.fold_left (|:) gnd b)) vdd x

let bnot z x = eval [ [x; z]; [~. x; ~. z] ] 

let bor z x = 
  let sum = List.fold_right (fun x a -> x :: a) x [~. z] in
  List.fold_right (fun x a -> [~. x; z] :: a) x [sum]
let bor z x y = eval @@ bor z [x;y]

let band z x =  
  let sum = List.fold_right (fun x a -> ~. x :: a) x [z] in
  List.fold_right (fun x a -> [x; ~. z] :: a) x [sum]
let band z x y = eval @@ band z [x;y]

let bxor z a b = 
  eval [ [~. z; ~. a; ~. b]; [~. z; a; b]; [z; ~. a; b]; [z; a; ~. b] ]

let _bnot = 
  let f z x = (z ==: (~: x)) ==: (bnot z x) in
  [
    f gnd gnd;
    f gnd vdd;
    f vdd gnd;
    f vdd vdd;
  ]

let op2 f g = 
  let f z x y = (z ==: (f x y)) ==: (g z x y) in
  [
    f gnd gnd gnd;
    f gnd gnd vdd;
    f gnd vdd gnd;
    f gnd vdd vdd;
    f vdd gnd gnd;
    f vdd gnd vdd;
    f vdd vdd gnd;
    f vdd vdd vdd;
  ]

let _band = op2 (&:) band
let _bor = op2 (|:) bor
let _bxor = op2 (^:) bxor


