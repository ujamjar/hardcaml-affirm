(* verification examples from the chalmers lava tutorial *)

#require "hardcaml";;
#mod_use "src/NuSMV.ml";;

open HardCaml.Signal.Comb

(* 2.1 *)
let halfAdd (a,b) = a ^: b, a &: b

(* 2.3 *)
let fullAdd (carryIn,(a,b)) = 
  let sum1, carry1 = halfAdd(a,b) in
  let sum, carry2 = halfAdd(carryIn,sum1) in
  sum, (carry2 ^: carry1)

let adder cin a b = 
  concat @@ snd @@
    List.fold_right2 
      (fun a b (c,l) -> 
        let s,c = fullAdd (c,(a,b)) in 
        c,s::l) 
      (bits a) (bits b) (cin,[])

let adder2 a b = adder gnd a b

let prop_HalfAddOutputNeverBothTrue (a,b) = 
  let sum,carry = halfAdd (a,b) in
  output "prop" (~: (sum &: carry))

let prop_FullAddCommutative (c,(a,b)) = 
  let s0,c0 = fullAdd (c,(a,b)) in
  let s1,c1 = fullAdd (c,(b,a)) in
  output "prop" ((s0==:s1) &: (c0==:c1))

let prop_EquivAdders8 (a,b) = 
  let x = adder2 a b in
  let y = a +: b in
  output "prop" (x ==: y)

let prop_AdderCommutative (a,b) = 
  output "prop" (adder2 a b ==: adder2 b a)

(* 5.1 *)

open HardCaml.Signal.Seq

let r' = reg r_none empty
let r'1s d = reg {r_none with HardCaml.Signal.Types.reg_reset_value=(ones (width d))} empty d
let r'fb = reg_fb r_none empty 

let toggle change = 
  let w = wire 1 in
  let out = change ^: w in
  w <== r' out;
  out

let edge d = 
  let d' = r' d in
  d ^: d'

(* 6.1 *)
let prop_ToggleEdgeIdentity inp = 
  let mid = toggle inp -- "mid" in
  let out = edge mid -- "out" in
  output "prop" (inp ==: out)

(* 5.4 *)

let addSeq (a,b) = 
  let carryIn = wire 1 in
  let sum, carryOut = fullAdd (carryIn, (a,b)) in
  carryIn <== r' carryOut;
  sum

let rowSeq f x = 
  let carryIn = wire 1 in
  let out, carryOut = fullAdd (carryIn, x) in
  carryIn <== r' carryOut;
  out

let addSeq' = rowSeq fullAdd

(* 6.1 *)
let prop_SameAdderSeq x = 
  output "prop" (addSeq x ==: addSeq' x)

(* 6.2 *)
let (==>:) a b = (~: a) |: b

let prop_ToggleTogglesWhenHigh inp = 
  let out = toggle inp in
  let out' = r' out in
  let change = out ^: out' in
  output "prop" (inp ==>: change)

(* 5.2 *)

let rec delayN n inp = 
  if n=0 then inp
  else
    r' (delayN (n-1) inp)

let puls n = 
  let last = wire 1 in
  let rec f n = 
    if n=1 then r'1s last
    else r' (f (n-1))
  in 
  let out = f n in
  last <== out;
  out

(* 6.5 *)

let prop_Toggle_vs_Puls = 
  let out1 = toggle vdd in
  let out2 = puls 2 in
  output "prop" (~: (out1 ==: out2))

(* verification tests *)

let a,b,cin = input "a" 1, input "b" 1, input "cin" 1 
let a8,b8 = input "a" 8, input "b" 8

let test=int_of_string Sys.argv.(1)
let () = 
  let write props = NuSMV.write print_string (HardCaml.Circuit.make "test" props) in
  match test with
  | 0 -> write [ prop_HalfAddOutputNeverBothTrue (a,b) ]
  | 1 -> write [ prop_FullAddCommutative (cin,(a,b)) ]
  | 2 -> write [ prop_EquivAdders8 (a8,b8) ]
  | 3 -> write [ prop_AdderCommutative (a8,b8) ]
  | 4 -> write [ prop_ToggleEdgeIdentity a ]
  | 5 -> write [ prop_SameAdderSeq (a,b) ]
  | 6 -> write [ prop_ToggleTogglesWhenHigh a ]
  | 7 -> write [ prop_Toggle_vs_Puls ]
  | _ -> print_string "NO TEST\n"

