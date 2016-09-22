#require "hardcaml";;
#directory "_build/src";;
#load "HardCamlAffirm.cma";;

open HardCaml.Signal.Comb
open HardCaml.Signal.Seq

(* 4 bit counter, wraps 0..7 *)
let y = reg_fb r_none empty 4 @@ fun d -> 
    mux2 (d ==:. 7) (zero 4) (d +:. 1)
let y = y -- "counter"

(* properties *)
open HardCamlAffirm

let y_is = 
  let y = Array.init 16 (fun i -> output ("y_is_" ^ string_of_int i) (y ==:. i)) in
  fun i -> Props.LTL.p (Array.get y i)

(* is y=4 then next state y=6 (obviously false) *)
let ltl_missing_5 = 
  Props.LTL.( ~: (g ((y_is 4) ==>: (x (y_is 6))) ))

(* will hit 2 infinitely *)
let ltl_2_repeats = 
  Props.LTL.(g (f (y_is 2)))



