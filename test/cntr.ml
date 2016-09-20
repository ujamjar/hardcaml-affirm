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
let y_is_2 = y ==:. 2
let y_is_4 = y ==:. 4
let y_is_6 = y ==:. 6

open HardCamlAffirm

(* is y=4 then next state y=6 (obviously false) *)
let ltl_missing_5 = 
  Props.LTL.( ~: (g ((p y_is_4) ==>: (x (p y_is_6))) ))

(* will hit 2 infinitely *)
let ltl_2_repeats = 
  Props.LTL.(g (f (p y_is_2)))



