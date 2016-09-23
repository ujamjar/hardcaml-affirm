#require "hardcaml-waveterm.lterm";;
#directory "_build/src";;
#load "HardCamlAffirm.cma";;

open HardCaml
open Signal.Comb
open Signal.Seq

(* a generic register *)
let q = output "q" (reg r_full enable (input "d" 1))

open HardCamlAffirm

let print ltl = 
  let props = Props.LTL.atomic_propositions ltl in
  Rtl.Verilog.write print_string @@ Circuit.make "ltl" props;
  ltl

let ltl0 = print @@ Props.LTL.(p q)
let ltl1 = print @@ Bmc.transform_regs ~reset:false ~clear:true  ~enable:true  ltl0
let ltl2 = print @@ Bmc.transform_regs ~reset:false ~clear:false ~enable:true  ltl0
let ltl3 = print @@ Bmc.transform_regs ~reset:false ~clear:true  ~enable:false ltl0
let ltl4 = print @@ Bmc.transform_regs ~reset:true  ~clear:false ~enable:false ltl0


