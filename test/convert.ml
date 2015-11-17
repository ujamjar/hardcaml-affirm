(* test Dimacs.Comb 
 *
 * This API implements add, sub, mul(s), (n)eq, lt and mux in terms
 * of and/or/xor/not gates.  This test checks the implementation is
 * correct. *)

#require "hardcaml";;
#directory "_build/src";;
#load "HardCamlAffirm.cma";;

open HardCamlAffirm
open HardCaml.Signal.Comb

let binop name op opb n m = 
  let (--) a b = a -- (name ^ "_" ^ b) in
  let input n b = input (name ^ "_" ^ n) b in
  let a, b = input "a" n, input "b" m in
  (((op a b) -- "reference") ==: (concat (opb (bits a) (bits b)) -- "dimacs")) -- "prop"

let binop2 name op opb = [
  (binop (name^"1") op opb 1 1);
  (binop (name^"2") op opb 2 2);
  (binop (name^"3") op opb 3 3);
  (binop (name^"8") op opb 8 8); 
]

let binopm name op opb = [
  (binop (name^"11") op opb 1 1);
  (binop (name^"22") op opb 2 2);
  (binop (name^"23") op opb 2 3);
  (binop (name^"32") op opb 3 2);
  (binop (name^"59") op opb 5 9);
]

let muxop name op opb ws lm wm = 
  let (--) a b = a -- (name ^ "_" ^ b) in
  let input n b = input (name ^ "_" ^ n) b in
  let sel = (input "sel" ws) in
  let d = Array.to_list @@ Array.init lm (fun i -> srand wm) in
  ((op sel d -- "reference") ==: (concat (opb (bits sel) (List.map bits d)) -- "dimacs")) -- "prop"

let muxops = [
  muxop "mux121" mux Dimacs.Comb.mux 1 2 1;
  muxop "mux222" mux Dimacs.Comb.mux 2 2 2;
  muxop "mux242" mux Dimacs.Comb.mux 2 4 2;
  muxop "mux374" mux Dimacs.Comb.mux 3 7 4;
  muxop "mux462" mux Dimacs.Comb.mux 4 6 2;
  muxop "mux495" mux Dimacs.Comb.mux 4 9 5;
]

let gen props = 
  let circ = NuSMV.make "test" [] 
    (List.map (fun prop -> `CTL Props.CTL.(ag @@ p prop)) props) 
  in
  NuSMV.write print_string circ

let () = 
  let t, f = true, false in
  gen @@
  (if t then binop2 "add"  (+:)   Dimacs.Comb.(+:)   else []) @ 
  (if t then binop2 "sub"  (-:)   Dimacs.Comb.(-:)   else []) @
  (if t then binop2 "eq"   (==:)  Dimacs.Comb.(==:)  else []) @
  (if t then binop2 "neq"  (<>:)  Dimacs.Comb.(<>:)  else []) @
  (if t then binop2 "lt"   (<:)   Dimacs.Comb.(<:)   else []) @
  (if t then binopm "mulu" ( *: ) Dimacs.Comb.( *: ) else []) @
  (if t then binopm "muls" ( *+ ) Dimacs.Comb.( *+ ) else []) @
  (if t then muxops                                  else []) @
  []

