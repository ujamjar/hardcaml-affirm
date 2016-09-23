(* what the heck is the difference between the optimising and non-optimising
 * compile_loop functions??? *)

#require "hardcaml-bloop";;

module S = HardCaml.Signal.Comb
module T = HardCaml.Signal.Types
module G = HardCamlBloop.Gates.Make_comb(HardCamlBloop.Gates.Basic_gates)

module LTL = struct

  (* LTL properties.
   
    We'll take a LTL formula built from properties (single bits) compiled
    as part of the circuit.

    We'll be given an array of property sets for each time step.  If k=0 then we get
    1 set of properties, k=1 gives 2 sets and so on.

    Next we should build the combinatorial logic representing the LTL formula

  *)

  (* an association list from the uid of the (original) property to the computed
     propery 'value' at this step *)
  type prop_set = (T.uid * S.t) list
  
  type prop_steps = prop_set array (* length=k+1 *)

  module M = Map.Make(struct
      type t = int * Props.LTL.path
      let compare = compare
  end)

  let loop map f l h = 
    let rec loop map lst l = 
      if l > h then map, List.rev lst 
      else 
        let map, x = f map l in
        loop map (x::lst) (l+1) 
    in
    loop map [] l 

  let scan f p = 
    let rec scan f l p = 
      match p with 
      | [] -> l 
      | h :: t -> scan f (h :: List.map (fun p -> f p h) l) t 
    in
    List.rev @@ scan f [] p 
  
  let compile_loop_no_opt ~props ~ltl ~l = 
    let open G in

    let ltl = Props.LTL.nnf ltl in
    let k = Array.length props - 1 in

    let succ i = if i < k then i+1 else l in 

    let open Printf in
    let () = printf "*** COMPILE_LOOP K=%i L=%i\n" k l in
    let rec g map i ltl = 
      if M.mem (i,ltl) map then 
        let x = M.find (i,ltl) map in
        map, x
      else
        let addi map i x = 
          M.add (i,ltl) x map, x 
        in
        let add map x = addi map i x in
        let add2 f a b = 
          let map, a = g map i a in
          let map, b = g map i b in
          add map (f a b)
        in
        (* recursively generate propositions over time steps *)
        match ltl with
        | Props.LTL.True -> 
          map, vdd
        | Props.LTL.Not Props.LTL.True -> 
          map, gnd
        | Props.LTL.P p -> 
          add map @@ List.assoc (T.uid p) props.(i)
        | Props.LTL.Pn p -> 
          add map @@ ~: (List.assoc (T.uid p) props.(i))
        | Props.LTL.And(a,b) -> 
          add2 (&:) a b
        | Props.LTL.Or(a,b) -> 
          add2 (|:) a b
        | Props.LTL.X p -> 
          let map, p = g map (succ i) p in
          add map p

        (* XXX TODO *)
        | Props.LTL.U(a,b) -> failwith "U"
        | Props.LTL.R(a,b) -> failwith "R"


        | Props.LTL.F p -> 
          let map, x = loop map (fun map i -> g map i p) (min l i) k in
          add map @@ reduce (|:) x
     
        | Props.LTL.G p -> 
          let map, x = loop map (fun map i -> g map i p) (min l i) k in
          add map @@ reduce (&:) x

        | Props.LTL.Not _ -> failwith "not in negated normal form"
    in

    snd @@ g M.empty 0 ltl

  let compile_loop_opt ~props ~ltl ~l = 
    let open G in

    let ltl = Props.LTL.nnf ltl in
    let k = Array.length props - 1 in

    let succ i = if i < k then i+1 else l in 

    let open Printf in
    let () = printf "*** COMPILE_LOOP K=%i L=%i\n" k l in
    let rec g map i ltl = 
      let get_min_idx i =  
        match ltl with
        | Props.LTL.G _ | Props.LTL.F _ -> min i l 
        | _ -> i
      in
      if M.mem (get_min_idx i,ltl) map then 
        let x = M.find (get_min_idx i,ltl) map in
        map, x
      else
        let addi map i x = M.add (i,ltl) x map, x in
        let add map x = addi map i x in
        let add2 f a b = 
          let map, a = g map i a in
          let map, b = g map i b in
          add map (f a b)
        in
        let create_temporal_loops f p = 
          let map, ps = loop map (fun map i -> g map i p) 0 k in
          let ps = scan f ps in
          fst @@ List.fold_left 
            (fun (map,i) p -> (fst @@ addi map i p), i+1) (map,0) ps 
        in
        (* recursively generate propositions over time steps *)
        match ltl with
        | Props.LTL.True -> 
          map, vdd
        | Props.LTL.Not Props.LTL.True -> 
          map, gnd
        | Props.LTL.P p -> 
          add map @@ List.assoc (T.uid p) props.(i)
        | Props.LTL.Pn p -> 
          add map @@ ~: (List.assoc (T.uid p) props.(i))
        | Props.LTL.And(a,b) -> 
          add2 (&:) a b
        | Props.LTL.Or(a,b) -> 
          add2 (|:) a b
        | Props.LTL.X p -> 
          let map, p = g map (succ i) p in
          add map p

        (* XXX TODO *)
        | Props.LTL.U(a,b) -> failwith "U"
        | Props.LTL.R(a,b) -> failwith "R"

        | Props.LTL.F p -> 
          g (create_temporal_loops (|:) p) i ltl

        | Props.LTL.G p -> 
          g (create_temporal_loops (&:) p) i ltl

        | Props.LTL.Not _ -> failwith "not in negated normal form"
    in

    snd @@ g M.empty 0 ltl

end

open G

let k = 10
let l = 5

let props,ltl =
  let y_is_2 = S.input "y_is_2_" 1 in
  let props = 
    Array.init (k+1) @@ fun i ->
      [ T.uid y_is_2, 
        input ("p/" ^ string_of_int i ^ "/") 1 ]
  in
  let ltl = Props.LTL.(nnf @@ (g (f (p y_is_2)))) in
  props, ltl

let f = LTL.compile_loop_opt ~props ~ltl ~l
let g = LTL.compile_loop_no_opt ~props ~ltl ~l
let () = Printf.printf "\n%s\n" (G.to_string f)
let () = Printf.printf "%s\n" (G.to_string g)

let sat = HardCamlBloop.Sat.(report @@ of_signal @@ (f <>: g))


