(* the full loop/no-loop model checking formula from Biere et. al.
   requires us to generate comparisons between the kth state and ith state for
   0 <= i <= k.  If we find such a (k,l) loop it means there is an infinite
   path and can prove things for G properties.
  
   This is implemented by testing (Si = Sk) for each appropriate i, except
   when i=k.  I dont see how it makes sense to write (Sk = Sk) in this case
   (in terms of implementation they are the same thing).
  
   If you look at Biere tutorial paper "Bounded Model Checking Using 
   Satisfiability Solving" in the liveness example on page 7 they describe
   using an extra expansion to (k+1) and checking Si up to Sk against S(k+1).
 
   "the sequence of states s0,s1,s2 must be part of a loop, meaning 
    there must be a transition from the last state, s2, back to either 
    s0, s1, or itself. This is

    T(s2,s3) ∧ (s3 = s0 ∨ s3 = s1 ∨ s3 = s2 )"

   I think this makes sense, so here we test what is going on.
*)

#require "hardcaml-bloop";;

open HardCamlBloop
open Gates.Comb

(*

  Model a counter which loops at a specific value back to some other value ie.

   reg_fb r_none empty bits (fun d -> mux2 (d ==:. upto) countfrom (d +:. 1)
*)

type stage = 
  {
    c : t;
    t : t;
  }

let run_counter ~bits ~upto ~countfrom ~k = 

  Printf.printf "bits=%i upto=%i countfrom=%i k=%i\n"
    bits upto countfrom k;

  let counter d = mux2 (d ==:. upto) (consti bits countfrom) (d +:. 1) in

  let mk i f = 
    let c = input ("c"^string_of_int i) bits in
    let t = f c in
    { c ; t}
  in
  let x0 = mk 0 (fun c -> c ==:. 0) in

  let rec gen_trans cprev i k = 
    if i>k then []
    else 
      let c = mk i (fun c -> c ==: counter cprev.c) in
      c :: gen_trans c (i+1) k
  in
  let states = x0 :: gen_trans x0 1 (k+1) in
  let trans = reduce (&:) (List.map (fun c -> c.t) states) in

  let rec gen_loops l = 
    let l = List.rev l in
    let h,t = List.hd l, List.tl l in
    Array.of_list @@ List.map (fun t -> t.c ==: h.c) (List.rev t)
  in

  let loops = gen_loops states in

  for l=0 to Array.length loops - 1 do
      Printf.printf "l=%i: " l;
      Sat.(report @@ of_signal (trans &: loops.(l)))
  done

(* 0,1,2,3,4,4,4,4...*)
let () = run_counter ~bits:3 ~upto:4 ~countfrom:4 ~k:0
let () = run_counter ~bits:3 ~upto:4 ~countfrom:4 ~k:3
let () = run_counter ~bits:3 ~upto:4 ~countfrom:4 ~k:4
let () = run_counter ~bits:3 ~upto:4 ~countfrom:4 ~k:5
(* 0,0,0,0....*)
let () = run_counter ~bits:3 ~upto:0 ~countfrom:0 ~k:0
let () = run_counter ~bits:3 ~upto:0 ~countfrom:0 ~k:1
(* 0,1,0,1,0,1,0,1....*)
let () = run_counter ~bits:1 ~upto:1 ~countfrom:0 ~k:0
let () = run_counter ~bits:1 ~upto:1 ~countfrom:0 ~k:1
let () = run_counter ~bits:1 ~upto:1 ~countfrom:0 ~k:2
let () = run_counter ~bits:1 ~upto:1 ~countfrom:0 ~k:3
(* 0,1,2,3,1,2,3,1,2,3...*)
let () = run_counter ~bits:2 ~upto:3 ~countfrom:1 ~k:0
let () = run_counter ~bits:2 ~upto:3 ~countfrom:1 ~k:1
let () = run_counter ~bits:2 ~upto:3 ~countfrom:1 ~k:2
let () = run_counter ~bits:2 ~upto:3 ~countfrom:1 ~k:3
let () = run_counter ~bits:2 ~upto:3 ~countfrom:1 ~k:4


