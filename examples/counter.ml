let help_message = "\
HardCamlAffirm counter verification example
-------------------------------------------

(c) 2016 MicroJamJar Ltd.

Verification tests for a counter with the following behaviour

init: counter[bits-1:0] := 0
next: if counter = wraps_at then 
        counter := wraps_to
      else 
        counter := counter + step

With this various counter behaviours can be configured i.e.

-bits 1 -wraps-at 1 -wraps-to 0

  0 1 0 1 0 1 ....

-bits 2 -wraps-at 3 -wraps-to 3

  0 1 2 3 3 3 ....

-bits 2 -wraps-at 2 -wraps-to 1

  0 1 2 1 2 1 ....

-bits 3 -wraps-at 7 -wraps-to 6 -step 3

  0 3 6 1 4 7 6 1 4 7 ...

Three different properties may be checked for particular
values of the counter

-is-never 'value' 

  G counter<>value

  counter is never the given value

-is-repeatedly 'value'

  G F counter=value

  counter will infinitely often be the given value

-finally-always 'value'

  F G counter=value

  counter will reach the given value and keep it
"

let nbits = ref 2
let wraps_at = ref 3
let wraps_to = ref 0
let step = ref 1

let repeatedly = ref (-1)
let never = ref (-1)
let finally_always = ref (-1)

let k = ref 10
let solve = ref false
let verbose = ref false

let nusmv = ref ""

let () = Arg.(parse
  (align @@ [
    (* counter configuration *)
    "-bits", Set_int nbits, " bits in counter";
    "-wraps-at", Set_int wraps_at, " max value of counter";
    "-wraps-to", Set_int wraps_to, " next value after max";
    "-step", Set_int step, " counter increment value";
    (* testable properties *)
    "-is-repeatedly", Set_int repeatedly, " counter is repeatedly the given value";
    "-is-never", Set_int never, " counter is never the given value";
    "-finally-always", Set_int finally_always, " eventually the counter is the given value";
    (* BMC configuration *)
    "-k", Set_int k, " number of steps to check";
    "-solve", Arg.Set solve, " show solution at step k rather than search for counter example";
    "-v", Arg.Set verbose, " verbose";
    (* generate NuSMV file *)
    "-nusmv", Arg.Set_string nusmv, " write NuSMV file";
  ])
  (fun _ -> ())
  help_message)

(* Design under test - the configurable counter *)

open HardCaml
open Signal.Comb
open Signal.Seq

let counter = 
  reg_fb r_none empty !nbits
    (fun d -> mux2 (d ==:. !wraps_at) (consti !nbits !wraps_to) (d +:. !step)) -- "counter"

let counter_is = 
  let counter_is = Array.init (1 lsl !nbits) 
      (fun i -> output ("counter_is" ^ string_of_int i) (counter ==:. i))
  in
  Array.get counter_is

(* Run tests *)

let tests = List.map snd @@ List.filter fst @@ [
  !repeatedly >= 0,     (fun () -> Props.LTL.(g (f (p (counter_is !repeatedly)))));
  !never >= 0,          (fun () -> Props.LTL.(g (~: (p (counter_is !never)))));
  !finally_always >= 0, (fun () -> Props.LTL.(f (g (p (counter_is !finally_always)))));
]

(* bounded model checker *)
let run ltl =
  let soln = 
    match !solve with
    | false -> Bmc.run ~verbose:!verbose ~k:!k Props.LTL.(~: ltl)
    | true -> Bmc.run1 ~verbose:!verbose ~k:!k ltl
  in
  match soln with
  | `unsat -> Printf.printf "unsat\n"
  | `sat _ as x -> Waves.run x (* note; escape to quit *)

let () = List.iter (fun ltl -> run (ltl())) tests

(* generate nusmv file *)
let () = 
  if !nusmv <> "" then begin
    let f = open_out !nusmv in
    let c = NuSMV.make "counter" [] (List.map (fun p -> `LTL (p())) tests) in
    NuSMV.write (output_string f) c;
    close_out f;
  end

