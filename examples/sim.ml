(*
   In this test we define a simple statemachine and use
   bounded model checking to show execution traces which 
   lead to a final state and also demonstrate some provable
   properties of the circuit.

   The code is also designed to use a couple of extra features
   of the library

   1. We use a simulator to initialise the starting point for BMC
   2. The circuit is defined with interfaces and we use them
      to generate the verification models and simulations.

*)

open HardCaml
open Signal.Comb
open Signal.Seq
open HardCamlAffirm
module B = Bits.Comb.IntbitsList 

module I = interface start[1] end
module O = interface is{|4|}[1] end

let test = try int_of_string Sys.argv.(1) with _ -> failwith "specify which test to run"

(************* HARDWARE ************)

(* upon application of the start signal we will sequence 
   through states 2, 1, 0, 3 and remain in 3 forever *)
let hw i = 
  let open Signal.Guarded in
  let state = g_reg 
      { r_none with 
        Signal.Types.reg_reset = gnd; (* start in state 2 *)
        Signal.Types.reg_reset_value = consti 2 2 } 
      empty 2 
  in
  let () = compile [
    g_switch (state#q -- "state")  [
      (consti 2 0), [ state $==. 3 ];
      (consti 2 1), [ state $==. 0 ];
      (consti 2 2), [ g_when i.I.start [ state $==. 1 ] ];
      (consti 2 3), [ ];
    ]
  ] in
  { O.is = Array.init 4 (fun i -> state#q ==:. i); }

module G = Bmc.Gen_with_sim(B)(I)(O)

(* run testbench for some 'cycles' and optionally display
   a waveform of the result *)
let tb sim show cycles =
  let sim, i = sim.G.sim, sim.G.inputs in
  let sim, viewer = 
    let module W = HardCamlWaveTerm.Wave.Make(HardCamlWaveTerm.Wave.Bits(B)) in
    let module Ws = HardCamlWaveTerm.Sim.Make(B)(W) in
    let module Ui = HardCamlWaveLTerm.Widget.Make(B)(W) in
    let sim, waves = Ws.wrap sim in
    sim, (fun () -> Ui.run W.{ cfg=default; waves } )
  in
  let module S = Cyclesim.Api in
  S.reset sim;
  i.I.start := B.vdd;
  for j=0 to cycles-1 do
    S.cycle sim;
    i.I.start := B.gnd;
  done;
  (if show then Lwt_main.run (viewer()))

(* run BMC for 'k' cycles with a model initialised after
   running a simulation for 'cycles'. *)
let run_bmc ~cycles ~waves ~k ~ltl =
  let bmc, sim = G.make "test" hw ltl in
  let () = tb sim waves cycles in
  match bmc.Bmc.run k with
  | `unsat -> Printf.printf "UNSAT\n"
  | _ as x -> Waves.run x

(* select a test to run *)
let test i msg f =
  if test = i then begin
    print_string msg; 
    f()
  end

(************* TESTS ************)
 
open Props.LTL
open O
open I

let () = test 1 "\
Run the simulation for 6 cycles and display the waveform.
" 
  (fun () -> run_bmc ~cycles:6 ~waves:true ~k:0 ~ltl:(fun _ _ -> gnd))

let () = test 2 "\
Run BMC for 3 steps and show we get into state 3.

Note the behvaiour of 'start' - we did not specify this, 
BMC inferred it.
"
  (fun () -> run_bmc ~cycles:0 ~waves:false ~k:3 ~ltl:(fun _ o -> x ~n:3 o.is.(3)))


let () = test 3 "\
Run BMC for 3 steps but this time look for 1 in the 
last step.

Again note the behaviour of 'start' which is being inferred
by BMC.
"
  (fun () -> run_bmc ~cycles:0 ~waves:false ~k:3 ~ltl:(fun _ o -> x ~n:3 o.is.(1)))

let () = test 4 "\
Show that the statemachine will eventually get to the 
value 3 and stay there.

To prove this we use the formula !(F G is_3).  Note 
that we also will need to start the machine running
which we will also need to encode.

    !(start -> (F G is_3))
"
  (fun () -> run_bmc ~cycles:0 ~waves:false ~k:3 
      ~ltl:(fun i o -> (~: (i.start ==>: f (g o.is.(3))))))

let () = test 5 "\
In test 4 we needed to encode the start up behaviour
of the circuit in the LTL formula (start is high in 
the first cycle).

This time we will perform the start in simulation
and initialise bmc using the simulators state.  bmc
will be run for 1 less cycle.
"
  (fun () ->
    run_bmc ~cycles:1 ~waves:false ~k:2 ~ltl:(fun _ o -> (~: (f (g o.is.(3))))))

