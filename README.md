# hardcaml-affirm

[![Build Status](https://travis-ci.org/ujamjar/hardcaml-affirm.svg?branch=master)](https://travis-ci.org/ujamjar/hardcaml-affirm)

Sequential verification tools for HardCaml.

## NuSMV backend

Generates a NuSMV model from a HardCaml circuit.

```
let circuit = HardCamlAffrim.NuSMV..make "mytest" [ outputs ] [ properties ]
let () = NuSMV.write (output_string chan) circuit
```

In this backend a circuit is a combination of both outputs and properties expressed
with the Props.CTL and Props.LTL modules.

The function NuSMV.make creates a circuit which ensures it includes all atomic
propositions included in the properties.

### Example; equivalence checking

```
open HardCamlAffirm 

let equivalent f1 f2 input = 
  let out1 = f1 input in
  let out2 = f2 input in
  `CTL Props.CTL.(ag (p (out1 ==: out2)))

let circ = NuSMV.make "test_equiv" [] [ equivalent f1 f2 input ]
let () = NuSMV.write print_string circ
```

## Bounded model checking

Unrolls a circuit over `k` time steps and checks it against a LTL
property specification.

BMC is particularly useful for finding counter examples to a property
specifiction.  Proving correctness is generally only possible up to 
the bound `k` (although there are cases where infinite traces can
be proven due to state loops - in general this will only happen with
simple sequential circuits with a small state space).

Note that the functions in the `Bmc` module evaluate the LTL formula
as given (ie it is NOT negated as many other tools tend to do).  To
find a counter-example (or prove!) a LTL property `prop` it should be
passed negated to these functions.  If `sat` is returned then it 
will provide a counterexample.  If `unsat` is returned, then the
formula is either proved, or the bound is not large enough.

### Example;

```
(* Generate properties from circuit *)
let ltl = Props.LTL.(g (f (p some_property_from_circuit)))

(* Run bounded model checker for 10 steps.  If satisifiable display
   result in waveform viewer. *)
let () = Waves.run @@ Bmc.run ~verbose:true ~k:10 (~: ltl)
```

If a counter example is found the result can be viewed with
HardCamlWaveTerm.

![bmc-wave](https://cloud.githubusercontent.com/assets/5944099/18785518/83f9770c-8190-11e6-910c-a845179c40af.jpg)


