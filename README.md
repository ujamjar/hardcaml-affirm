# hardcaml-affirm

**TODO**; more backends!

## NuSMV backend

Generates a NuSMV model of a hardware design.

```
let circuit = HardCamlAffrim.NuSMV..make "mytest" [ outputs ] [ properties ]
let () = NuSMV.write (output_string chan) circuit
```

In this backend a circuit a combination of both outputs and properties expressed
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

