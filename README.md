# hardcaml-affirm

Verification tools for hardcaml designs.

* NuSMV - generates SMV files readable with NuSMV.  Each circuit output should be a 1 bit property and will be checked with the CTL expression `AG prop`

```
let circuit = Circuit.make "mytest" [ list_of_properties ]
let () = NuSMV.write (output_string chan) circuit
```


