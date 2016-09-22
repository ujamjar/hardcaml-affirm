module B : HardCaml.Comb.S
module W : HardCamlWaveTerm.Wave.W with type elt = B.t
module Widget : module type of HardCamlWaveLTerm.Widget.Make(B)(W)

val to_waves : int * ((string * string array) list) -> W.waves

val run : (int * ((string * string array) list)) Dimacs.result -> unit

