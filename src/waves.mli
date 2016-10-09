module B : HardCaml.Comb.S
module W : HardCamlWaveTerm.Wave.W with type elt = B.t
module Widget : module type of HardCamlWaveTerm.Widget.Make(B)(W)

(** convert the data from a sat result from Bmc.run to waves *)
val to_waves : int * ((string * string array) list) -> W.waves

(** run interactive waveform viewer *)
val run : (int * ((string * string array) list)) Sattools.Result.t -> unit

