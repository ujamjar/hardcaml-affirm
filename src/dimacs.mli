val convert : HardCaml.Signal.Comb.t -> Sat.relabelled Sat.sat

val write : out_channel -> Sat.relabelled Sat.sat -> unit

val run : ?solver:string -> ?verbose:bool -> Sat.relabelled Sat.sat -> bool

