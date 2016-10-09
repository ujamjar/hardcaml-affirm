type property = [ `LTL of Props.LTL.path | `CTL of Props.CTL.state ]
type circuit = HardCaml.Circuit.t * property list
type io = string -> unit

val make : string -> HardCaml.Signal.Comb.t list -> property list -> circuit

val write : io -> circuit -> unit

