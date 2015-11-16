module Comb : HardCaml.Comb.S with type t = HardCaml.Signal.Comb.t

module Transform : HardCaml.Transform.TransformFn

val convert_circuit : HardCaml.Circuit.t -> HardCaml.Circuit.t

