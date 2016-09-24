open HardCaml
open Signal.Types
open Signal.Comb

type transform = (uid -> t) -> register -> t -> t -> register * t

val to_muxes : reset:bool -> clear:bool -> enable:bool -> transform

val transform : transform -> t list -> t list

module Make(I : Interface.S)(P : Interface.S) : sig
  val transform : transform -> (t I.t -> t P.t) -> t I.t -> t P.t
end

