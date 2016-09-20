open HardCaml
open Signal.Types
open Signal.Comb

(** simplify hardcaml registers to delay elements (remove reset, clear and enable) *)
val simple_reg : (uid -> t) -> register -> t -> t -> register * t

module SimplifyRegs : Transform.TransformFn

module Unroll : sig
  type step 
  val transform : step -> (uid -> t) -> t -> t
end

module Unroller(B : HardCaml.Comb.S) : sig

  val schedule : t list -> t list -> t list -> t list

  val copy_names : int -> B.t -> t -> B.t

  val create_signal : B.t UidMap.t -> t -> B.t

  val init_value : t -> B.t

  val unroller : k:int -> t list -> B.t * B.t list * ((uid * B.t) list array)

end

module LTL : sig

  (** association list from the uid of the (original) property to the computed
      propery 'value' at this step *)
  type prop_set = (uid * t) list
  
  type prop_steps = prop_set array (* length=k+1 *)

  (** compile LTL property *)
  val compile :
    props:prop_steps ->
    loop_k:t ->
    ltl:Props.LTL.path ->
    t

end

(** unroll circuit over k time steps *)
val unroll : k:int -> t list -> t * t list * ((uid * t) list array)

type loop = [`none|`all|`offset of int]

(** get loop clause (of k steps) *)
val get_loop : ?loop:loop -> loop_k:t list -> k:int -> unit -> t

(** generate a BMC formula for a circuit and LTL formula over k time steps.
 
    For a LTL formula with depth d, the circuit is unrolled (k+d) times.
    The (default) loop check will be for k steps. *)
val compile : ?loop:loop -> k:int -> Props.LTL.path -> t

(** run BMC with bound k *)
val run1 : ?loop:loop -> k:int -> Props.LTL.path -> ((string * string) list) Dimacs.result

(** Iteratively run BMC for up to k time steps *)
val run : k:int -> Props.LTL.path -> (int * ((string * string) list)) Dimacs.result

