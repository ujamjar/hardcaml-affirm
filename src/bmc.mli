open HardCaml
open Signal.Types
open Signal.Comb

(** simplify hardcaml registers to delay elements (remove reset, clear and enable) *)
val simple_reg : (uid -> t) -> register -> t -> t -> register * t

module SimplifyRegs : Transform.TransformFn

(** Unroll circuit *)
module Unroller(B : HardCaml.Comb.S) : sig

  (* Unroll circuit over k time steps.  Returns the transition function,
     loop clause(s) and properties over time *)
  val unroller : ?verbose:bool -> 
                 k:int -> t list -> 
                 B.t * B.t list * ((uid * B.t) list array)

end

type loop = [ `none | `all | `offset of int]
type mode = [ `limit_formula | `min_k]

module LTL : sig

  (** association list from the uid of the (original) property to the computed
      propery 'value' at this step *)
  type prop_set = (uid * t) list
  
  type prop_steps = prop_set array (* length=k+1 *)

  (** compile LTL property *)
  val compile :
    mode:mode ->
    props:prop_steps ->
    loop_k:t ->
    ltl:Props.LTL.path ->
    t

end

(** get loop clause (of k steps) *)
val get_loop : ?loop:loop -> loop_k:t list -> k:int -> unit -> t

(** generate a BMC formula for a circuit and LTL formula over k time steps.
 
    For a LTL formula with depth d, the circuit is unrolled (k+d) times.
    The (default) loop check will be for k steps. *)
val compile : ?verbose:bool -> ?mode:mode -> ?loop:loop -> 
              k:int -> Props.LTL.path -> 
              t

(** run BMC with bound k *)
val run1 : ?verbose:bool -> ?mode:mode -> ?loop:loop -> 
           k:int -> Props.LTL.path -> 
           ((string * string) list) Dimacs.result

(** Iteratively run BMC for up to k time steps *)
val run : ?verbose:bool -> ?mode:mode -> 
          k:int -> Props.LTL.path -> 
          (int * ((string * string) list)) Dimacs.result

