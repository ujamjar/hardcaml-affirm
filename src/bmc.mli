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
                 B.t list * B.t list * ((uid * B.t) list array)

end

module LTL : sig

  (** association list from the uid of the (original) property to the computed
      propery 'value' at this step *)
  type prop_set = (uid * t) list
  
  type prop_steps = prop_set array (* length=k+1 *)

  module M : Map.S

  val compile_no_loop :
    map:t M.t ->
    props:prop_steps ->
    ltl:Props.LTL.path ->
    t M.t * t

  val compile_loop :
    map:t M.t ->
    props:prop_steps ->
    ltl:Props.LTL.path ->
    l:int ->
    t M.t * t

  (** compile LTL property *)
  val compile :
    props:prop_steps ->
    ltl:Props.LTL.path ->
    loop_k: t list ->
    k:int ->
    t

end

(** generate a BMC formula for a circuit and LTL formula over k>=0 time steps. *)
val compile : ?verbose:bool -> 
              k:int -> Props.LTL.path -> 
              t

(** run BMC with bound k *)
val run1 : ?verbose:bool -> 
           k:int -> Props.LTL.path -> 
           (int * ((string * string array) list)) Dimacs.result

val print : k:int -> Props.LTL.path -> unit

(** Iteratively run BMC for up to k time steps *)
val run : ?verbose:bool -> 
          k:int -> Props.LTL.path -> 
          (int * ((string * string array) list)) Dimacs.result

