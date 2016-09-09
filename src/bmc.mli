open HardCaml
open Signal.Types
open Signal.Comb

val simple_reg : (uid -> t) -> register -> t -> t -> register * t

module SimplifyRegs : Transform.TransformFn

module Unroll : sig
  type step 
  val transform : step -> (uid -> t) -> t -> t
end

module LTL : sig

  (* an association list from the uid of the (original) property to the computed
     propery 'value' at this step *)
  type prop_set = (uid * t) list
  
  type prop_steps = prop_set array (* length=k+1 *)

  val compile :
    props:prop_steps ->
    loop_k:t ->
    ltl:Props.LTL.path ->
    t

end

val unroll : k:int -> t list -> t * t * ((uid * t) list array)

val compile_ltl : k:int -> ltl:Props.LTL.path -> t

