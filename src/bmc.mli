open HardCaml
open Signal.Types
open Signal.Comb

module Init_state(B : HardCaml.Comb.S)(B_sim : HardCaml.Comb.S) : sig

  val init_state : t -> B.t

  val init_from_sim : B_sim.t HardCaml.Cyclesim.Api.cyclesim -> t -> B.t

end

(** Unroll circuit *)
module Unroller(B : HardCaml.Comb.S) : sig

  (* Unroll circuit over k time steps.  Returns the transition function,
     loop clause(s) and properties over time *)
  val unroller : ?verbose:bool -> 
                 ?init_state:(t -> B.t) ->
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

(** By default the BMC routines ignore the register reset/clear/enable.

    To keep them they should be converted into muxes at the front of the registers.
    This function will extract a circuit from the LTL specification, transform it
    optionally generating muxes for the reset/clear/enable signals, then rewrite the
    LTL formula with the revised atomic propositions *)
val transform_regs : reset:bool -> clear:bool -> enable:bool -> Props.LTL.path -> Props.LTL.path

(** generate a BMC formula for a circuit and LTL formula over k>=0 time steps. *)
val compile : ?verbose:bool -> 
              ?init_state:(t -> t) ->
              k:int -> 
              Props.LTL.path -> 
              t

type bmc_result = (int * ((string * string array) list)) Dimacs.result

(** run BMC with bound k *)
val run1 : ?verbose:bool -> 
           ?init_state:(t -> t) ->
           k:int -> Props.LTL.path -> 
           bmc_result

val print : ?init_state:(t -> t) ->
            k:int -> 
            Props.LTL.path -> unit

(** Iteratively run BMC for up to k time steps *)
val run : ?verbose:bool -> 
          ?init_state:(t -> t) ->
          k:int -> Props.LTL.path -> 
          bmc_result

(** Interface flow *)

type bmc = 
  {
    run : ?verbose:bool -> int -> bmc_result;
    run1 : ?verbose:bool -> int -> bmc_result;
  }

module Gen(I : Interface.S)(O : Interface.S) : sig

  open Props.LTL
  val make : string -> (t I.t -> t O.t) -> (path I.t -> path O.t -> path) -> bmc 

end

module Gen_with_sim(B : Comb.S)(I : Interface.S)(O : Interface.S) : sig

  module S : module type of Cyclesim.Make(B)

  type sim = 
    {
      sim : S.cyclesim;
      inputs : B.t ref I.t;
      outputs : B.t ref O.t;
      next : B.t ref O.t;
    }

  open Props.LTL
  val make : string -> (t I.t -> t O.t) -> (path I.t -> path O.t -> path) -> bmc * sim

end
