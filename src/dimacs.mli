module Comb_basic_gates : 
  HardCaml.Comb.T with type t = HardCaml.Signal.Comb.t list

module Comb : HardCaml.Comb.S with type t = HardCaml.Signal.Comb.t list

module Transform : HardCaml.Transform.TransformFn'

val convert_signals : HardCaml.Signal.Comb.t list -> Comb.t list

module Vars = HardCaml.Signal.Types.UidMap
type var = HardCaml.Signal.Types.uid
type clause = var list
type cnf = var list list

val bnot : var -> var -> cnf
val bor : var -> var -> var -> cnf
val band : var -> var -> var -> cnf
val bxor : var -> var -> var -> cnf

type cnf_inputs = (string * (var option list)) list
type cnf_result = [ `cnf_true | `cnf_false | `cnf of cnf * cnf_inputs * int ]
val cnf_of_circuit : HardCaml.Circuit.t -> cnf_result

module Minisat : sig
  type minisat_result = [ `unsat | `sat of int list ]
  val write_dimacs : out_channel -> cnf -> int -> unit
  val read_output : in_channel -> minisat_result
  val report : out_channel -> cnf_result -> minisat_result -> unit
  val run : ?v:bool -> string -> string -> cnf_result -> minisat_result
end

