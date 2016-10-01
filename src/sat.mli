type uid = int
type terms = int list list
type wire_name = (string * int) list ref
type 'a sat = 
  (* tracking sat clauses *)
  | P of uid * terms
  | C of uid * terms * 'a sat list
  (* wires *)
  | W of uid * wire_name * terms ref * 'a sat ref 
  | E
type relabelled
type unlabelled

module Sat : sig
  type t = unlabelled sat list
end

(* HardCaml API implemented using SAT clauses *)
module Comb : HardCaml.Comb.S with type t = unlabelled sat list

module M : Map.S with type key = int

val relabel : unlabelled sat -> relabelled sat

val nterms : 'a sat -> int

type name_map = (string * int) list M.t

val name_map : name_map -> relabelled sat -> (string * int) list M.t

val nvars : relabelled sat -> int

val fold : ('a -> terms -> 'a) -> 'a -> 'b sat -> 'a

(** convert a single bit signal to SAT *)
val convert : HardCaml.Signal.Comb.t -> relabelled sat

(** run SAT solver, parse and return results *)
val run : ?solver:string -> relabelled sat -> int list Sattools.Result.t

(** partition (sorted) list into sublists with equal predicates *)
val partition : ('a -> 'a -> bool) -> 'a list -> 'a list list

(** convert output of SAT tool to human readable format *)
val report : name_map -> int list Sattools.Result.t -> (string * string) list Sattools.Result.t

