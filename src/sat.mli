type uid = int
type terms = int list list
type 'a sat = 
  (* tracking sat clauses *)
  | P of uid * terms
  | C of uid * terms * 'a sat list
  (* wires *)
  | W of uid * terms ref * 'a sat ref 
  | E
type relabelled
type unlabelled

module Sat : sig
  type t = unlabelled sat list
end

(* HardCaml API implemented using SAT clauses *)
module Comb : HardCaml.Comb.S with type t = unlabelled sat list

val relabel : unlabelled sat -> relabelled sat

val nterms : 'a sat -> int

val nvars : relabelled sat -> int

val fold : ('a -> terms -> 'a) -> 'a -> 'b sat -> 'a

