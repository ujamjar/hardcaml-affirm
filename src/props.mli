type atomic_proposition = HardCaml.Signal.Comb.t

val name : HardCaml.Signal.Types.signal -> string

module CTL : sig

  type state =
    | True
    | P of atomic_proposition
    | And of state * state
    | Not of state
    | E of path
    | A of path

  and path = X of state | U of state * state | F of state | G of state

  val t : state
  val p : atomic_proposition -> state
  val ( &: ) : state -> state -> state
  val ( ~: ) : state -> state
  val e : path -> state
  val a : path -> state
  val x : state -> path
  val ax : ?n:int -> state -> state
  val ex : ?n:int -> state -> state
  val u : state -> state -> path
  val au : state -> state -> state
  val eu : state -> state -> state
  val ( -- ) : state -> state -> path
  val f : state -> path
  val af : state -> state
  val ef : state -> state
  val g : state -> path
  val ag : state -> state
  val eg : state -> state

  val to_string : ?name:(atomic_proposition -> string) -> state -> string
  val atomic_propositions : state -> atomic_proposition list
end

module LTL : sig

  type path =
    | True
    | P of atomic_proposition
    | Pn of atomic_proposition
    | And of path * path
    | Or of path * path
    | Not of path
    | X of path
    | U of path * path
    | R of path * path
    | F of path 
    | G of path

  val vdd : path
  val gnd : path
  val p : atomic_proposition -> path
  val ( &: ) : path -> path -> path
  val ( |: ) : path -> path -> path
  val ( ~: ) : path -> path
  val ( ==>: ) : path -> path -> path
  val x : ?n:int -> path -> path
  val u : path -> path -> path
  val ( -- ) : path -> path -> path
  val r : path -> path -> path
  val f : path -> path
  val g : path -> path
  val w : path -> path -> path

  val to_string : ?name:(atomic_proposition -> string) -> path -> string
  val atomic_propositions : path -> atomic_proposition list
  val depth : path -> int
  val nnf : path -> path
  val limit_depth : int -> path -> path

end

