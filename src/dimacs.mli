(** convert a single bit signal to SAT *)
val convert : HardCaml.Signal.Comb.t -> Sat.relabelled Sat.sat

(** write SAT to file *)
val write : out_channel -> Sat.relabelled Sat.sat -> unit

type 'a result = [ `unsat | `sat of 'a ]

val partition : ('a -> 'a -> bool) -> 'a list -> 'a list list

(** run SAT solver, parse and return results *)
val run : ?solver:[`pico|`mini|`crypto] -> Sat.relabelled Sat.sat -> int list result 

(** convert output of SAT tool to human readable format *)
val report : Sat.name_map -> int list result -> (string * string) list result

