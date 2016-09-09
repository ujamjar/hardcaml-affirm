val convert : HardCaml.Signal.Comb.t -> Sat.relabelled Sat.sat

val write : out_channel -> Sat.relabelled Sat.sat -> unit

type 'a result = [ `unsat | `sat of 'a ]

val run : ?solver:[`pico|`mini|`crypto] -> Sat.relabelled Sat.sat -> int list result 

val report : Sat.name_map -> int list result -> (string * string) list result

