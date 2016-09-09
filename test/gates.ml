open HardCaml

module Make(S : sig
    type t
    val width : t -> int
    val const : string -> t
    val empty : t
    val select : t -> int -> int -> t
    val concat : t list -> t
    val wire : int -> t
    val (<==) : t -> t -> unit
    val (~:) : t -> t 
    val (&:) : t -> t -> t
    val (|:) : t -> t -> t
    val (^:) : t -> t -> t
end) =
struct
    include S

    (* utils *)
    let vdd = const "1"
    let gnd = const "0"
    let bits_lsb x = 
        let w = width x in
        Array.to_list (Array.init w (fun i -> select x i i))
    let bits_msb x = List.rev (bits_lsb x)
    let reduce_bits def op a = List.fold_left op def (bits_lsb a)
    let repeat s n = 
        if n <= 0 then empty
        else concat (Array.to_list (Array.init n (fun _ -> s)))
    let concat_e l = 
        let x = List.filter ((<>)empty) l in
        if x = [] then empty
        else concat x

    let ripple_carry_adder cin a b =
        let fa cin a b = 
            let sum = (a ^: b) ^: cin in
            let carry = (a &: b) |: (b &: cin) |: (cin &: a) in
            sum, carry
        in
        let a = bits_lsb a in
        let b = bits_lsb b in
        let sum,_ = List.fold_left2 (fun (sum_in,carry_in) a b -> 
            let sum,carry_out = fa carry_in a b in
            sum::sum_in, carry_out) ([],cin) a b
        in
        concat sum

    (** addition *)
    let (+:) a b = ripple_carry_adder gnd a b
    
    (** subtraction *)
    let (-:) a b = ripple_carry_adder vdd a (~: b) 
    
    (** unsigned multiplication *)
    let ( *: ) a b = 
        let _,r = List.fold_left (fun (i,acc) b -> 
            let acc = concat_e [gnd; acc] in
            let a = concat_e [ gnd ; a ; repeat gnd i ] in
            i+1, (+:) acc ((&:) a (repeat b (width a)))
        ) (0,(repeat gnd (width a))) (bits_lsb b) in
        r
    
    (** signed multiplication *)
    let ( *+ ) a b = 
        let last = (width b) - 1 in
        let msb x = select x (width x - 1) (width x -1 ) in
        let _,r = List.fold_left (fun (i,acc) b -> 
            let acc = concat_e [msb acc; acc] in
            let a = concat_e [ msb a; a ; repeat gnd i ] in
            i+1, (if i = last then (-:) else (+:)) acc ((&:) a (repeat b (width a)))
        ) (0,(repeat gnd (width a))) (bits_lsb b) in
        r

    (** equality *)
    let (==:) a b = 
        let eq = (~: (a &: (~: b))) &: (~: ((~: a) &: b)) in
        reduce_bits vdd (&:) eq
    
    (** less than *)
    let (<:) a b = 
        let w = width a in
        let a,b = concat [gnd;a], concat [gnd;b] in
        let d = a -: b in
        select d w w
    
    (** multiplexer *)
    let mux s d = 
        let mux2 sel a b = 
            assert (width sel = 1);
            let s = repeat sel (width a) in
            (s &: a) |: ((~: s) &: b) 
        in
        let d' = List.hd (List.rev d) in
        (* generate the 'n' input mux structure 'bottom-up'.
         * it works from the lsb of the select signal.  Pairs
         * from the data list are mux'd together and we recurse 
         * until the select is complete.  Proper 'default' handling 
         * is included with the '[a]' case in 'zip' *)
        let rec build s d = 
            match s with 
            | [] -> List.hd d
            | s::s' ->
                let rec zip l = 
                    match l with
                    | [] -> []
                    | [a] -> [mux2 s d' a] 
                    (* | [a] -> [a] simpler *)
                    | a::b::tl -> mux2 s b a :: zip tl
                in
                build s' (zip d)
        in
        build (bits_lsb s) d

  let (--) s n = s
  let to_bstr _ = failwith "to_bstr"
  let to_int _ = failwith "to_int"
  let to_string _ = failwith "to_string"

end

module Tseitin = struct

  let bfalse z = [ [ - z ] ]

  let btrue z = [ [ z ] ]

  let bnot z x = [ [x; z]; [- x; - z] ]
  
  let bwire z x = [ [ -z; x ]; [ z; -x ] ]

  let bnor z x = 
    let sum = List.fold_right (fun x a -> x :: a) x [z] in
    List.fold_right (fun x a -> [- x; - z] :: a) x [sum]

  let bor z x = 
    let sum = List.fold_right (fun x a -> x :: a) x [- z] in
    List.fold_right (fun x a -> [- x; z] :: a) x [sum]

  let bnand z x = 
    let sum = List.fold_right (fun x a -> - x :: a) x [- z] in
    List.fold_right (fun x a -> [x; z] :: a) x [sum]

  let band z x =  
    let sum = List.fold_right (fun x a -> - x :: a) x [z] in
    List.fold_right (fun x a -> [x; - z] :: a) x [sum]

  let bxor z a b = 
    [ [- z; - a; - b]; [- z; a; b]; [z; - a; b]; [z; a; - b] ]

end


module Sat' = struct

  open Tseitin

  type uid = int

  type t' = 
    (* tracking sat clauses *)
    | P of uid * (int list list)
    | C of uid * (int list list) * t' list
    (* wires *)
    | W of uid * (int list list) ref * t' ref 
    | E

  type t = t' list

  let uid = 
    let x = ref 0 in
    (fun () -> incr x; !x)

  let get_uid = function 
    | P(uid,_) -> uid 
    | C(uid,_,_) -> uid
    | W(uid,_,_) -> uid 
    | E -> failwith "uid of empty signal"

  let gnd = let uid = uid () in P(uid, bfalse uid)
  let vdd = let uid = uid () in P(uid, btrue uid)

  let width s = List.length s

  let const v = 
    let len = String.length v in
    let rec const b i = 
      if len = i then b 
      else 
        let x = match v.[i] with '0' -> gnd | '1' -> vdd | _ -> failwith "const" in
        const (x :: b) (i+1)
    in
    List.rev (const [] 0)

  let empty = []

  let select s h l = 
    let rec sel b i = 
      match b with
      | [] -> []
      | hd::tl -> 
        if i > h then []
        else if i >= l then hd :: sel tl (i+1)
        else sel tl (i+1)
    in
    List.rev (sel (List.rev s) 0)

  let concat l = List.concat l

  let bnot a =
    let uid = uid () in
    C(uid, bnot uid (get_uid a), [a])

  let (~:) = List.map bnot

  let bop2 op a b = 
    let uid = uid () in
    C(uid, op uid [get_uid a; get_uid b], [a;b])

  let (&:) = List.map2 (bop2 band)

  let (|:) = List.map2 (bop2 bor) 

  let bxor a b = 
    let uid = uid () in
    C(uid, bxor uid (get_uid a) (get_uid b), [a;b])

  let (^:) = List.map2 bxor 

  let wire n = 
    Array.to_list @@ Array.init n (fun i -> W(uid(), ref [], ref E))

  let (<==) a b = 
    assert (width a = width b);
    List.iter2 
      (fun a b ->
        match a with
        | W(uid, t, r) -> begin
          t := bwire uid (get_uid b);
          r := b 
        end
        | _ -> failwith "not a wire") a b

end

module Sat : Comb.S with type t = Sat'.t = Comb.Make(Make(Sat'))

open Printf 

module M = Map.Make(struct type t = int let compare = compare end) 
let relabel s = 
  let mk_uid = let uid = ref 0 in (fun () -> incr uid; !uid) in
  let rec relabel map s = 
    let open Sat' in
    let find map x = 
      try if x < 0 then - (M.find (-x) map) else M.find x map
      with _ -> failwith ("map: " ^ string_of_int x) in
    let relabel_terms map uid' terms = 
      let uid, map = 
        if M.mem uid' map then 
          find map uid', map
        else
          let uid = mk_uid () in
          let map = M.add uid' uid map in
          uid, map
      in
      map, uid, List.map (List.map (find map)) terms
    in
    match s with
    | P (uid, terms) -> 
      let map, uid, terms = relabel_terms map uid terms in
      map, P(uid, terms)
    | C (uid, terms, args) -> 
      let map, args = List.fold_left 
          (fun (map,args) x -> 
             let map, x = relabel map x in
             map, x::args) 
          (map,[]) args
      in
      let map, uid, terms = relabel_terms map uid terms in
      map, C(uid, terms, List.rev args)
    | W(uid, terms, arg) ->
      let map, arg = relabel map !arg in
      let map, uid, terms = relabel_terms map uid !terms in
      map, W(uid, ref terms, ref arg)
    | E -> map, E
  in
  snd @@ relabel M.empty s

let write_dimacs chan s = 
  let open Sat' in

  assert (Sat'.width s = 1);
  let s = List.hd s in
  
  let rec count s = 
    let sum_terms t = List.length t in
    let sum_args a = List.fold_left (fun a b -> a + count b) 0 a in
    match s with
    | P (uid, terms) -> sum_terms terms
    | C (uid, terms, args) -> sum_terms terms + sum_args args
    | W (uid, terms, arg) -> sum_terms !terms + sum_args [!arg]
    | E -> 0
  in

  let s = relabel s in
  let nvars = Sat'.get_uid s in
  let nterms = count s in

  fprintf chan "p cnf %i %i\n" nvars (nterms+1);
  let print_term t = List.iter (fprintf chan "%i ") t; fprintf chan "0\n" in
  let print_terms = List.iter print_term in
  print_term [nvars];
  let rec print s = 
    match s with
    | P(_, terms) -> print_terms terms
    | C(_, terms, args) -> (print_terms terms; List.iter print args)
    | W(_, terms, arg) -> (print_terms !terms; print !arg)
    | E -> ()
  in
  print s

module Test = struct

  open Sat

  let a, b = input "a" 1, input "b" 1
  let f a b c = (ue a +: ue b) ==:. c
  let x c = 
    let a = let x = wire 1 in x <== a; x in
    let w = wire 1 in
    w <== f a b c;
    w

  let run x = 

    let with_out_file n f = let x = open_out n in let y = f x in close_out x; y in
    let () = with_out_file "foo.cnf" @@ fun f -> write_dimacs f x in

    let status = Unix.system ("picosat foo.cnf") in

    match status with
    | Unix.WEXITED 10 -> eprintf "SAT\n"
    | Unix.WEXITED 20 -> eprintf "UNSAT\n"
    | _ -> eprintf "Invalid exit status\n"

  let () = 
    run (x 0);
    run (x 1);
    run (x 2);
    run (x 3)

end

