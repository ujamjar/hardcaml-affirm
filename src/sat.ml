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
    val (--) : t -> string -> t
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
        let eq = (~: (a &: (~: b))) &: (~: ((~: a) &: b)) in (* ~: (a ^: b) *)
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

module Sat = struct

  open Tseitin

  type t = unlabelled sat list

  let uid = 
    let x = ref 0 in
    (fun () -> incr x; !x)

  let get_uid = function 
    | P(uid,_) -> uid 
    | C(uid,_,_) -> uid
    | W(uid,_,_,_) -> uid 
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
    Array.to_list @@ Array.init n (fun i -> W(uid(), ref [], ref [], ref E))

  let (<==) a b = 
    assert (width a = width b);
    List.iter2 
      (fun a b ->
        match a with
        | W(uid, names, t, r) -> begin
          t := bwire uid (get_uid b);
          r := b 
        end
        | _ -> failwith "not a wire") a b

  let name_bit s n b = 
    match s with 
    | W(_,names,_,_) -> begin names := (n,b) :: !names; s end
    | _ -> s

  let (--) s n = 
    let w = width s in
    List.mapi (fun i s -> name_bit s n (w-i-1)) s

end

module Comb : Comb.S with type t = unlabelled sat list = Comb.Make(Make(Sat))

module M = Map.Make(struct type t = int let compare = compare end) 

let relabel s = 
  let mk_uid = let uid = ref 0 in (fun () -> incr uid; !uid) in
  let rec relabel map s = 
    let open Sat in
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
    | W(uid, names, terms, arg) ->
      let map, arg = relabel map !arg in
      let map, uid, terms = relabel_terms map uid !terms in
      map, W(uid, names, ref terms, ref arg)
    | E -> map, E
  in
  snd @@ relabel M.empty s

let nterms s = 
  let rec count s = 
    let sum_terms t = List.length t in
    let sum_args a = List.fold_left (fun a b -> a + count b) 0 a in
    match s with
    | P (uid, terms) -> sum_terms terms
    | C (uid, terms, args) -> sum_terms terms + sum_args args
    | W (uid, _, terms, arg) -> sum_terms !terms + sum_args [!arg]
    | E -> 0
  in
  count s

let nvars s = Sat.get_uid s

type name_map = (string * int) list M.t

let rec name_map map s = 
  match s with
  | P(_ ) -> map
  | C(_, _, args) -> 
    List.fold_left (fun map arg -> name_map map arg) map args
  | W(uid, names, _, arg) ->
    let map = if !names <> [] then M.add uid !names map else map in
    name_map map !arg
  | E -> map

let rec fold f a = function 
  | P(_, terms) -> f a terms
  | C(_, terms, args) -> 
    let a = f a terms in
    List.fold_left (fun a t -> fold f a t) a args
  | W(_, _, terms, arg) -> 
    let a = f a !terms in
    fold f a !arg
  | E -> a

module T = HardCaml.Transform.MakePureCombTransform(Comb)

let convert s = 
  let open HardCaml.Signal.Comb in
  if width s <> 1 then failwith "expecting single bit property"
  else
    let cnf = List.hd (T.rewrite_signals T.transform [s]) in
    relabel (List.hd cnf) 

let run ?(solver="dimacs-mini") cnf = 
  let module S = (val Sattools.Libs.get_solver solver) in
  let s = S.create () in
  S.add_clause s [ nvars cnf ];
  fold (fun () -> List.iter (S.add_clause s)) () cnf;
  let model = S.solve_with_model s in
  S.destroy s;
  model

let partition eq l =
  let rec f n p l = 
    match l with
    | [] -> [p]
    | h :: tl when eq h n -> f n (h :: p) tl
    | h :: tl             -> p :: f h [] l
  in
  match l with
  | [] -> []
  | h :: _ -> f h [] l

let to_vec l = 
  let len = 1 + List.fold_left (fun m (_,n,_) -> max m n) 0 l in
  let name = function (n,_,_) :: _ -> n |  [] -> failwith "bad vector" in
  let rec find_bit b = function 
    | [] -> None 
    | (_,b',v) :: tl -> if b'=b then Some(v) else find_bit b tl 
  in
  let value = String.init len 
    (fun i -> 
      match find_bit (len-i-1) l with 
      | None -> '?' 
      | Some(1) -> '1' 
      | _ -> '0')
  in
  name l, value

let report map = function
  | `unsat -> `unsat
  | `sat x ->
    let x = List.filter (fun x -> M.mem (abs x) map) x in
    let x = List.sort compare @@ List.flatten @@ List.map 
      (fun x -> 
        let l = M.find (abs x) map in
        List.map (fun (n,b) -> (n, b, if x<0 then 0 else 1)) l) 
      x 
    in
    let x = List.map to_vec @@ partition (fun (n,_,_) (m,_,_) -> n=m) x in
    `sat x

