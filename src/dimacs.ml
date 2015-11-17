open Printf

module Comb_basic_gates = struct

  module B = HardCaml.Signal.Comb
  type t = B.t list

  let gnd = [B.gnd]
  let vdd = [B.vdd]

  let rec is_const c = function (* see through (assigned) wires *)
    | HardCaml.Signal.Types.Signal_const(_,c') -> c=c'
    | HardCaml.Signal.Types.Signal_wire(_,d) -> is_const c !d
    | _ -> false
  let rec is_vdd = is_const "1"
  let rec is_gnd = is_const "0"

  let empty = []
  let width = List.length

  let const s = 
    Array.init (String.length s) (fun i -> s.[i]) |> Array.to_list |> 
      List.map (function '0' -> B.gnd | _ -> B.vdd)

  let select s h l = 
    let rec f i = function
      | [] -> []
      | a::b ->
        if i>h then []
        else if i>=l then a::f (i+1) b 
        else f (i+1) b
    in
    List.rev (f 0 (List.rev s))

  (* utils *)
  let zero n = const (HardCaml.Utils.bstr_of_int n 0)
  let consti n x = const (HardCaml.Utils.bstr_of_int n x)
  let bits = List.map (fun x -> [x])
  let concat = List.concat
  let concat_e = List.concat
  let ue s = concat [ gnd; s ]
  let msb s = select s (width s - 1) (width s - 1)
  let rec repeat x n = if n=0 then empty else concat [x; repeat x (n-1)]
  let rec reduce f = function
    | [] -> failwith "empty"
    | [a] -> a
    | a::b::t -> reduce f (f a b :: t)

  let not_ x = 
    if is_vdd x then B.gnd else
    if is_gnd x then B.vdd else
    B.(~:) x
  let (~:) = List.map not_
  let (^:) = List.map2 (fun x y -> 
    if is_gnd x && is_gnd y then B.gnd else
    if is_vdd x && is_vdd y then B.gnd else
    if is_vdd x && is_gnd y then B.vdd else
    if is_gnd x && is_vdd y then B.vdd else
    if is_gnd x then y else
    if is_gnd y then x else
    if is_vdd x then not_ y else
    if is_vdd y then not_ x else
    B.(x ^: y))
  let (&:) = List.map2 (fun x y ->
    if is_gnd x || is_gnd y then B.gnd else
    if is_vdd x && is_vdd y then B.vdd else
    if is_vdd x then y else
    if is_vdd y then x else
    B.(x &: y))
  let (|:) = List.map2 (fun x y ->
    if is_vdd x || is_vdd y then B.vdd else
    if is_gnd x && is_gnd y then B.gnd else
    if is_gnd x then y else
    if is_gnd y then x else
    B.(x |: y))

  let add cin a b = 
    let ha a b = a ^: b, a &: b in
    let fa cin a b = 
      let s1,c1 = ha a b in
      let s,c2 = ha cin s1 in
      s, (c2 ^: c1)
    in
    let f a b (c,l) =
      let s,c = fa c a b in
      c,s::l
    in
    concat @@ snd @@ List.fold_right2 f (bits a) (bits b) (cin,[])

  let (+:) = add gnd
  let (-:) a b = add vdd a (~: b) 

  let (==:) a b = reduce (&:) (bits (~: (a ^: b)))
  let (<>:) a b = reduce (&:) (bits (a ^: b))

  let (<:) a b = msb ((ue a) -: (ue b))

  let mux sel vals =
    let last_elem = List.hd (List.rev vals) in
    Array.init (1 lsl (width sel))
      (fun i -> 
        let e = ((consti (width sel) i) ==: sel) in
        let v = try List.nth vals i with _ -> last_elem in
        let e = repeat e (width v) in
        e &: v) |> Array.to_list |> reduce (|:) 

  let ( *: ) a b = 
    let _,r = List.fold_left (fun (i,acc) b -> 
      let acc = concat_e [gnd; acc] in
      let a = concat_e [ gnd ; a ; repeat gnd i ] in
      i+1, (+:) acc ((&:) a (repeat b (width a)))
    ) (0,(zero (width a))) (List.rev (bits b)) in
    select r (width a + width b - 1) 0
  
  let ( *+ ) a b = 
    let last = (width b) - 1 in
    let _,r = List.fold_left (fun (i,acc) b -> 
      let acc = concat_e [msb acc; acc] in
      let a = concat_e [ msb a; a ; repeat gnd i ] in
      i+1, (if i = last then (-:) else (+:)) acc ((&:) a (repeat b (width a)))
    ) (0,(zero (width a))) (List.rev (bits b)) in
    select r (width a + width b - 1) 0

  let to_int x = B.concat x |> B.to_int
  let to_bstr x = B.concat x |> B.to_bstr
  let to_string x = B.concat x |> B.to_string
  let (--) a b = 
    let w = width a in
    List.mapi (fun i a -> B.(--) a (b ^ "_" ^ string_of_int (w-i-1))) a

  let wire n = Array.init n (fun _ -> B.wire 1) |> Array.to_list |> List.rev
  let (<==) = List.iter2 (fun a b -> B.(<==) a b)

end

module Comb = HardCaml.Comb.Make(Comb_basic_gates)

module Transform : HardCaml.Transform.TransformFn' with type t = HardCaml.Signal.Comb.t list
  = HardCaml.Transform.MakePureCombTransform(Comb)

let convert_signals signals = Transform.rewrite_signals Transform.transform signals

module Vars = HardCaml.Signal.Types.UidMap
type var = HardCaml.Signal.Types.uid
type clause = var list
type cnf = var list list

(* Tseitin transformation *)
let (~.) = Int64.neg

let bnot z x = [ [x; z]; [~. x; ~. z] ] 

let bor z x = 
  let sum = List.fold_right (fun x a -> x :: a) x [~. z] in
  List.fold_right (fun x a -> [~. x; z] :: a) x [sum]
let bor z x y = bor z [x;y]

let band z x =  
  let sum = List.fold_right (fun x a -> ~. x :: a) x [z] in
  List.fold_right (fun x a -> [x; ~. z] :: a) x [sum]
let band z x y = band z [x;y]

let bxor z a b = 
  [ [~. z; ~. a; ~. b]; [~. z; a; b]; [z; ~. a; b]; [z; a; ~. b] ]

type cnf_inputs = (string * (var option list)) list
type cnf_result = [ `cnf_true | `cnf_false | `cnf of cnf * cnf_inputs * int ]

let cnf_of_circuit circ = 
  let open HardCaml in 
  let open Signal.Types in
  let open Signal.Comb in
  let failwith s = failwith ("cnf_of_circuit: " ^ s) in


  (* output (proposition) from circuit *)
  let output = 
    match Circuit.outputs circ with
    | [o] -> if width o <> 1 then failwith "circuit output must be 1 bit wide"
             else o
    | _ -> failwith "circuit must have 1 output which is 1 bit wide"
  in
  (* inputs to circuit *)
  let inputs = Circuit.inputs circ in

  (* inputs and outputs of converted circuit *)
  let output' = List.hd (convert_signals [output]) in
  let inputs' = Circuit.inputs (Circuit.make "dimacs" output') in
  let inputs' = List.map (fun i -> List.hd (names i), uid i) inputs' in

  (* variable tracking *)
  let new_id = 
    let id = ref 0L in
    (fun () -> id := Int64.add !id 1L; !id) (* 1... *)
  in

  (* SAT clause generation *)
  let unop op signal (cnf,vars) = 
    (* operator arguments *)
    let a = List.nth (deps signal) 0 in
    (* find cnf ids *)
    let a = Vars.find (uid a) vars in
    (* output var id, add to mapping  *)
    let c = new_id () in
    let vars = Vars.add (uid signal) c vars in
    (* cnf clauses *)
    let cnf = List.fold_left (fun cnf term -> term::cnf) cnf (op c a) in
    cnf, vars
  in

  let binop op signal (cnf,vars) =
    (* operator arguments *)
    let a = List.nth (deps signal) 0 in
    let b = List.nth (deps signal) 1 in
    (* find cnf ids *)
    let a = Vars.find (uid a) vars in
    let b = Vars.find (uid b) vars in
    (* output var id, add to mapping  *)
    let c = new_id () in
    let vars = Vars.add (uid signal) c vars in
    (* cnf clauses *)
    let cnf = List.fold_left (fun cnf term -> term::cnf) cnf (op c a b) in
    cnf, vars
  in

  (* conversion *)
  match output' with
  | [Signal_wire(_, {contents=Signal_const(_, "1")})] -> `cnf_true
  | [Signal_wire(_, {contents=Signal_const(_, "0")})] -> `cnf_false
  | _ -> begin

    let cnf, vars = 
      Circuit.search
        Circuit.id
        (fun (cnf,vars) signal ->
          match signal with
          | Signal_empty -> (cnf,vars) (* skip *)
          | Signal_reg _ -> failwith "registers not supported"
          | Signal_mem _ -> failwith "memories not supported"
          | Signal_inst _ -> failwith "instantiations not supported"
          | Signal_const _ -> failwith "constants should have been compiled out"
          | Signal_op(_,op) -> begin
            match op with
            | Signal_and -> binop band signal (cnf, vars)
            | Signal_or -> binop bor signal (cnf, vars)
            | Signal_xor -> binop bxor signal (cnf, vars)
            | Signal_not -> unop bnot signal (cnf, vars)
            | Signal_cat -> failwith "concatenations should have been compiled out"
            | _ -> failwith "unsupported operator 'convert_circuit' first" 
          end
          | Signal_select(_,h,l) -> failwith "selects should have been compiled out"
          | Signal_wire(id,d) -> 
            if !d = empty then 
              (* an input *)
              (cnf, Vars.add (uid signal) (new_id()) vars)
            else
              (* look through the wire *)
              (cnf, Vars.add (uid signal) (Vars.find (uid !d) vars) vars)
        )
        ([], Vars.empty) output'
    in

    (* add final clause *)
    let final = Int64.sub (new_id ()) 1L in
    let cnf = [final]::cnf in

    (* mapping of cnf ids to inputs *)
    let inputs = 
      List.map 
        (fun i ->
          let n = List.hd (names i) in
          let w = width i in
          let tryfind n = 
            match Vars.find (List.assoc n inputs') vars with
            | exception _ -> None
            | x -> Some(x)
          in
          let ids = Array.init w (fun j -> tryfind (n ^ "_" ^ string_of_int j)) in
          n, List.rev @@ Array.to_list ids)
        inputs
    in

    `cnf(cnf, inputs, Int64.to_int final)
  
  end

module Minisat = struct

  type minisat_result = [ `unsat | `sat of int list ]

  let split_char sep str =
    let string_index_from i =
      try Some (String.index_from str i sep)
      with Not_found -> None
    in
    let rec aux i acc = match string_index_from i with
      | Some i' ->
          let w = String.sub str i (i' - i) in
          aux (succ i') (w::acc)
      | None ->
          let w = String.sub str i (String.length str - i) in
          List.rev (w::acc)
    in
    aux 0 []

  let read_output chan = 
    match input_line chan with
    | "UNSAT" -> `unsat
    | "SAT" ->
      let l = input_line chan in
      let l = split_char ' ' l |> List.map int_of_string in
      let l = List.rev l in
      assert (List.hd l = 0);
      `sat (List.tl l)
    | _ -> failwith "bad output file"

  let write_dimacs chan cnf nvars = 
    fprintf chan "p cnf %i %i\n" nvars (List.length cnf);
    List.iter 
      (fun t ->
        List.iter (fun t -> fprintf chan "%Li " t) t;
        fprintf chan "0\n") cnf

  let report chan inputs result = 
    let report inputs l = 
      fprintf chan "SAT\n";
      List.iter 
        (fun (n,vars) ->
          fprintf chan "%s : [" n;
          List.iter 
            (function None -> fprintf chan "?" 
                    | Some(id) -> 
                      let id = Int64.to_int id in
                      if List.mem id l then fprintf chan "1"
                      else if List.mem (- id) l then fprintf chan "0"
                      else fprintf chan "x") vars;
          fprintf chan "]\n") 
        inputs;
    in
    match inputs, result with
    | `cnf_false, _ | _, `unsat -> fprintf chan "UNSAT\n"
    | `cnf_true, _ -> fprintf chan "SAT (trivially)\n"
    | `cnf(_,inputs,_), `sat l -> report inputs l

  let run ?(v=false) dimacs out = function
    | `cnf_false -> `unsat (* trivially false *)
    | `cnf_true -> `sat [] (* trivially true *)
    | `cnf(cnf,_,nvars) ->
      let f = open_out dimacs in
      write_dimacs f cnf nvars;
      close_out f;
      let verb = if v then "" else " > /dev/null" in
      let _ = Unix.system ("minisat " ^ dimacs ^ " " ^ out ^ verb) in
      let f = open_in out in
      let o = read_output f in
      close_in f;
      o

end

