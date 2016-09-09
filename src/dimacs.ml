open Printf

module T = HardCaml.Transform.MakePureCombTransform(Sat.Comb)

let convert s = 
  let open HardCaml.Signal.Comb in
  if width s <> 1 then failwith "expecting single bit property"
  else
    let cnf = List.hd (T.rewrite_signals T.transform [s]) in
    Sat.relabel (List.hd cnf) 

let write chan cnf = 
  let nvars = Sat.nvars cnf in
  let nterms = Sat.nterms cnf in
  fprintf chan "p cnf %i %i\n" nvars (nterms+1);
  fprintf chan "%i 0\n" nvars;
  let print_term t = List.iter (fprintf chan "%i ") t; fprintf chan "0\n" in
  let print_terms = List.iter print_term in
  Sat.fold (fun () -> print_terms) () cnf 


let solver_name solver = 
  match solver with
  | `crypto -> "cryptominisat4_simple"
  | `mini -> "minisat"
  | `pico -> "picosat"

let run_solver solver fin fout = 
  let solver_name = solver_name solver in
  match solver with 
  | `crypto -> 
    ignore @@ Unix.system(sprintf "%s --verb=0 %s > %s" solver_name fin fout)
  | `mini -> 
    ignore @@ Unix.system(sprintf "%s -verb=0 %s %s" solver_name fin fout)
  | `pico -> 
    ignore @@ Unix.system(sprintf "%s %s > %s" solver_name fin fout)

let with_out_file name fn = 
  let f = open_out name in
  let r = fn f in
  close_out f;
  r

(* read output file *)
let read_sat_result fout = 
  let f = open_in fout in
  let result = 
    match input_line f with
    | "SATISFIABLE" | "SAT" | "s SATISFIABLE" -> `sat
    | "UNSATISFIABLE" | "UNSAT" | "s UNSATISFIABLE" -> `unsat
    | _ -> failwith "DIMACS bad output"
    | exception _ -> failwith "DIMACS bad output"
  in
  if result = `sat then 
    let split_char sep str =
      let rec indices acc i =
        try
          let i = succ(String.index_from str i sep) in
          indices (i::acc) i
        with Not_found -> (String.length str + 1) :: acc
      in
      let is = indices [0] 0 in
      let rec aux acc = function
        | last::start::tl ->
            let w = String.sub str start (last-start-1) in
            aux (w::acc) (start::tl)
        | _ -> acc
      in
      aux [] is 
    in
    let rec read_result_lines () = 
      match input_line f with
      | _ as line -> begin
        let tokens = List.filter ((<>) "") @@ split_char ' ' line in
        match tokens with
        | "v" :: tl -> List.map int_of_string tl :: read_result_lines ()
        | _ as l -> List.map int_of_string l :: read_result_lines ()
      end
      | exception _ ->
        []
    in
    let res = List.flatten @@ read_result_lines () in
    let () = close_in f in
    `sat res
  else 
    let () = close_in f in
    `unsat

type 'a result = [ `unsat | `sat of 'a ]

let run ?(solver=`pico) cnf = 
  let fin = Filename.temp_file "sat_cnf_in" "hardcaml" in
  let fout = Filename.temp_file "sat_res_out" "hardcaml" in
  (* generate cfg file *)
  with_out_file fin (fun f -> write f cnf);
  (* run solver *)
  run_solver solver fin fout;
  (* parse result file *)
  let result = read_sat_result fout in
  (* delete the temporary files *)
  (try Unix.unlink fin with _ -> ());
  (try Unix.unlink fout with _ -> ());
  result

let partition l =
  let rec f n p l = 
    match l with
    | [] -> [p]
    | ((n',_,_) as p') :: tl when n=n' -> f n (p' :: p) tl
    | (n',_,_) :: tl                   -> p :: f n' [] l
  in
  match l with
  | [] -> []
  | (n,_,_) :: _ -> f n [] l

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
    let x = List.filter (fun x -> Sat.M.mem (abs x) map) x in
    let x = List.sort compare @@ List.flatten @@ List.map 
      (fun x -> 
        let l = Sat.M.find (abs x) map in
        List.map (fun (n,b) -> (n, b, if x<0 then 0 else 1)) l) 
      x 
    in
    let x = List.map to_vec @@ partition x in
    `sat x

