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

let run ?(solver="picosat") ?(verbose=false) cnf = 
  let n = Filename.temp_file "cnf" "hardcaml" in
  let f = open_out n in
  write f cnf;
  close_out f;
  let status = Unix.system (solver ^ " " ^ n ^ (if verbose then "" else " > /dev/null")) in
  Unix.unlink n;
  match status with
  | Unix.WEXITED 10 -> true
  | Unix.WEXITED 20 -> false
  | _ -> failwith "bad exit code"

