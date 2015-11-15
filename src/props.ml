type atomic_proposition = HardCaml.Signal.Comb.t

let name s = 
  let open HardCaml.Signal.Types in
  "bool(" ^ (try List.hd (names s) with _ -> "_" ^ Int64.to_string (uid s)) ^ ")" 

module CTL_star = struct

  (* for reference; the type for CTL* *)

  type state = 
    | True | P of atomic_proposition | SAnd of state * state 
    | SNot of state | E of path | A of path 

  and path = 
    | S of state | PAnd of path * path | PNot of path 
    | X of path | U of path * path | F of path | G of path 

end

module CTL = struct

  type state = 
    | True 
    | P of atomic_proposition 
    | And of state * state 
    | Not of state 
    | E of path 
    | A of path 

  and path = X of state | U of state * state | F of state | G of state 

  let t = True
  let p ap = P ap
  let (&:) a b = And(a,b)
  let (~:) a = Not(a)
  let e p = E p
  let a p = A p

  let x p = X p
  let rec ax ?(n=1) s = if n=0 then s else a (X (ax ~n:(n-1) s))
  let rec ex ?(n=1) s = if n=0 then s else e (X (ex ~n:(n-1) s))
  let u a b = U(a,b)
  let au x y = a @@ u x y
  let eu x y = e @@ u x y
  let (--) = u
  let f s = F s
  let af s = a @@ f s
  let ef s = e @@ f s
  let g s = G s
  let ag s = a @@ g s
  let eg s = e @@ g s

  let rec to_string ?(name=name) = function
    | True -> "TRUE"
    | P ap -> name ap
    | And(a,b) -> "(" ^ to_string a ^ " & " ^ to_string b ^ ")"
    | Not(s) -> "(!" ^ to_string s ^ ")"
    | E(G(p)) -> "(EG " ^ to_string p ^ ")"
    | E(F(p)) -> "(EF " ^ to_string p ^ ")"
    | E(X(p)) -> "(EX " ^ to_string p ^ ")"
    | E(U(a,b)) -> "(E [" ^ to_string a ^ " U " ^ to_string b ^ "])"
    | A(G(p)) -> "(AG " ^ to_string p ^ ")"
    | A(F(p)) -> "(AF " ^ to_string p ^ ")"
    | A(X(p)) -> "(AX " ^ to_string p ^ ")"
    | A(U(a,b)) -> "(A [" ^ to_string a ^ " U " ^ to_string b ^ "])"

  let rec atomic_propositions = function
    | True -> []
    | P ap -> [ap]
    | And(a,b) -> atomic_propositions a @ atomic_propositions b
    | Not(s) -> atomic_propositions s
    | E(G(p)) -> atomic_propositions p
    | E(F(p)) -> atomic_propositions p
    | E(X(p)) -> atomic_propositions p
    | E(U(a,b)) -> atomic_propositions a @ atomic_propositions b
    | A(G(p)) -> atomic_propositions p
    | A(F(p)) -> atomic_propositions p
    | A(X(p)) -> atomic_propositions p
    | A(U(a,b)) -> atomic_propositions a @ atomic_propositions b

end

module LTL = struct

  type path = 
    | True 
    | P of atomic_proposition 
    | And of path * path 
    | Not of path 
    | X of path 
    | U of path * path 

  let t = True
  let p ap = P ap
  let (&:) a b = And(a,b)
  let (~:) a = Not(a)
  let rec x ?(n=1) s = if n=0 then s else X (x ~n:(n-1) s)
  let u a b = U(a,b)
  let (--) = u

  let f p = t -- p
  let g p = ~: (f (~: p))

  let rec to_string ?(name=name) p = 
    match p with
    | U(True,b) -> "(F " ^ to_string b ^ ")"
    | Not(U(True,Not(p))) -> "(G " ^ to_string p ^ ")"
    | True -> "TRUE"
    | P ap -> name ap
    | And(a,b) -> "(" ^ to_string a ^ " & " ^ to_string b ^ ")"
    | Not(a) -> "(!" ^ to_string a ^ ")"
    | X(p) -> "(X " ^ to_string p ^ ")"
    | U(a,b) -> "(" ^ to_string a ^ " U " ^ to_string b ^ ")"

  let rec atomic_propositions = function
    | True -> []
    | P ap -> [ap]
    | And(a,b) -> atomic_propositions a @ atomic_propositions b
    | Not(a) -> atomic_propositions a
    | X(p) -> atomic_propositions p
    | U(a,b) -> atomic_propositions a @ atomic_propositions b

end

