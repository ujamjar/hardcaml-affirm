module Comb_basic_gates = struct

  (* combinatorial api representend with (&:), (|:), (~:) and (^:) which is
   * easy to convert to sat *)

  include HardCaml.Signal.Comb

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

end

module Comb = HardCaml.Comb.Make(Comb_basic_gates)

module Transform = HardCaml.Transform.MakeCombTransform(Comb)

let convert_circuit circ = HardCaml.Transform.rewrite_circuit Transform.transform circ



