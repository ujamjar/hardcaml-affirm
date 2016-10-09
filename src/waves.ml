(* render a BMC sat trace as a waveform *)

module B = HardCaml.Bits.Comb.IntbitsList
module W = HardCamlWaveTerm.Wave.Make(HardCamlWaveTerm.Wave.Bits(B))
module Widget = HardCamlWaveTerm.Widget.Make(B)(W)

let to_state3 str = 
  let open B in
  (const @@ String.map (function | '?' -> '1' | _ -> '0') str) @:
  (const @@ String.map (function | '?' -> '0' | x -> x) str)

let string_of_state3 v = 
  let open B in
  let x,y = split v in
  let x,y = bits x, bits y in
  String.concat "" @@ List.map2 (fun x y -> if to_int x = 1 then "?" else to_string y) x y

let to_waves (k,data) = 
  W.{
    cfg = default;
    waves = Array.of_list @@
      Data("step", W.init (k+1) (fun i -> B.consti 32 i), U) ::
      List.map 
        (fun (name,data) -> 
           Data(name, 
                W.init (Array.length data) 
                       (fun i -> to_state3 data.(i)), 
                F string_of_state3)) 
        data
  }

let run = function
  | `unsat -> ()
  | `sat(k, data) -> Lwt_main.run @@ Widget.run @@ to_waves (k,data)

