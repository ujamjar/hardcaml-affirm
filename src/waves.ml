(* render a BMC sat trace as a waveform *)

module B = HardCaml.Bits.Comb.IntbitsList
module W = HardCamlWaveTerm.Wave.Make(HardCamlWaveTerm.Wave.Bits(B))
module Widget = HardCamlWaveLTerm.Widget.Make(B)(W)

let to_waves (k,data) = 
  W.{
    cfg = default;
    waves = Array.of_list @@
      Data("step", W.init (k+1) (fun i -> B.consti 32 i), U) ::
      List.map 
        (fun (name,data) -> 
           Data(name, W.init (Array.length data) (fun i -> B.const data.(i)), B)) 
        data
  }

let run = function
  | `unsat -> ()
  | `sat(k, data) -> Lwt_main.run @@ Widget.run @@ to_waves (k,data)

