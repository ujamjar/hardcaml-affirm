(* Convert to NuSMV word based design *)

open HardCaml
open Signal.Types
open Signal.Comb

type property = [ `LTL of Props.LTL.path | `CTL of Props.CTL.state ]
type circuit = HardCaml.Circuit.t * property list
type io = string -> unit

let make name outputs props = 

  let module S = Set.Make(struct
    open HardCaml.Signal.Types
    type t = signal
    let compare a b = compare (uid a) (uid b)
  end) in

  let props' = 
    List.fold_left 
      (fun set prop ->
        let ap = 
          match prop with
          | `LTL prop -> Props.LTL.atomic_propositions prop
          | `CTL prop -> Props.CTL.atomic_propositions prop
        in
        List.fold_left (fun set ap -> S.add ap set) set ap)
      S.empty props
  in

  let ap = S.elements props' in
  let outputs = 
    match ap with
    | [] -> outputs
    | _ -> (output "__the_atomic_propositions" @@ HardCaml.Signal.Comb.concat ap) :: outputs 
  in
  HardCaml.Circuit.make name outputs, props

let write os (circ, props) = 
  let inputs, outputs = Circuit.inputs circ, Circuit.outputs circ in
  let is_internal s = not (Circuit.is_input circ s) && 
                      not (Circuit.is_output circ s) && 
                      not (s = empty) in 
  let internal_signals = Circuit.filter is_internal outputs in
  let internal_signals, registers = List.partition 
    (function Signal_reg _ -> false | _ -> true) internal_signals 
  in
  let internal_signals, memories = List.partition
    (function Signal_mem _ -> false | _ -> true) internal_signals
  in
  (* simple naming *)
  let name s = try List.hd (names s) with _ -> "_" ^ Int64.to_string (uid s) in
  let word_spec s = "unsigned word [" ^ string_of_int (width s) ^ "]" in
  let const' w s = "0h" ^ string_of_int w ^ "_" ^ (Utils.hstr_of_bstr Utils.Unsigned s) in
  let const s = const' (width s) (const_value s) in
  let consti w i = const' w (Utils.bstr_of_int w i) in
  let sel s h l = name s ^ "[" ^ string_of_int h ^ ":" ^ string_of_int l ^ "]" in
  let define s x = os "DEFINE "; os (name s); os " := "; os x; os ";\n" in

  os ("MODULE main\n");

  os ("\n-- inputs\n");
  List.iter (fun s -> os ("VAR " ^ name s ^ " : " ^ word_spec s ^ ";\n")) inputs;

  os ("\n-- registers\n");
  List.iter (fun s -> os ("VAR " ^ name s ^ " : " ^ word_spec s ^ ";\n")) registers;

  (* os ("-- memories\n"); *)
  assert (memories = []);

  os ("\n-- combinatorial logic\n");
  let define s = 
    let dep = let deps = deps s in List.nth deps in
    let ndep n = name (dep n) in
    match s with
    | Signal_empty -> failwith "NuSMV - unexpected empty signal"
    | Signal_inst _ -> failwith "NuSMV - instantiation not supported"
    | Signal_reg _ | Signal_mem _ -> failwith "NuSMV error - reg or mem not expected here"
    | Signal_const _ -> define s (const s)
    | Signal_wire (_,rf) -> define s (name !rf)
    | Signal_select(_,h,l) -> define s (sel (dep 0) h l)
    | Signal_op(_,op) -> begin
      let op2 op s = ndep 0 ^ op ^ ndep 1 in
      let wrap s t = s ^ "(" ^ t ^ ")" in
      let signed, unsigned = wrap "signed", wrap "unsigned" in
      let bool, word1 = wrap "bool", wrap "word1" in
      let sop2 op s = unsigned @@ (signed (ndep 0)) ^ op ^ (signed (ndep 1)) in
      let comp op s = word1 (op2 "=" s) in
      let not_ s = "!" ^ name (dep 0) in 
      let cat s = String.concat "::" @@ List.map name (deps s) in
      let mux _ =
        os "DEFINE "; os (name s); os " := \n";
        os "  case\n";
        let sel,cases = List.hd (deps s), List.tl (deps s) in
        let nsel = name sel in
        let rec f n = function
          | [] -> ()
          | [a] -> os "    TRUE: "; os (name a); os ";\n"
          | h::t -> 
              let w = width (sel) in
              os "    "; os nsel; os "="; os (consti w n); os ": "; 
                os (name h); os ";\n"; 
              f (n+1) t
        in
        f 0 cases;
        os "  esac;\n";
      in
      match op with
      | Signal_add -> define s (op2 "+" s)
      | Signal_sub -> define s (op2 "-" s)
      | Signal_mulu -> define s (op2 "*" s)
      | Signal_muls -> define s (sop2 "*" s)
      | Signal_and -> define s (op2 "&" s)
      | Signal_or -> define s (op2 "|" s)
      | Signal_xor -> define s (op2 " xor " s)
      | Signal_eq -> define s (comp "=" s)
      | Signal_not -> define s (not_ s)
      | Signal_lt -> define s (comp "<" s)
      | Signal_cat -> define s (cat s)
      | Signal_mux -> mux s
    end
  in
  List.iter define internal_signals;

  os ("\n-- register updates\n");
  List.iter 
    (fun s -> 
      match s with 
      | Signal_reg(_, r) -> 
        let next s = 
          let din = List.hd (deps s) in
          let mux2 s t f = "(bool(" ^ s ^ ")?" ^ t ^ ":" ^ f ^ ")" in
          let mux2e s t f = 
            if s=empty || s=vdd then t 
            else if s=gnd then f 
            else mux2 (name s) t f
          in
          let mux2r s l t f = 
            if s=empty then f
            else if l=vdd then mux2 (name s) t f
            else if l=gnd then mux2 (name s) f t
            else failwith "NuSMV - register update conversion failed"
          in
          let nxt = mux2e r.reg_enable (name din) (name s) in
          let nxt = mux2r r.reg_clear r.reg_clear_level (name r.reg_clear_value) nxt in
          let nxt = mux2r r.reg_reset r.reg_reset_level (name r.reg_reset_value) nxt in
          nxt
        in
        let init s = 
          if r.reg_reset = empty then
            if r.reg_reset_value = empty then 
              consti (width s) 0 (* default to zero *)
            else
              const r.reg_reset_value (* treat as a default value *)
          else 
            const r.reg_reset_value 
        in
        os ("ASSIGN init("^name s^") := "^init s^";\n");
        os ("ASSIGN next("^name s^") := "^next s^";\n");
      | _ -> failwith "NuSMV - expecting a register")
    registers;

  os ("\n-- outputs\n");
  List.iter define outputs;

  os ("\n-- SPECS\n");
  List.iter 
    (function
      | `CTL p -> os ("CTLSPEC " ^ Props.CTL.to_string p ^ ";\n")
      | `LTL p -> os ("LTLSPEC " ^ Props.LTL.to_string p ^ ";\n"))
    props

