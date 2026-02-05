open Exp
open Analysis
(*

variant
-1 -> not shrunk
0 -> remove_uncalled_mutuals done
1+ -> that many local shrinker steps have already been performed
*)

(******************* PARAMETERS ********************)

let input_exp_f = ref ("")
let output_exp_f = ref ("")
let output_code_f = ref("")
let speclist =
[
  ("-input_exp_f", Arg.Set_string input_exp_f, "input_exp_f");
  ("-output_exp_f", Arg.Set_string output_exp_f, "output_exp_f");
  ("-output_code_f", Arg.Set_string output_code_f, "output_code_f");
]

(* assume header is of the form
(variant other text here ...)
*)
let variant_from_header str = 
  let contents = String.split_on_char ' ' str in
  int_of_string @@ String.sub (List.hd contents) 1 (String.length @@ List.hd contents) 


let read_exps file: exp list * int = 
  match In_channel.with_open_text file In_channel.input_lines with 
  | header :: exps -> List.map (fun estr -> exp_of_sexp (Sexplib.Sexp.of_string estr)) exps, variant_from_header header
  | _ -> raise (Util.Impossible (Format.sprintf "Could not read: %s" file))

let write_exps code_f exp_f es variant =
  Out_channel.output_string (Out_channel.open_text code_f) "hello"
  (* TODO: write to both files; add LANG info as a command line argument ...
  maybe variant should also be a command line argument althrough i dont know how else to return it...
  maybe you dont need to IG since the python wrapper can track it*)

(************* SHRINK **************)

(* consume up to n elements of the sequence and track how many were consumed *)
let rec drop_while (seq : 'a Seq.t) (n : int) = 
  match seq, n with
  | _, 0 -> seq, n
  | _ when Seq.is_empty seq -> seq, n
  | _ -> drop_while (Seq.drop 1 seq) (n-1)

let rec run_local_steps (es : exp list) (variant : int) (steps : (exp -> exp Seq.t) list) : exp list = 
  match steps with
  | [] -> raise (Util.Impossible "ran out of local shrinking steps")
  | step :: rsteps ->
    let shrinks = local_shrinker_wrapper step es in
    let shrinks, v = drop_while shrinks variant in
    match shrinks (), v with
    | Seq.Nil, 0 -> raise (Util.Impossible "ran out of local shrinking steps")
    | Seq.Cons (new_es, _), 0 -> new_es 
    | _, v -> run_local_steps es v rsteps


(************** MAIN *********************)
let () =
  Arg.parse speclist (fun _ -> ())
    "sized_generator";

  let init_exps, variant  = read_exps !input_exp_f in

  let new_exps = 
    if variant = -1 
    then Analysis.remove_uncalled_mutuals init_exps (* global shrinker steps *)
    else
      run_local_steps init_exps variant [use_base_case] in

  write_exps !output_code_f !output_exp_f new_exps @@ variant+1
