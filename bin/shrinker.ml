open Exp
open Analysis
open Library
(*
I am using an integer to keep track of the variant produced by shrinking: 
-1 -> not shrunk
0 -> remove_uncalled_mutuals done
1+ -> that many local shrinker steps have already been performed
*)

(******************* PARAMETERS ********************)

let input_exp_f = ref ("")
let output_exp_f = ref ("")
let output_code_f = ref("")

let variant = ref(-1)
let lang = ref("")
let input = ref("")
let speclist =
[
  ("-input_exp_f", Arg.Set_string input_exp_f, "input_exp_f");
  ("-output_exp_f", Arg.Set_string output_exp_f, "output_exp_f");
  ("-output_code_f", Arg.Set_string output_code_f, "output_code_f");
  ("-variant", Arg.Set_int variant, "variant");
  ("-lang", Arg.Set_string lang, "lang");
  ("-input", Arg.Set_string input, "input");
]

let read_exps file: exp list = exps_of_str @@ In_channel.with_open_text file In_channel.input_lines 

let write_exps code_of_exps code_f exp_f es =
  (* print the sexp*)
  Out_channel.output_string (Out_channel.open_text exp_f) @@
    str_of_exps es;
  (* print the code in chosen language *)
  Out_channel.output_string (Out_channel.open_text code_f) @@
    (code_of_exps [es] !input)

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

  let langM = 
    match !lang with
    | "ml" -> Gen_ml.ml_ 
    | "rkt" -> Gen_racket.racket_
    | "sml" -> Gen_sml.sml_
    | _ -> raise (Util.Unimplemented "lang not supported") in
  let get_printer (module L : Language) = L.printer in

  let init_exps : exp list = read_exps !input_exp_f in

  let new_exps = 
    if !variant = -1 
    then Analysis.remove_uncalled_mutuals init_exps (* global shrinker steps *)
    else
      run_local_steps init_exps !variant [use_base_case] in 

  write_exps (get_printer langM) !output_code_f !output_exp_f new_exps 
