[@@@ocaml.warning "-26-27-32-39"]
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

let end_txt = "out of shrinks" (* python driver looks for this string in stderr *)

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
  | [] -> raise (Util.Impossible end_txt) (* no steps remain *)
  | step :: rsteps ->
    let shrinks = local_shrinker_wrapper step es in
    let shrinks, v = drop_while shrinks variant in (* drop shrinks before the requested # *)
    match shrinks (), v with
    | Seq.Cons (new_es, _), 0 -> new_es (* we found the requested variant *)
    | _, v -> run_local_steps es v rsteps (* we have not yet found the variant, and must run more steps *)


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
      run_local_steps init_exps !variant [lambdify_functions; drop_let_binding; constify_let_binding; ] in (* use_base_case; drop_let_binding; constify_let_binding *)

  write_exps (get_printer langM) !output_code_f !output_exp_f new_exps

  (* Debugging*)
  (* print the filtered variations to files*)
  (* Seq.iteri (fun i es ->
    write_exps (get_printer langM) (!output_code_f ^ string_of_int i) (!output_exp_f ^ string_of_int i) es)
  @@ local_shrinker_wrapper lambdify_functions init_exps; *)

  (* print the OG code *)
  (* Out_channel.output_string (Out_channel.open_text @@ !input_exp_f ^ "code") @@
    ((get_printer langM) [init_exps] !input) *)

  (* print the first variation of the first exp*)
  (* print_endline (string_of_int @@ Seq.length @@ drop_let_binding @@ List.hd init_exps) *)

  (* print the UNFILTERED variations of the first exp to files*)
  (* Seq.iteri (fun i es ->
  write_exps (get_printer langM) (!output_code_f ^ string_of_int i) (!output_exp_f ^ string_of_int i) [es])
  @@ lambdify_functions @@ List.hd init_exps *)
