open Exp
open Library

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

(************** GENERATE *********************)
let () =
  Arg.parse speclist (fun _ -> ())
    "sized_generator [-n <1>] [-size <10>] [-seed <-1>] [-lang <ml>]";
  (* TODO: fix the strings above for args parsing *)

    

  (* let file = "example.txt" in
  let ic = open_in file in
  let line = input_line ic in
  let init_exp = exp_of_yojson (Yojson.Safe.from_string line) in
  close_in ic; *)

  (* TODO: if a shrinker choice fails, how do we backtrack & make a different choice?? *)
  (* let rec shrink(curr_exps) = 
    let new_exps = shrinker curr_exps in () *)



  
  (* generate initial exp by calling generate (hard coded for now) *)
  let batch_size = ref(1) in
  let fuel = ref (10) in
  let seed = ref (766704) in
  let lang = ref ("sml") in

  Random.init !seed;  

  let langM = 
    match !lang with
    | "ml" -> Gen_ml.ml_ 
    | "rkt" -> Gen_racket.racket_
    | "sml" -> Gen_sml.sml_
    | _ -> raise (Util.Unimplemented "lang not supported") in
  let get_data_constructors (module L : Language) = L.data_constructors in
  let get_std_lib (module L : Language) = L.std_lib in
  let get_printer (module L : Language) = L.printer in

  let steps : generators_t = (Generators.main {std_lib = get_std_lib langM; data_cons = get_data_constructors langM}) in
  let generate_stlc (fuel : int) : exp list = 
    Generate.generate_fp 
      steps
      fuel (* target type: *)
      [ nat_func1; nat_func1 ] in
  let input = "(code 5 9)" in
  let generate_batch fuel batch_size =
    Seq.init batch_size
              (fun _ ->
                let p = generate_stlc fuel in
                Debug.run prerr_newline;
                Debug.run (fun () -> Printf.eprintf "==================");
                Debug.run prerr_newline;
                p) in
  let fs = generate_batch !fuel !batch_size in
  (* let es = List.hd (List.of_seq fs) in *)
  print_endline (get_printer langM (List.of_seq fs) input);
  (* let new_exps = Analysis.shrinker es in
  print_endline (get_printer langM new_exps input); *)


