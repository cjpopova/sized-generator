open Exp
open Library
(* open Analysis *)

(******************* PARAMETERS ********************)

let batch_size = ref 1
let fuel = ref 5
let seed = ref (-1)
let lang = ref ("ml")

let type_str = ref (Sexplib.Sexp.to_string (sexp_of_size_ty Library.nat_func1))
let input = ref ("(code 5 9)")

let speclist =
[
  ("-n", Arg.Set_int batch_size, "Number of tests to generate");
  ("-size", Arg.Set_int fuel, "Size of each function");
  ("-seed", Arg.Set_int seed, "Random generator seed");
  ("-lang", Arg.Set_string lang, "Language (ml, sml, rkt)");
  ("-test-type", Arg.Set_int Debug.test_type, "Test type (see README)");
  ("-type", Arg.Set_string type_str, "Type to generate");
  ("-input", Arg.Set_string input, "Call to code with inputs");
  ("-debug", Arg.Set Debug.debug_mode, "Enable debug mode");
  ("-disable-size-check", Arg.Clear Debug.check_sizes, "Disable size type checking");
]

(************** GENERATE *********************)
let () =
  Arg.parse speclist (fun _ -> ())
    "sized_generator [-n <1>] [-size <10>] [-seed <-1>] [-lang <ml>] [-test-type <0>] [-type <...>] [-input \"(code 5 9)\"]";
  (if !seed < 0
   then Random.self_init ()
   else Random.init !seed);

   let target_ty = size_ty_of_sexp (Sexplib.Sexp.of_string !type_str) in

   (* Language setup*)
  let langM = 
    match !lang with
    | "ml" -> Gen_ml.ml_ 
    | "rkt" -> Gen_racket.racket_
    | "sml" -> Gen_sml.sml_
    | _ -> raise (Util.Unimplemented "lang not supported") in
  let get_data_constructors (module L : Language) = L.data_constructors in
  let get_std_lib (module L : Language) = L.std_lib in
  let get_printer (module L : Language) = L.printer in


  (* GENERATION *) 
  let steps : generators_t = (Generators.main {std_lib = get_std_lib langM; data_cons = get_data_constructors langM}) in

  let generate_stlc (fuel : int) : exp list = 
    Generate.generate_fp 
      steps
      fuel 
      [ target_ty; target_ty ]
  in
  let generate_batch fuel batch_size =
    Seq.init batch_size
              (fun _ ->
                let p = generate_stlc fuel in
                Debug.run prerr_newline;
                Debug.run (fun () -> Printf.eprintf "==================");
                Debug.run prerr_newline;
                p) in
  let fs = generate_batch !fuel !batch_size in
  let fs_lst = List.of_seq fs in
  
  print_endline (get_printer langM fs_lst !input);
(* 
  Printf.printf "==================\n";
  let shrunk_lst = List.map Analysis.shrinker fs_lst in
  
  print_endline (get_printer langM shrunk_lst input); *)
