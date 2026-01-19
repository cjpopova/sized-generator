open Exp
open Library
(* open Analysis *)

(******************* PARAMETERS ********************)

let batch_size = ref 1
let fuel = ref 5
let seed = ref (-1)
let lang = ref ("ml") (* ml or rkt *)
let speclist =
[
  ("-n", Arg.Set_int batch_size, "Number of tests to generate");
  ("-size", Arg.Set_int fuel, "Size of each function");
  ("-seed", Arg.Set_int seed, "Random generator seed");
  ("-lang", Arg.Set_string lang, "Language (ml, rkt)");
  ("-test-type", Arg.Set_int Debug.test_type, "Test type"); (* see README *)
  ("-debug", Arg.Set Debug.debug_mode, "Enable debug mode");
]

(************** GENERATE *********************)
let () =
  Arg.parse speclist (fun _ -> ())
    "sized_generator [-n <1>] [-size <10>] [-seed <-1>] [-lang <ml>]";
  (if !seed < 0
   then Random.self_init ()
   else Random.init !seed);

   (* Language setup*)
  let langM = 
    match !lang with
    | "ml" -> Gen_ml.ml_ 
    | "rkt" -> Gen_racket.racket_
    | _ -> raise (Util.Unimplemented "lang not supported") in
  let get_data_constructors (module L : Language) = L.data_constructors in
  let get_std_lib (module L : Language) = L.std_lib in
  let get_printer (module L : Language) = L.printer in


  (* GENERATION *) 
  let steps : generators_t = (Generators.main {std_lib = get_std_lib langM; data_cons = get_data_constructors langM}) in

  let generate_stlc (fuel : int) : exp list = 
    Generate.generate_fp 
      steps
      fuel (* target type: *)
      [ nat_func1; nat_func1 ]
  in
  (* Assume `code` is the name of the function to call. Format the function call & inputs appropriately. Examples:
  ((code 100) 42)     rkt : int -> int -> _
  code [100; 42]      ml : int list -> _
  *)
  let input = "(code 10 42)" in
  let generate_batch fuel batch_size =
    Seq.init batch_size
              (fun _ ->
                let p = generate_stlc fuel in
                Debug.run prerr_newline;
                Debug.run (fun () -> Printf.eprintf "==================");
                Debug.run prerr_newline;
                p) in
  let fs = generate_batch !fuel !batch_size in
  
  print_endline (get_printer langM fs input);
