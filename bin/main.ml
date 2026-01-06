open Exp
open Library
(* open Analysis *)

(******************* PARAMETERS ********************)

let batch_size = ref 1
let fuel = ref 5
let seed = ref (-1)
let mode = ref (0) (* 0 for print; 1 for trace *)
let lang = ref ("ml") (* ml or rkt (same as file extension) *)
let speclist =
[
  ("-n", Arg.Set_int batch_size, "Number of tests to generate");
  ("-size", Arg.Set_int fuel, "Size of each function");
  ("-seed", Arg.Set_int seed, "Random generator seed");
  ("-print_or_trace", Arg.Set_int mode, "print or trace modes"); (* NOTE: cleanup*)
  ("-lang", Arg.Set_string lang, "Language");
  ("-debug", Arg.Set Debug.debug_mode, "Enable debug mode");
]


(************** TRACER SETUP *********************)
let outdir = "output/"
let subdir = outdir ^ string_of_int @@ int_of_float @@ Unix.time ()
(* in lieu of generating inputs, we will supply default inputs to match the target type above. List = "(make-list 100 0)" *)
let input = "[100; 42]"

(************** GENERATE *********************)
let () =
  Arg.parse speclist (fun _ -> ())
    "sized_generator [-n <1>] [-size <10>] [-seed <-1>] [-print_or_trace <0>] [-lang <ml>]";
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
  let get_compile_and_run (module L : Language) = L.compile_and_run in


  (* GENERATION *) 
  let steps : generators_t = (Generators.main {std_lib = get_std_lib langM; data_cons = get_data_constructors langM}) in

  let generate_stlc (fuel : int) : exp list = 
    Generate.generate_fp 
      steps
      fuel (* target type: *)
      (* [
        (TyArrow(Q (SVar "k"), [tNat (SVar "k"); tNat Inf], tNat (SVar "k"))); (* these need to use the same quantifier *)
        (TyArrow(Q (SVar "k"), [tNat (SVar "k"); tNat Inf], tNat (SVar "k"))) 
      ] *)
      [
        (TyArrow(Q (SVar "k"), [tList (SVar "k") (tNat Inf)], tList (SVar "k") (tNat Inf)));
        (TyArrow(Q (SVar "k"), [tList (SVar "k") (tNat Inf)], tList (SVar "k") (tNat Inf)))
      ]
      (* (TyArrow(Some (SVar "k"), [tNat (SVar "k"); tNat Inf], tNat Inf)) *)
      (* ([tBool] --> tBool) *)
      (* ([tList i (tNat Inf)] --> tList i (tNat Inf)) *)
      (* ([tList i (tNat Inf); tList Inf (tNat Inf)] --> (tList Inf (tNat Inf)))  *)
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
  

  if !mode == 0 then (* print*)
    (Printf.eprintf "num tests: %d\n%!" !batch_size;
    Seq.iter (fun (es : exp list) -> 
      (* print_endline "\n======================"; *)
      print_endline (get_printer langM es input);
      (* Printf.printf "mutual recursion analysis: ";  
      List.iter2 (fun count e -> 
      Printf.printf "[%s %d %d]" (func_var e).var_name count.self_calls count.mutual_calls) 
      (Analysis.analyze_num_mutual_calls es) es; *)
    )
    fs)
  else
    (Printf.printf "num tests: %d\n%!" !batch_size;
    Sys.mkdir subdir 0o755;
    Seq.iteri (fun i (e : exp list) -> 
      let file = subdir ^ "/m" ^ string_of_int i ^ "." ^ !lang in
      let oc = open_out file in
      Printf.fprintf oc "%s" (get_printer langM e  input);
      close_out oc;
      Printf.printf "test %d\n%!" i; (*flush*)
      let _ = Sys.command @@ (get_compile_and_run langM subdir file) in ())
    fs)