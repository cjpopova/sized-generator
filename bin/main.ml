open Exp
open Library

let steps : generators_t = (Generators.main {std_lib = std_lib; data_cons = data_constructors})

(******************* LOOP **************************)

let generate_stlc (fuel : int) = 
  Generate.generate_fp 
    steps
    fuel (* target type: *)
    (TyArrow(Q (SVar "k"), [tNat (SVar "k"); tNat Inf], tNat (SVar "k")))
    (* (TyArrow(Some (SVar "k"), [tNat (SVar "k"); tNat Inf], tNat Inf)) *)
    (* ([tBool] --> tBool) *)
    (* ([tList i (tNat Inf)] --> tList i (tNat Inf)) *)
    (* ([tList i (tNat Inf); tList Inf (tNat Inf)] --> (tList Inf (tNat Inf)))  *)

let generate_batch fuel batch_size =
Seq.init batch_size
           (fun _ ->
             let p = generate_stlc fuel in
             Debug.run prerr_newline;
             Debug.run (fun () -> Printf.eprintf "==================");
             Debug.run prerr_newline;
             p);;

(* tracing/file output setup *)
let outdir = "output/"
let subdir = outdir ^ string_of_int @@ int_of_float @@ Unix.time ()
let _ = Sys.mkdir subdir 0o755
(* in lieu of generating inputs, we will supply default inputs to match the target type above. List = "(make-list 100 0)" *)
let input = "100 42"
let batch_size = 100
let () = Printf.printf "num tests: %d\n%!" batch_size (* flush *)
  
(* generate! *)
let () = 
  Debug.debug_mode := false;
  Printf.eprintf ("\n");
Seq.iteri (fun i e -> 
  let file = subdir ^ "/" ^ string_of_int i ^ ".rkt" in
  let oc = open_out file in
  (* PrettyPrinter.pretty_print e data_constructors; print to stdout *)
  PrettyPrinter.print_trace e data_constructors oc input; (* print to file *)
  let _ = close_out oc in
  Printf.printf "test %d\n%!" i; (* flush *)
  let _ = (Sys.command @@ "timeout 10s racket " ^ file) in ()
  )
  (generate_batch 5 batch_size)