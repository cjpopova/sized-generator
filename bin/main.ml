open Exp
open Library

let steps : generators_t = (Generators.main {std_lib = std_lib; data_cons = data_constructors})

(******************* PARAMETERS ********************)

let generate_stlc (fuel : int) = 
  Generate.generate_fp 
    steps
    fuel (* target type: *)
    [(TyArrow(Q (SVar "k"), [tNat (SVar "k"); tNat Inf], tNat (SVar "k")))]
    (* (TyArrow(Some (SVar "k"), [tNat (SVar "k"); tNat Inf], tNat Inf)) *)
    (* ([tBool] --> tBool) *)
    (* ([tList i (tNat Inf)] --> tList i (tNat Inf)) *)
    (* ([tList i (tNat Inf); tList Inf (tNat Inf)] --> (tList Inf (tNat Inf)))  *)

let batch_size = 5
let fuel = 10
let mode="trace" (* "print" or "trace" *)
let debug_mode = false

(******************* LOOP  **************************)
let generate_batch fuel batch_size =
Seq.init batch_size
           (fun _ ->
             let p = generate_stlc fuel in
             Debug.run prerr_newline;
             Debug.run (fun () -> Printf.eprintf "==================");
             Debug.run prerr_newline;
             p);;

(************** TRACER SETUP *********************)
let outdir = "output/"
let subdir = outdir ^ string_of_int @@ int_of_float @@ Unix.time ()
let _ = if mode=="trace" then Sys.mkdir subdir 0o755 else ()
(* in lieu of generating inputs, we will supply default inputs to match the target type above. List = "(make-list 100 0)" *)
let input = "100 42"

(************** GENERATE *********************)
let () = Printf.printf "num tests: %d\n%!" batch_size (* flush *)
let () = 
  Debug.debug_mode := debug_mode;
  Printf.eprintf ("\n");
Seq.iteri (fun i e -> 
  if mode=="print" then
    PrettyPrinter.pretty_print e data_constructors (* print to stdout *)
  else
    let file = subdir ^ "/" ^ string_of_int i ^ ".rkt" in
    let oc = open_out file in
    PrettyPrinter.print_trace e data_constructors oc input; (* print to file *)
    let _ = close_out oc in
    let _ = () in
    Printf.printf "test %d\n%!" i; (*flush*)
    let _ = (Sys.command @@ "timeout 10s racket " ^ file) in ()
  )
  (generate_batch fuel batch_size)