open Exp
open Library

let steps : generators_t = (Generators.main {std_lib = std_lib; data_cons = data_constructors})

(******************* LOOP **************************)

let generate_stlc (fuel : int) = 
  Generate.generate_fp 
    steps
    fuel (* target type: *)
    (* (TyArrow(Some (SVar "k"), [tNat (SVar "k"); tNat Inf], tNat (SVar "k"))) *)
    (* (TyArrow(Some (SVar "k"), [tNat (SVar "k"); tNat Inf], tNat Inf)) *)
    (* ([tBool] --> tBool) *)
    (* ([tList i (tNat Inf)] --> tList i (tNat Inf)) *)
    ([tList i (tNat Inf)] --> (tNat Inf)) (* this is a test of whether the generator can return the element of the list *)

let generate_batch fuel batch_size =
Seq.init batch_size
           (fun _ ->
             let p = generate_stlc fuel in
             Debug.run prerr_newline;
             Debug.run (fun () -> Printf.eprintf "==================");
             Debug.run prerr_newline;
             p);;

let () = 
  Debug.debug_mode := true;
  Printf.eprintf ("\n");
Seq.iter (fun e -> PrettyPrinter.pretty_print e data_constructors) (generate_batch 5 10)

