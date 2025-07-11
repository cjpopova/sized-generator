open Exp
open Library

let steps : generators_t = (Generators.main {std_lib = std_lib; data_cons = data_constructors})

(******************* LOOP **************************)

let generate_stlc (fuel : int) = 
  Generate.generate_fp 
    steps
    fuel (* target type: *)
    (* ([tInt (SHat (SVar "k")); tInt Inf] --> tInt  (SVar "k")) *)
    (* above type isn't sound, so the generator should crash ... *)
    (tInt (SHat (SVar "K")))
    (* (tInt Inf) *)

let generate_batch fuel batch_size =
Seq.init batch_size
           (fun _ ->
             let p = generate_stlc fuel in
             Debug.run prerr_newline;
             p);;

let () = 
  Debug.debug_mode := true;
  Printf.eprintf ("\n");
Seq.iter (fun e -> PrettyPrinter.pretty_print e data_constructors) (generate_batch 5 1)

