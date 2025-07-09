open Exp

(********************* LIBRARY *************************)
let (-->) ty_params ty_body = TyArrow (ty_params, ty_body)
let tInt sexp = TyCons ("Int", [], sexp)
let tBool = TyCons ("Bool", [], Inf)

let data_constructors : data_constructor_t = [
    {ty=tBool; constructors=[("true", []); ("false", [])]};
    {ty=tInt (SHat(SVar "i"));  constructors=["Zero", []; ("Succ", [tInt (SVar "i")])]}
  ]  

let std_lib = 
  [("(+)",    [tInt (SVar "i"); tInt Inf] --> tInt Inf);
   ("(-)",    [tInt (SVar "i"); tInt Inf] --> tInt (SVar "i"));]

let steps : generators_t = (Generators.main {std_lib = std_lib; data_cons = data_constructors})

(******************* LOOP **************************)

let generate_stlc (size : int) = 
  Generate.generate_fp 
    steps
    size
    ([tInt (SVar "i"); tInt Inf] --> tInt Inf)

let generate_batch exp_size batch_size =
Seq.init batch_size
           (fun _ ->
             let p = generate_stlc exp_size in
             Debug.run prerr_newline;
             p);;

let () = 
  Debug.debug_mode := true;;
Seq.iter (fun e -> PrettyPrinter.pretty_print e data_constructors) (generate_batch 5 1)

