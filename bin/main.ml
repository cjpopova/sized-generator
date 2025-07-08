open Exp

(********************* LIBRARY *************************)
let (-->) ty_params ty_body = FlatTyArrow (ty_params, ty_body)
let tInt = FlatTyCons ("Int", [])
let tBool = FlatTyCons ("Bool", [])

let data_constructors : data_constructor_t = [
    {ty=tBool; constructors=[("true", []); ("false", [])]};
    {ty=tInt;  constructors=["Zero", []; ("Succ", [tInt])]}
  ]

let flat_std_lib = 
  [("(+)",    [tInt; tInt] --> tInt);
   ("(-)",    [tInt; tInt] --> tInt);]

let steps : generators_t = (Generators.main {std_lib = flat_std_lib; data_cons = data_constructors})

(******************* LOOP **************************)

let generate_stlc (size : int) = 
  Generate.generate_fp 
    steps
    size
    ([tInt] --> tInt)

let generate_batch exp_size batch_size =
Seq.init batch_size
           (fun _ ->
             let p = generate_stlc exp_size in
             Debug.run prerr_newline;
             p);;

let () = 
  Debug.debug_mode := true;;
Seq.iter (fun e -> PrettyPrinter.pretty_print e data_constructors) (generate_batch 5 1)

