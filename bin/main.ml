open Exp

let (-->) ty_params ty_body = FlatTyArrow (ty_params, ty_body)
let tInt = FlatTyCons ("Int", [])
let tBool = FlatTyCons ("Bool", [])

let data_constructors : data_constructor_t = [
    {ty=tBool; constructors=[("true", []); ("false", [])]};
    {ty=tInt;  constructors=["Zero", []; ("Succ", [tInt])]}
  ]

let flat_std_lib = 
  [("true",    tBool);
   ("false",   tBool);
   ("Zero",    tInt);
   ("Succ",   [tInt] --> tInt);
   (* TODO: above should be removed once we use data_constructors *)
   ("(+)",    [tInt; tInt] --> tInt);
   ("(-)",    [tInt; tInt] --> tInt);]

let () = 
  Debug.debug_mode := true;;
let p = Generate.generate_fp 
    (Generators.main {std_lib = flat_std_lib; data_cons = data_constructors})
    10 
    tInt
  in PrettyPrinter.pretty_print p;;
