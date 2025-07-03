open Type

let (-->) ty_params ty_body = FlatTyArrow (ty_params, ty_body)
let tInt = FlatTyCons ("Int", [])
let tBool = FlatTyCons ("Bool", [])

let flat_std_lib = 
  [("true",    tBool);
   ("false",   tBool);
   ("Zero",    tInt);
   ("Succ",   [tInt] --> tInt);
   ("(+)",    [tInt; tInt] --> tInt);
   ("(-)",    [tInt; tInt] --> tInt);]

let () = 
  Debug.debug_mode := true;;
  let p = Generate.generate_fp (Generators.main flat_std_lib) 10 
    tInt
  in PrettyPrinter.pretty_print p;;
