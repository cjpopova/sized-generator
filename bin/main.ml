open Type

(* let (-->) ty_params ty_body = TyArrow (ty_params, ty_body)
let tInt = TyCons ("Int", [])
let tBool = TyCons ("Bool", [])

let sized_std_lib = 
  [("Zero",    tInt);
   ("Succ",   [tInt] --> tInt);
   ("(+)",    [tInt; tInt] --> tInt);
   ("(-)",    [tInt; tInt] --> tInt);] *)

let flat_std_lib = 
  [("Zero",    FlatTyInt);
   ("Succ",   FlatTyArrow([FlatTyInt], FlatTyInt))]

let () = 
  Debug.debug_mode := true;;
  let p = Generate.generate_fp (Generators.main flat_std_lib) 10 
    (* (FlatTyArrow ([Type.FlatTyInt], Type.FlatTyInt))  *)
    Type.FlatTyInt
  in PrettyPrinter.pretty_print p;;
