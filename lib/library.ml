open Exp

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
