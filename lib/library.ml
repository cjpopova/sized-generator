open Exp

let (-->) ty_params ty_body = TyArrow (ty_params, ty_body)
let tNat sexp = TyCons ("Nat", [], sexp)
let tBool = TyCons ("Bool", [], Inf)

let data_constructors : data_constructor_t = [
    {ty=tBool; constructors=[("true", []); ("false", [])]};
    {ty=tNat (SHat(SVar "i"));  constructors=["Zero", []; ("Succ", [tNat (SVar "i")])]}
  ]  

let std_lib = 
  [("(+)",    [tNat (SVar "i"); tNat Inf] --> tNat Inf);
   ("(-)",    [tNat (SVar "i"); tNat Inf] --> tNat (SVar "i"));]
