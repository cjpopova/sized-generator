open Exp

let (-->) ty_params ty_body = TyArrow (Some (SVar "i"), ty_params, ty_body) (* all constructors and std_lib are quantified over i*)
let tNat sexp = TyCons ("Nat", [], sexp)
let tBool = TyCons ("Bool", [], Inf)

let data_constructors : data_constructor_t = [
    {ty=tBool; constructors=[("true", []); ("false", [])]};
    {ty=tNat (SHat(SVar "i"));  constructors=["Zero", []; ("Succ", [tNat (SVar "i")])]}
  ]  

let std_lib = 
  [("(+)",    [tNat (SVar "i"); tNat Inf] --> tNat Inf);
   ("(-)",    [tNat (SVar "i"); tNat Inf] --> tNat (SVar "i"));]
