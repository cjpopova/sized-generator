open Exp

let (-->) ty_params ty_body = TyArrow (Some (SVar "i"), ty_params, ty_body) (* all constructors and std_lib are quantified over i*)
let tNat sexp = TyCons ("Nat", [], sexp)
let tBool = TyCons ("Bool", [], Inf)

let data_constructors : data_constructors_t = [
    ["true", [] --> tBool; 
     "false", [] --> tBool ];
    ["Zero", [] --> tNat (SHat(SVar "i"));
     "Succ", [tNat (SVar "i")] --> tNat (SHat(SVar "i"))]]

let std_lib = [
  "(+)",    [tNat (SVar "i"); tNat Inf] --> tNat Inf;
  "(-)",    [tNat (SVar "i"); tNat Inf] --> tNat (SVar "i");
  "idNat",  [tNat (SVar "i")] --> tNat (SVar "i"); (* not polymorphic*)
  "odd",    [tNat Inf] --> tBool;
  "even",   [tNat Inf] --> tBool;
  "(&&)",   [tBool; tBool] --> tBool;
  "(||)",   [tBool; tBool] --> tBool;
  "not",    [tBool] --> tBool;
  "(==)",   [tNat Inf; tNat Inf] --> tBool; (* not polymorphic*)
  ]
