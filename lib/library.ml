open Exp

let i = SVar "i"
let ihat = SHat i
let (-->) ty_params ty_body = TyArrow (Some i, ty_params, ty_body) (* all constructors and std_lib are quantified over i*)

let tBool = TyCons ("Bool", [], ihat) (* technically bools are unsized but this simplifies substitution *)
let tNat sexp = TyCons ("Nat", [], sexp)
let tList ty sexp = TyCons ("List", [ty], sexp)

let data_constructors : data_constructors_t = [
    ["true", [] --> tBool; 
     "false", [] --> tBool ];
    ["Zero", [] --> tNat ihat;
     "Succ", [tNat i] --> tNat ihat];
    (* ["Nil", [] --> tList (TVar "X") ihat; (* this X is unsized as a param *)
     "Cons" [TVar "X" Inf, tList (TVar "X") i] --> tList (tVar "X") ihat] this X is sized as a domain *)
    ]

let std_lib = [
  "(+)",    [tNat i; tNat Inf] --> tNat Inf;
  "(-)",    [tNat i; tNat Inf] --> tNat i;
  "idNat",  [tNat i] --> tNat i; (* not polymorphic*)
  "odd",    [tNat Inf] --> tBool;
  "even",   [tNat Inf] --> tBool;
  "(&&)",   [tBool; tBool] --> tBool;
  "(||)",   [tBool; tBool] --> tBool;
  "not",    [tBool] --> tBool;
  "(==)",   [tNat Inf; tNat Inf] --> tBool; (* not polymorphic*)
  "42",     tNat Inf; (* it is useful to have some large constants, because Succ consumes fuel*)
  "560",    tNat Inf;
  "1000000",tNat Inf;
  ]
