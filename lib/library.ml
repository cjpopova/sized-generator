open Exp

let i = SVar "i"
let ihat = SHat i
let tX = TyVar("X",Inf)
let (-->) ty_params ty_body = TyArrow (Some i, ty_params, ty_body) (* all constructors and std_lib are quantified over i*)

let tBool = TyCons ("Bool", [], ihat) (* technically bools are unsized but this simplifies substitution *)
let tNat sexp = TyCons ("Nat", [], sexp)
let tList sexp ty = TyCons ("List", [ty], sexp)

let data_constructors : data_constructors_t = [
    ["true", [] --> tBool; 
     "false", [] --> tBool ];
    ["Zero", [] --> tNat ihat;
     "Succ", [tNat i] --> tNat ihat];
    ["Nil", [] --> tList ihat tX; 
     "Cons", [tX; tList i tX] --> tList ihat tX]
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
  "head"   ,[tList i tX] --> tX;
  "tail"   ,[tList i tX] --> tX;
  "take"   ,[tList i tX; tNat Inf] --> tList i tX;
  "list-ref",[tList i tX; tNat Inf] --> tX;
 

  (* higher order danger zone:
  map      ,[(tX --> tY), tList i tX] -->  tList i tY;
  foldr    ,N/A

  ; see page 29 of Barthe tutorial
  map : Π X Y. ∀ i .
    (X -> Y) ->
    List i X ->
    List i Y
  if we want to generate a function for map : X Inf --> Y Inf
  can we subtype with : ∀ j. X j --> Y j
  probably ... i don't see this violating soundness i think
  *)
  ]
