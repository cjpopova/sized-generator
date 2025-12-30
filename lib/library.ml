open Exp

let i = SVar "i"
let ihat = SHat i
let k = SVar "k"
let j = SVar "j"
let khat = SHat k
let jhat = SHat j
let tX = TyVar("X",Inf)
let tY = TyVar("Y",Inf)
let (-->) ty_params ty_body = TyArrow (Q i, ty_params, ty_body) (* all constructors and std_lib are quantified over i*)

let tBool = TyCons ("bool", [], ihat) (* technically bools are unsized but this simplifies substitution *)
let tNat sexp = TyCons ("int", [], sexp)
let tList sexp ty = TyCons ("list", [ty], sexp)


(* module type shared among language backends *)
module type Language = sig
    val data_constructors : data_constructors_t 
    val std_lib : (string * size_ty) list
    val printer : exp list -> string -> string
  end;;