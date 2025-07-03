(* type tree datatype *)
type flat_ty =
  | FlatTyCons of string * (flat_ty list)
  (* | FlatTyList of flat_ty *)
  | FlatTyArrow of (flat_ty list) * flat_ty
  (* | FlatTyVar of string *)
[@@deriving show]

type size_exp = (* size algebra *)
  | Inf
  | SVar of string
  | SHat of size_exp
[@@deriving show]

type size_ty = (* sized types*)
  | TyCons of string * (flat_ty list) * size_exp
  (* generalization, where the ty list is parameter variables, like the type of a list (a la alphas from Barthe 2004 constructor schemes) *)
  | TyArrow of size_ty list * size_ty
[@@deriving show]

(* NOTES
Sized_ty_std_lib // assume that all constructors have a single size variable <i>
let tNat = TyCons ("Nat", [])
  O           tNat <Ihat>
  S           tNat <i> -s-> tNat <ihat>
let tBoolList = TyCons ("List", []) ; since we're instantiating this with bool, no variables necessary
  Nil         tBoolList <ihat>
  Cons        TBool <inf>, TBoolList <i> -s-> TBoolList <ihat>


--------------------------------------------------------------

substitute : sized_ty size_exp -> sized_ty
substitute (UBool, _) _ = (UBool, inf)
substitute (UNat, e1) e2 = (UNat, (substitute_size_exp e1 e2)
*)
