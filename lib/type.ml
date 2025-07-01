(* type tree datatype *)
type flat_ty =
  | FlatTyInt
  | FlatTyBool
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
  (* | TyCons of string * (*size_ty list **) size_exp *) 
    (* generalization, where the ty list is parameter variables, like the type of a list (a la alphas from Barthe 2004 constructor schemes) *)
  | TNat of size_exp
  | TyArrow of size_ty list * size_ty
[@@deriving show]

(* NOTES
UNTYPED std_lib:
let tBool = TyCons ("Bool", [])
  True        TBool
  False       TBool
let tNat = TyCons ("Nat", [])
  O           tNat
  S           tNat --> tNat
let tBoolList = TyCons ("List", []) ; since we're instantiating this with bool, no variables necessary
  Nil         tBoolList
  Cons        TBool, TBoolList --> TBoolList
let tOrdinal = TyCons ("Ord", [])
  O           tOrd
  S           tOrd --> tOrd
  Lim         tNat, tOrd --> tOrd

AND NOW TYPED: // assume that all constructors have a single size variable <i>
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

(* move this to typeUtil.ml*)

(************************ SIZES ***********************************)

let rec substitute_size_exp (theta : size_exp) (i : string) (e : size_exp) : size_exp = 
  match theta with
  | Inf -> Inf
  | (SVar x) -> if x = i then e else (SVar x)
  | (SHat theta') -> (SHat (substitute_size_exp theta' i e))


