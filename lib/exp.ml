(* type tree datatype *)
type flat_ty =
  | FlatTyCons of string * (flat_ty list)
  | FlatTyArrow of (flat_ty list) * flat_ty
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

(***************************************************************************************************************)

type exp =
  (* | Hole of flat_ty * env *)
  | Var of var
  | Lambda of ((var list) * exp)
  | App of (exp * (exp list))
  | Letrec of (var * (var list) * exp) (*  (letrec ([f (λ (params) body)]) f)  *)
  | ExtRef of string * flat_ty
  | Case of exp * flat_ty * ((var list * exp) list) (* case e \tau of { (x ... -> e_1) ... } *)
[@@deriving show]

and var = {
  var_name : string;
  var_ty : flat_ty;
}
[@@deriving show]
and env = var list
[@@deriving show]

type data_info = { 
    ty : flat_ty; 
    constructors : (string * flat_ty list) list
    (* case be extended w/ size information, like whether it's sized or
    what its size variable is *)
}
[@@deriving show]

type data_constructor_t = data_info list

type library = {
    std_lib : (string * flat_ty) list;
    data_cons : data_constructor_t
}

type hole_info = {
    fuel : int;
    env : env;
    depth : int;
    ty : flat_ty
}

type rule_urn = (unit -> exp) Urn.t
and generate_t = hole_info -> exp
and generators_t = (generate_t -> hole_info -> rule_urn -> rule_urn) list

(**************************** EXP UTILS ********************************************)

let var_counter = ref 0
let reset_var_counter () = var_counter := 0
let new_var ty =
  let x = !var_counter in
  incr var_counter;
  { var_name = "x" ^ Int.to_string x;
    var_ty = ty;
  }
