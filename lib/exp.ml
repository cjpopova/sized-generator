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
  | TyCons of string * (flat_ty list) * size_exp (* NOTE: parameter types are unsized *)
  | TyArrow of size_ty list * size_ty
[@@deriving show]

(***************************************************************************************************************)

type exp =
  (* | Hole of flat_ty * env *)
  | Var of var
  | Lambda of ((var list) * exp)
  | App of (exp * (exp list))
  | Letrec of (var * (var list) * exp) (*  (letrec ([f (λ (params) body)]) f)  *)
  | ExtRef of string * size_ty
  | Case of exp * size_ty * ((var list * exp) list) (* case e \tau of { (x ... -> e_1) ... } *)
[@@deriving show]

and var = {
  var_name : string;
  var_ty : size_ty;
}
[@@deriving show]
and env = var list
[@@deriving show]

type data_info = { 
    ty : size_ty; 
    constructors : (string * size_ty list) list
    (* case be extended w/ size information, like whether it's sized or
    what its size variable is *)
}
[@@deriving show]

type data_constructor_t = data_info list

type library = {
    std_lib : (string * size_ty) list;
    data_cons : data_constructor_t
}

type hole_info = {
    fuel : int;
    env : env;
    depth : int;
    ty : size_ty
}

type rule_urn = (unit -> exp) Urn.t
and generate_t = hole_info -> exp
and generators_t = (generate_t -> hole_info -> rule_urn -> rule_urn) list

(**************************** EXP UTILS ********************************************)

let var_counter = ref 0
let reset_var_counter () = var_counter := 0
let new_var (ty : size_ty) =
  let x = !var_counter in
  incr var_counter;
  { var_name = "x" ^ Int.to_string x;
    var_ty = ty;
  }

let s_var_counter = ref 0
let reset_s_var_counter () = s_var_counter := 0
let new_s_var _ =
  let x = !s_var_counter in
  incr s_var_counter;
  SVar ("x" ^ Int.to_string x)