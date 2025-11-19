type size_exp = (* size algebra *)
  | Inf
  | SVar of string
  | SHat of size_exp

type quantifier = 
  | Q of size_exp (* Quantified by SVar k: may be called with anything  *)
  | U of size_exp (* Unquantified by SVar k: may only be called with s $<= k where |_s_| = k (added to the environment of a recursive function for recursive calls)*)

type size_ty = (* sized types*)
  | TyVar of string * size_exp (* INVARIANT: size_exp is Inf*)
  | TyCons of string * (size_ty list) * size_exp (* NOTE: parameter types are unsized/Inf *)
  | TyArrow of quantifier * size_ty list * size_ty

(***** PRINTERS ******)
let rec show_size_exp sexp =
  match sexp with
  | Inf -> "Inf"
  | SVar v -> v
  | SHat e -> show_size_exp e ^ "^"
let pp_size_exp fmt sexp = Format.fprintf fmt "%s" (show_size_exp sexp)

let rec show_size_ty ty = 
  match ty with
  | TyVar (name, sexp) -> name ^ " " ^ show_size_exp sexp
  | TyCons (name, params, sexp) -> name ^ " " ^ show_size_exp sexp ^ 
    if List.is_empty params then "" else " (" ^ show_size_ty (List.hd params) ^ ")"
  | TyArrow(quant, doms, cod) ->
     (match quant with 
     | Q e -> "∀"^(show_size_exp e)^"."
     | U _ -> "")
     ^
     List.fold_right (fun ty acc -> show_size_ty ty ^ " -> " ^ acc) doms "" 
     ^ show_size_ty cod
let pp_size_ty fmt ty = Format.fprintf fmt "%s" (show_size_ty ty)

(***************************************************************************************************************)

type exp =
  (* | Hole of flat_ty * env *)
  | Var of var
  | Lambda of ((var list) * exp)
  | App of (exp * (exp list))
  | Letrec of (var * (var list) * exp) (*  (letrec ([f (λ (params) body)]) f)  *)
  | NLetrec of (var * (var list) * exp * exp) (*  Nested letrec := (letrec ([f (λ (params) e_func_body)]) e_let_body)  *)
  | ExtRef of string * size_ty (* the size_ty isn't ever used *)
  | Case of exp * size_ty * ((var list * exp) list) (* case e \tau of { (x ... -> e_1) ... } *)
(* [@@deriving show] *)

and var = {
  var_name : string;
  var_ty : size_ty;
}
[@@deriving show]
and env = var list
[@@deriving show]


type func_list = (string * size_ty) list
[@@deriving show]
type data_constructors_t = func_list list
type library = {
    std_lib : (string * size_ty) list;
    data_cons : data_constructors_t
}


type hole_info = {
    fuel : int;
    env : env;
    depth : int;
    ty : size_ty
}
[@@deriving show]

type rule_urn = (unit -> exp) Urn.t
and generate_t = hole_info -> exp
and generators_t = (generate_t -> hole_info -> rule_urn -> rule_urn) list

(**************************** EXP UTILS ********************************************)

let var_counter = ref 0
let reset_var_counter () = var_counter := 0
let new_var ?(prefix="x") (ty : size_ty)  =
  let x = !var_counter in
  incr var_counter;
  { var_name = prefix ^ Int.to_string x;
    var_ty = ty;
  }

let s_var_counter = ref 0
let reset_s_var_counter () = s_var_counter := 0
let new_s_var _ =
  let x = !s_var_counter in
  incr s_var_counter;
  SVar ("i" ^ Int.to_string x)

let is_mutual_var (_ : var) = false (* TODO cheat & use prefix to determine if v is a preallocated var*)