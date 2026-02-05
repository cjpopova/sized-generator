open Sexplib.Std

type size_exp = (* size algebra *)
  | Inf
  | SVar of string
  | SHat of size_exp
[@@deriving show, sexp_of, of_sexp]

type quantifier = 
  | Q of size_exp (* Quantified by SVar k: may be called with anything  *)
  | U of size_exp (* Unquantified by SVar k: may only be called with s $<= k where |_s_| = k (added to the environment of a recursive function for recursive calls)*)
[@@deriving show, sexp_of, of_sexp]

type size_ty = (* sized types*)
  | TyVar of string * size_exp (* INVARIANT: size_exp is Inf*)
  | TyCons of string * (size_ty list) * size_exp (* NOTE: parameter types are unsized/Inf *)
  | TyArrow of quantifier * size_ty list * size_ty
[@@deriving show, sexp_of, of_sexp]

(***** PRINTERS ******)
let rec show_size_exp sexp =
  match sexp with
  | Inf -> "Inf"
  | SVar v -> v
  | SHat e -> show_size_exp e ^ "^"
(* let pp_size_exp fmt sexp = Format.fprintf fmt "%s" (show_size_exp sexp) *)

let rec show_unsized_ty ty = 
  match ty with
  | TyVar (name, _) -> name
  | TyCons (name, _, _) -> name 
  | TyArrow(_, doms, cod) ->
     List.fold_right (fun ty acc -> show_unsized_ty ty ^ " -> " ^ acc) doms "" 
     ^ show_unsized_ty cod

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
(* let pp_size_ty fmt ty = Format.fprintf fmt "%s" (show_size_ty ty) *)

(***************************************************************************************************************)

type exp =
  (* | Hole of flat_ty * env *)
  | Var of var
  | App of (exp * (exp list))
  | Letrec of (var * (var list) * exp) (*  (funrec ([f (λ (params) body)]) f)  *)
  | Let of (var * exp * exp)
  | ExtRef of string * size_ty (* the size_ty isn't ever used *)
  | Case of exp * size_ty * ((var list * exp) list) (* case e \tau of { (x ... -> e_1) ... } *)
[@@deriving sexp_of, of_sexp]

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
    ty : size_ty;
    match_head_count : int list
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

(* SOME HELPERS FOR PRINTING *)
let is_func (t:size_ty) : bool = 
  match t with
  | TyArrow _ -> true
  | _ -> false

let func_var (e:exp) : var = 
  match e with
  | Letrec (name, _, _) -> name
  | _ -> raise (Util.Impossible "func_var: bad exp")

let first_func_name (es: exp list) =
  (match (List.hd es) with | Letrec (func, _, _) -> func | _ -> raise (Util.Impossible "first_func_name: bad exp given")).var_name

(* defining sets for size_tys requires creating an ordering function *)
module SizeTyOrdered = struct
  type t = size_ty
  let compare x1 x2 = compare x1 x2
end
module SizeTySet = Set.Make(SizeTyOrdered)

(* ─( 16:56:37 )─< command 0 >────────────────────────────────────────────────────────────────────────────────{ counter: 0 }─
utop # open Exp;;
─( 16:56:37 )─< command 1 >────────────────────────────────────────────────────────────────────────────────{ counter: 0 }─
utop # let mys = SizeTySet.of_list [TyVar("X",Inf); TyVar("X",Inf)];;
val mys : SizeTySet.t = <abstr>
─( 16:57:16 )─< command 2 >────────────────────────────────────────────────────────────────────────────────{ counter: 0 }─
utop # SizeTySet.to_list mys;;
- : size_ty list = [TyVar ("X", Inf)]
─( 16:57:51 )─< command 3 >────────────────────────────────────────────────────────────────────────────────{ counter: 0 }─
utop #  *)