open Type;;

let rec is_same_ty tyl1 tyl2 = (* type-equal? *) (*CJP: todo add subtyping*)
  match (tyl1, tyl2) with
  | (FlatTyCons (name1, _), FlatTyCons (name2, _)) -> name1 = name2
  | (FlatTyArrow (doms1, cod1), FlatTyArrow (doms2, cod2)) -> 
    List.length doms1 = List.length doms2
    && List.for_all2 is_same_ty doms1 doms2
    && is_same_ty cod1 cod2
  | (_, _) -> false

(* is maybe a function type that produces target? TODO NOT higher order*)
let ty_produces (target : flat_ty) (maybe : flat_ty) =
  match maybe with
  | FlatTyArrow (doms, cod) -> if is_same_ty target cod then Some doms else None (*|| (ty_produces target cod) *)
  | _ -> None

(************************ SIZES ***********************************)
let rec substitute_size_exp (theta : size_exp) (i : string) (e : size_exp) : size_exp = 
  match theta with
  | Inf -> Inf
  | (SVar x) -> if x = i then e else (SVar x)
  | (SHat theta') -> (SHat (substitute_size_exp theta' i e))

(* std_lib type compatibility:
TyBool TyBool -> true
TyBool TyFun(_, TyBool) -> true
*)
(* let rec size_ty_compat (target : size_ty) (maybe : size_ty) =
  match (target, maybe) with
  | (TyCons(name1, _), TyCons(name2, _)) -> name1 = name2
  | (TyCons(_, _), TyArrow(_,ty2)) -> size_ty_compat target ty2
  (* todo: include higher order case where target is a function *)
  | (_, _) -> false *)