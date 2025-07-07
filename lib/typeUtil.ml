open Exp;;

(*********************** TYPE COMPARISON ******************************)

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
  | FlatTyArrow (_, cod) -> is_same_ty target cod
  | _ -> false

(********************** CONSTRUCTORS **********************************)

(* NOTE: could be improved. these are cached in generators.main

Returns the std_lib form of *base* datatype constructors, or ones that require no
recursive arguments.
Example (TO TEST): [{ty=tInt;  constructors=["Zero", []; ("Succ", [tInt])]}] -> ["Zero", tyInt]
*)
let base_constructors_to_std_lib (cons : data_constructor_t) : (string * flat_ty) list = 
  List.fold_left
    (fun acc {ty=ty; constructors=constructors} -> 
      List.filter_map 
      (fun cc -> if List.is_empty (snd cc) then Some(fst cc, ty) else None)
      constructors
      @ acc)
    []
    cons

(* Same as base_constructors_to_std_lib, but for recursive constructors (eg Succ) *)
let recur_constructors_to_std_lib (cons : data_constructor_t) : (string * flat_ty) list = 
  List.fold_left
    (fun acc {ty=ty; constructors=constructors} -> 
      List.filter_map 
      (fun cc -> if List.is_empty (snd cc) then None else Some(fst cc, ty))
      constructors
      @ acc)
    []
    cons

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