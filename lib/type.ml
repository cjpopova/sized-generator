(* type tree datatype *)
type flat_ty =
  | FlatTyInt
  | FlatTyBool
  (* | FlatTyList of flat_ty *)
  | FlatTyArrow of (flat_ty list) * flat_ty
  (* | FlatTyVar of string *)
[@@deriving show]

let rec is_same_ty tyl1 tyl2 =
  match (tyl1, tyl2) with
  | (FlatTyBool, FlatTyBool) -> true
  | (FlatTyInt, FlatTyInt) -> true
  | (FlatTyArrow (doms1, cod1), FlatTyArrow (doms2, cod2)) -> 
    List.length doms1 = List.length doms2
    && List.for_all2 is_same_ty doms1 doms2
    && is_same_ty cod1 cod2
  | (_, _) -> false

(*CJP: todo add subtyping*)