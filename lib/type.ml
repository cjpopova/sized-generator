(* type tree datatype *)
type flat_ty =
  | FlatTyInt
  | FlatTyBool
  (* | FlatTyList of flat_ty *)
  | FlatTyArrow of (flat_ty list) * flat_ty
  (* | FlatTyVar of string *)
