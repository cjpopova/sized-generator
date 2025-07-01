open Type;;

let rec is_same_ty tyl1 tyl2 = (* type-equal? *) (*CJP: todo add subtyping*)
  match (tyl1, tyl2) with
  | (FlatTyBool, FlatTyBool) -> true
  | (FlatTyInt, FlatTyInt) -> true
  | (FlatTyArrow (doms1, cod1), FlatTyArrow (doms2, cod2)) -> 
    List.length doms1 = List.length doms2
    && List.for_all2 is_same_ty doms1 doms2
    && is_same_ty cod1 cod2
  | (_, _) -> false
  
let rec random_type size (prog : Exp.program) =
  (Choose.choose_frequency
      [(8, (fun _ -> FlatTyBool));
        (12, (fun _ -> FlatTyInt));
        (* (size / 4, (fun _ -> TyList (random_type (size / 2) prog))); *)
        (size / 4, (fun _ ->
                      let n = (Random.int 3) + 1 in
                      let tys = List.init n (fun _ -> random_type (size / (2 * n)) prog) in
                      FlatTyArrow (tys, (random_type (size / 2) prog))))])
  ()