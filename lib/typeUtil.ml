open Type;;
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