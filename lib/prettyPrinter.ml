
let tab =
  let tab_table = Hashtbl.create 10 in
  let () = Hashtbl.add tab_table 0 "" in
  let rec tab (i : int) : string =
    if i = 0
    then ""
    else match Hashtbl.find_opt tab_table i with
         | Some x -> x
         | None -> let old = tab(i-1) in
                   let t = old ^ "   " in
                   (Hashtbl.add tab_table i t; t) in
  tab

let rec print_lst (print : 'a -> int -> string list -> string list) (sep : string list) (zs : 'a list) (tab_i : int) (acc : string list) =
    match zs with
    | [] -> acc
    | z :: zs -> print z tab_i (sep @ (print_lst print sep zs tab_i acc))

let rec string_of_ty (ty : Exp.size_ty) =
  match ty with
  | Exp.TyCons(name, _, _) -> name
  | Exp.TyArrow(doms, cod) -> 
    "[" ^ List.fold_right (fun t acc -> string_of_ty t ^ acc) doms "" 
      ^ "] --> " ^ string_of_ty cod

let pprint_prog (ppf : Format.formatter) (prog : Exp.exp) (data_cons : Exp.data_constructor_t) : unit =
  let print_bnd (x : Exp.var) (_ : int) (acc : string list) =
    ("["^(x.var_name)^":"^string_of_ty x.var_ty^"]") :: acc
  in
  let print_bnds = print_lst print_bnd [" "] in
  let rec print_e (e : Exp.exp) (tab_i : int) (acc : string list) : string list =
    let tab_i1 = tab_i+1 in
    match e with
    (* | Hole -> "[~]" :: acc *)
    | Var x -> (x.var_name) :: acc
    | Lambda (params, body) ->
      let body = "\n"::(tab tab_i1)::(print_e body tab_i1 (")"::acc)) in
      let lambda = "(λ "::"("::(print_bnds params tab_i (")"::body)) in
      lambda
    | App (func, args) -> 
      let print_es = print_lst print_e ["\n";tab tab_i1] in
      let args = "\n"::(tab tab_i1)::(print_es args tab_i1 (")"::acc)) in
      "(call"::"\n"::(tab tab_i1)::(print_e func tab_i1 args)
    | Letrec (func, params, body) -> (*  (letrec ([f (λ (params) body)]) f)  *)
      let tail = ")]) "::(func.var_name)::")"::acc in
      let body = "\n"::(tab tab_i1)::(print_e body tab_i1 tail) in
      let lambda = "(letrec (["::(func.var_name)::" (λ "::"("::(print_bnds params tab_i (")"::body)) in
      lambda
    | ExtRef (name, _) ->
      name :: acc
    | Case (e, ty, clauses) -> (* (match e [(D x ...) e_1)] ... ) *)
      let print_bnds vars = print_lst print_bnd [" "] vars tab_i1 in
      let constructors = TypeUtil.lookup_constructors data_cons ty in
      let str_clauses = List.fold_right2 (fun (vars, body) (cname, _) acc ->
        let body_str = ("\n"^tab tab_i1)::(print_e body tab_i1 ("]"::acc)) in
        ("\n"^tab tab_i1)::("[("^cname)::(print_bnds vars (")"::body_str)))
        clauses
        constructors
        (")"::acc) in
      "(match " :: (print_e e tab_i str_clauses) in
    Format.fprintf ppf "%s" (String.concat "" (print_e prog 0 []))
      

let pretty_print (prog : Exp.exp) (data_cons : Exp.data_constructor_t) : unit =
  print_string("\n");
  pprint_prog Format.std_formatter prog data_cons;
  print_string("\n")
