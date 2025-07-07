
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

let pprint_prog (ppf : Format.formatter) (prog : Exp.exp) : unit =
  let print_bnd (x : Exp.var) (_ : int) (acc : string list) =
    (* TODO: type information *)
    (x.var_name) :: acc
  in
  let rec print_e (e : Exp.exp) (tab_i : int) (acc : string list) : string list =
    let tab_i1 = tab_i+1 in
    match e with
    (* | Hole -> "[~]" :: acc *)
    | Var x -> (x.var_name) :: acc
    | Lambda (params, body) ->
      let print_bnds = print_lst print_bnd [" "] in
      let body = "\n"::(tab tab_i1)::(print_e body (tab_i+1) (")"::acc)) in
      let lambda = "(λ "::"("::(print_bnds params tab_i (")"::body)) in
      lambda
    | App (func, args) -> 
      let print_es = print_lst print_e ["\n";tab tab_i1] in
      let args = "\n"::(tab tab_i1)::(print_es args tab_i1 (")"::acc)) in
      "(call"::"\n"::(tab tab_i1)::(print_e func tab_i1 args)
    | Letrec (func, params, body) -> (*  (letrec ([f (λ (params) body)]) f)  *)
      let print_bnds = print_lst print_bnd [" "] in
      let tail = ")]) "::(func.var_name)::")"::acc in
      let body = "\n"::(tab tab_i1)::(print_e body (tab_i+1) tail) in
      let lambda = "(letrec (["::(func.var_name)::" (λ "::"("::(print_bnds params tab_i (")"::body)) in
      lambda
    | ExtRef (name, _) ->
      name :: acc
    | Case (e, _, clauses) -> (* (match e [(D x ...) e_1)] ... ) *)
      let print_bnds vars = print_lst print_bnd [" "] vars (tab_i+1) in
      let str_clauses = List.fold_right (fun (vars, e) acc ->
        let e_str = print_e e (tab_i+1) ("]"::acc) in
        "[("::(print_bnds vars (")"::e_str)))
        clauses
        (")"::acc) in
      "(match " :: (print_e e tab_i (" "::str_clauses)) in
    Format.fprintf ppf "%s" (String.concat "" (print_e prog 0 []))
      

let pretty_print (prog : Exp.exp) : unit =
  print_string("\n");
  pprint_prog Format.std_formatter prog;
  print_string("\n")
