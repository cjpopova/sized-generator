
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

let pretty_print (prog : Exp.program) : unit =
  let print_bnd (x : Exp.var) (_ : int) (acc : string list) =
    (* TODO: type information *)
    (Exp.Var.to_string x) :: acc
  in
  let rec print_e (e : Exp.exp_label) (tab_i : int) (acc : string list) : string list =
    let tab_i1 = tab_i+1 in
    match (prog.get_exp e).exp with
    | Hole -> "[~]" :: acc
    | Var x -> (Exp.Var.to_string x) :: acc
    | ValInt i -> (Int.to_string i) :: acc
    | ValBool b -> (Bool.to_string b) :: acc
    (*| StdLibRef str -> str :: acc *)
    | Let (x, rhs, body) ->
      let body = "\n"::(tab tab_i)::"in"
                 ::"\n"::(tab tab_i1)::(print_e body tab_i1 acc) in
      let rhs = "\n"::(tab tab_i1)::(print_e rhs tab_i1 body) in
      let bnd = "let "::(print_bnd x tab_i (" = "::rhs)) in
      bnd 
    | Lambda (params, body) ->
      let print_bnds = print_lst print_bnd [" "] in
      let body = "\n"::(tab tab_i1)::(print_e body (tab_i+1) (")"::acc)) in
      let lambda = "(λ "::"("::(print_bnds params tab_i (")"::body)) in
      lambda
    | App (func, args) -> 
      let print_es = print_lst print_e ["\n";tab tab_i1] in
      let args = "\n"::(tab tab_i1)::(print_es args tab_i1 (")"::acc)) in
      "(call"::"\n"::(tab tab_i1)::(print_e func tab_i1 args)
    | Letrec (func, params, body) -> (*  (letrec ([f (λ (params) body)]) f)  *) (* TODO: this is probably off*)
      let print_bnds = print_lst print_bnd [" "] in
      let tail = ")]) "::(Exp.Var.to_string func)::")"::acc in
      let body = "\n"::(tab tab_i1)::(print_e body (tab_i+1) tail) in
      let lambda = "(letrec (["::(Exp.Var.to_string func)::" (λ "::"("::(print_bnds params tab_i (")"::body)) in
      lambda
      
  in
  print_string (String.concat "" (print_e prog.head 0 []));
  print_string("\n")
