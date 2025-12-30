open Exp;;

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


(*************************************)
(* replace generic datatype constructor names with their racket variants*)    
let rackety_renamer name = 
  match name with
  | "Zero" -> "0"
  | "Succ"  -> "add1"
  | "-" -> "nat-min"
  | _ -> name

let rackety_header = 
  "#lang racket\n
  (define nat-min
  (λ x
    (define y (apply - x))
    (if (negative? y) 0 y)))\n
  "

(*************************************)

(* shortcut to fresh variables *)
let fresh_var _ = new_var (TyVar("h", Inf))

let pprint_prog (ppf : out_channel) (prog : Exp.exp) (data_cons : Exp.data_constructors_t) 
                (trace : bool)
                : unit =
  (* let print_bnd_with_ty (x : Exp.var) (_ : int) (acc : string list) = (* with type annotations *)
    ("["^(x.var_name)^":"^Exp.show_size_ty x.var_ty^"]") :: acc
  in *)
  let print_bnd (x : Exp.var) (_ : int) (acc : string list) =
    x.var_name :: acc
  in
  let print_bnds = print_lst print_bnd [" "] in
  (*let traces : (var, var) Hashtbl.t = Hashtbl.create 5 in (* recursive function |-> trace argument *) *)
  let rec print_e (e : Exp.exp) (tab_i : int) (acc : string list): string list =
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
      "("::(print_e func tab_i1 args)
    | Letrec (func, params, body) -> (*  (letrec ([f (λ (params) body)]) f)  *)
      let tail = ")]) "::(func.var_name)::")"::acc in
      let prebody = if trace
        then "(hash-set! hsh "^func.var_name^" (add1 (hash-ref! hsh "^func.var_name^" 0)))\n" (* initialize & update the trip counter *)
        else "" in 
      let body = "\n"::prebody::(tab tab_i1)::(print_e body tab_i1 tail) in
      let lambda = "(letrec (["::(func.var_name)::" (λ "::"("::(print_bnds params tab_i (") ; LR : "::(show_size_ty func.var_ty)::body)) in
      lambda
    | NLetrec (func, params, func_body, let_body ) -> (*  Nested letrec := (letrec ([f (λ (params) e_func_body)]) e_let_body) *)
      let let_body_tail = ")]) "::(print_e let_body tab_i1 (")"::acc)) in
      let prebody = if trace
        then "(hash-set! hsh "^func.var_name^" (add1 (hash-ref! hsh "^func.var_name^" 0)))\n" (* initialize & update the trip counter *)
        else "" in 
      let body = "\n"::prebody::(tab tab_i1)::(print_e func_body tab_i1 let_body_tail) in
      let lambda = "(letrec (["::(func.var_name)::" (λ "::"("::(print_bnds params tab_i (") ; NLR : "::(show_size_ty func.var_ty)::body)) in
      lambda
    | ExtRef (name, _) ->
      rackety_renamer name :: acc
    | Case (e, ty, clauses) -> (* (match e [(D x ...) e_1)] ... ) *)
      (* if we can't assume that e is a variable, then we should store it in a variable to use later ... *)
      (* let head_var = fresh_var () in  *)
      let head_var = print_e e tab_i [] in
      let print_bnds vars = print_lst print_bnd [" "] vars tab_i1 in
      let constructors = TypeUtil.lookup_constructors data_cons ty in
      let str_clauses = List.fold_right2 (fun (vars, body) (cname, _) acc ->
        match cname with  (* special case for printing natural #s *)
        | "Zero" -> (* removes the parens around 0 *)
          let body_str = ("\n"^tab tab_i1)::(print_e body tab_i1 ("]"::acc)) in
          ("\n"^tab tab_i1)::("[0"::body_str)
        | "Succ" -> (* [(? positive?) (let ([var (sub1 head_var)]) body)] *)
          let body_str = ("\n"^tab tab_i1)::(print_e body tab_i1 (")]"::acc)) in
          ("\n"^tab tab_i1)::("[(? positive?) 
            (let ([" :: print_bnds vars (" (sub1 "::head_var@")])"
            ::body_str))
        | _ -> (* normal case *)
          let body_str = ("\n"^tab tab_i1)::(print_e body tab_i1 ("]"::acc)) in
          ("\n"^tab tab_i1)::("[("^(rackety_renamer cname)^" ")::(print_bnds vars (")"::body_str)))
        clauses
        constructors
        (")"::acc) in
      "(match " :: (print_e e tab_i str_clauses) in
    Printf.fprintf ppf "%s" (String.concat "" (print_e prog 0 []))
      

(* let extract_name (e : exp) =
  match e with 
  | Letrec f xs e1 -> TODO
  | _ -> raise (Util.Impossible "Printer cannot extract non-letrec") *)


let pretty_print (progs : Exp.exp list) (data_cons : Exp.data_constructors_t) : unit =
  print_string("\n");
  List.iter (fun prog -> pprint_prog stdout prog data_cons false) progs;
  print_string("\n")

(* trace = trace number of recursive calls in hashtable*)
let print_trace (progs : Exp.exp list) (data_cons : Exp.data_constructors_t) 
                (oc : out_channel) (input : string)
                : unit =
  print_string("\n");
  Printf.fprintf oc "%s" (rackety_header);
  Printf.fprintf oc "%s" ("(define hsh (make-hash))\n");
  Printf.fprintf oc "%s" ("(define res (\n");
  List.iter (fun prog -> pprint_prog oc prog data_cons true) progs;
  Printf.fprintf oc "%s" (" "^ input ^"))\n");
  Printf.fprintf oc "%s" ("\n(for ([(k v) hsh]) (printf \"~a ~a\n\" k v))\n") 