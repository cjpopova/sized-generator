open Exp
(* open Library *)
(* Static analysis on exps *)

type counters = { self_calls: int; mutual_calls: int }
let empty_counter _ = {self_calls = 0; mutual_calls=0}
let add_counters c1 c2 = {self_calls = c1.self_calls + c2.self_calls; mutual_calls=c1.mutual_calls + c2.mutual_calls}

(* list of how many times ith function statically calls other mutually recursive functions (not including itself) *)
let analyze_num_mutual_calls (es : exp list) : counters list = 
  (* get vars of top level functions *)
  let mutuals = List.map func_var es in

  let rec traverse_ast (e:exp) (self_name:var) : counters = 
    match e with 
    | Var _ -> empty_counter ()
    | App (func, args) -> 
      add_counters
      (match func with
      | Var v when v=self_name -> {self_calls = 1; mutual_calls=0}
      | Var v when List.mem v mutuals -> {self_calls=0; mutual_calls=1}
      | _ -> traverse_ast func self_name)
      (List.fold_left (fun acc e -> add_counters acc (traverse_ast e self_name)) (empty_counter ()) args)
    | Letrec (_, _, body) -> traverse_ast body self_name
    | Let (_, v, let_body) -> 
      add_counters (traverse_ast v self_name) (traverse_ast let_body self_name)
    | ExtRef (_, _) -> empty_counter ()
    | Case (_, _, clauses) -> List.fold_left (fun acc (_, body)-> add_counters acc (traverse_ast body self_name)) (empty_counter ()) clauses
    in

  List.map2 traverse_ast es mutuals

let print_count_lst (cc : counters list) =
  List.iter (fun (c : counters) -> 
    Printf.eprintf "%d,%d\n" c.self_calls c.mutual_calls) 
    cc

(* shrinker transformations
- remove m2 if it is not called by m1
- remove (mutual) recursive call & replace with placeholder
- shrink constants to 0
- remove match branches
- replace let-bindings with constants (eg (let x=e1 in e2) become (let x=1 in e2))
- remove unused let binding
- replace (match e1 with |c1 -> e2 | c2 -> e3) with e2 (should have no free variables)
*)

(* remove m0 if it is not called by m1, etc *)
let remove_uncalled_mutuals es : exp list = 
  let counter_lst = analyze_num_mutual_calls es in
  (* print_count_lst counter_lst; *)
  let filtered_es = List.fold_left2 (fun called_es e { self_calls=_; mutual_calls= mut_calls } ->
    if mut_calls == 0 then called_es else e::called_es
  ) [] es counter_lst in
  if List.is_empty filtered_es then [(List.hd es)] else filtered_es

let use_base_case e : exp = 
  let rec traverse_ast (e:exp) : exp = 
    match e with 
    | Var _ -> e
    | App (func, args) -> App(traverse_ast func, List.map traverse_ast args)
    | Letrec (name, params, body) -> Letrec(name, params, traverse_ast body)
    | Let (x, v, let_body) -> Let (x, v, traverse_ast let_body)
    | ExtRef _ -> e
    | Case (_, _, clauses) -> 
        match List.hd clauses with
        | (_, e2) -> e2
    in
  traverse_ast e

let shrinker (es : exp list) = 
  let es = remove_uncalled_mutuals es in
  let es = List.map use_base_case es in
  es