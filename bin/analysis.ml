open Exp
(* Static analysis on exps for *)

type counters = { self_calls: int; mutual_calls: int }
let empty_counter _ = {self_calls = 0; mutual_calls=0}
let add_counters c1 c2 = {self_calls = c1.self_calls + c2.self_calls; mutual_calls=c1.mutual_calls + c2.mutual_calls}

(* list of how many times ith function calls other mutually recursive functions (not including itself) *)
let analyze_num_mutual_calls (es : exp list) : counters list = 
  (* get vars of top level functions *)
  let mutuals = List.map func_var es in

  let rec traverse_ast (e:exp) (self_name:var) : counters = 
    match e with 
    | Var _ -> empty_counter ()
    | Lambda (_, body) -> traverse_ast body self_name
    | App (func, args) -> 
      add_counters
      (match func with
      | Var v when v=self_name -> {self_calls = 1; mutual_calls=0}
      | Var v when List.mem v mutuals -> {self_calls=0; mutual_calls=1}
      | _ -> traverse_ast func self_name)
      (List.fold_left (fun acc e -> add_counters acc (traverse_ast e self_name)) (empty_counter ()) args)
    | Letrec (_, _, body) -> traverse_ast body self_name
    | NLetrec (_, _, func_body, let_body) -> 
      add_counters (traverse_ast func_body self_name) (traverse_ast let_body self_name)
    | ExtRef (_, _) -> empty_counter ()
    | Case (_, _, clauses) -> List.fold_left (fun acc (_, body)-> add_counters acc (traverse_ast body self_name)) (empty_counter ()) clauses
    in

  List.map2 traverse_ast es mutuals