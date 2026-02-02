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
- [x] remove m2 if it is not called by m1
- [ ] remove (mutual) recursive call & replace with placeholder
- [ ] shrink constants to 0
- [ ] remove match branches
- [ ] replace let-bindings with constants (eg (let x=e1 in e2) become (let x=1 in e2))
- [ ] remove unused let binding
- [~] replace (match e1 with |c1 -> e2 | c2 -> e3) with e2 (should have no free variables)
*)

(* remove m0 if it is not called by m1, etc *)
let remove_uncalled_mutuals es : exp list = 
  let counter_lst = analyze_num_mutual_calls es in
  (* print_count_lst counter_lst; *)
  let filtered_es = List.fold_left2 (fun called_es e { self_calls=_; mutual_calls= mut_calls } ->
    if mut_calls == 0 then called_es else e::called_es
  ) [] es counter_lst in
  if List.is_empty filtered_es then [(List.hd es)] else filtered_es


(* TODO: how do we handle mapping across lists of arguments or clauses??
and recombining those into a sequence

using list.map produces exp seq.t list
whereas we want exp seq.t seq.t
which we can accomplish by turning the underlying list into an seq first

Lets say we have args=[a;b]
then for each we have sequences <a',etc> and <b',etc>
we want to produce <Constructor(a',b); constructor(etc,b)...; Constructor(a,b'); constructor(a,etc)...>
*)
(* let use_base_case e : exp Seq.t = 
  (* replace ith element of lst with v *)
  let replace (lst : 'a list) (i : int) (v : 'a) : 'a list = 
    let rec helper lst j = 
      match lst with
      | [] -> []
      | h :: t -> if i=j then v::t else h::(helper t (j+1))
    in helper lst 0 in

  let rec traverse_ast (e:exp) : exp Seq.t = 
    match e with 
    | Var _ -> List.to_seq [e]
    | App (func, args) -> 
      let fs : exp Seq.t = (traverse_ast func) |> Seq.map (fun f' -> App (f', args)) in
      let args_s : exp Seq.t list = (List.map traverse_ast args) in
      let args_combine : exp Seq.t list = List.mapi (fun i (seq: exp Seq.t) -> 
        Seq.map (fun a -> App (func, replace args i a)) seq)
        args_s in
      Seq.append fs @@ Seq.concat (List.to_seq args_combine)
    | Letrec (name, params, body) -> 
      traverse_ast body
      |> Seq.map (fun body' -> Letrec(name, params, body'))
    | Let (x, v, let_body) -> 
      traverse_ast let_body
      |> Seq.map (fun body' -> Let (x, v, body'))
    | ExtRef _ -> List.to_seq [e]
    | Case (head, ty, clauses) -> 
        (match List.hd clauses with
        | (_, e2) -> 
          let _ : (var list * exp) list = replace clauses 0 ([], e2) in

          let shrink_clauses : exp Seq.t list = 
            List.mapi (fun i (binders, e) ->
              Seq.map (fun e' -> 
                let pair = (binders, e') in
                Case (head, ty,
              
              (* clauses *)
              replace clauses i pair
              
              
              ))
               (traverse_ast e))
            clauses in
          Seq.concat @@ List.to_seq shrink_clauses) (* TODO: add e2*)
    in
  traverse_ast e *)


  (* oh god we have to have sequences of sequences - maybe this is why we should split these steps up at a higher level
   *)
let shrinker (es : exp list) : exp list Seq.t = 
  let es : exp list = remove_uncalled_mutuals es in
  (* let es = List.map use_base_case es in *)
  Seq.return es