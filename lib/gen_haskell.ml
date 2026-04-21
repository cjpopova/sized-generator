open Exp
open Library
open Gen_ml

(* Re-use gen_ml's data constuctors and std_lib with some renaming *)
let data_constructors : data_constructors_t = List.map ( fun data_cons ->
   List.map (fun (name, ty) ->
    let n_name = match name with
    | "(::)" -> "(:)"
    | _ -> name
    in n_name, ty)
  data_cons)
  Gen_ml.data_constructors

let std_lib = List.map ( fun (name, ty )->
  let n_name = match name with
  | "(10 :: 50 :: [])" -> "(10 : 50 : [])"
  | "List.map" -> "map"
  | "List.fold_left" -> "foldl"
  | "List.append" -> "(++)"
  | _ -> name in
  n_name, ty
  ) Gen_ml.std_lib
  
  
(*************************************************************************************************************************)


(******************* HELPERS *******************)

let rec show_unsized_ty ty = 
  match ty with
  | TyVar (name, _) -> name
  | TyCons ("int", _, _) -> "Int"
  | TyCons ("list", [ty], _) -> "["^show_unsized_ty ty^"]"
  | TyCons (name, [], _) -> name 
  | TyCons (name, tys, _) -> "(" ^ String.concat ", " (List.map (fun ty -> show_unsized_ty ty) tys) ^ ")" ^ name 
  | TyArrow(_, doms, cod) ->
     "(" ^ List.fold_right (fun ty acc -> show_unsized_ty ty ^ " -> " ^ acc) doms "" 
     ^ show_unsized_ty cod ^ ")"

let string_of_params params = (String.concat " " (List.map (fun v -> v.var_name) params))

let header : string =  
"module Main where
import Control.Monad

nat_min :: Int -> Int -> Int
nat_min x y = if y >= x then 0 else (x-y) -- defn of minus for naturals 
"

(******************** main printer function for single expression ********************)

  let rec haskell_str (e : exp) : string = 
    match e with 
    | Var x -> x.var_name
    | App (func, args) ->  (* (func args) *)
      (match func, args with
      | ExtRef (f, _), [e1; e2] when is_infix f ->
         "(" ^ haskell_str e1 ^
        " " ^ make_infix f ^ " " ^
        haskell_str e2 ^ ")"
      | _, [] ->  haskell_str func ^ "()"
      | _, _ -> "(" ^ haskell_str func ^ " " ^ String.concat " " (List.map haskell_str args) ^ ")")      
    | Letrec (func, params, body) -> (*  (let fun f (params) : retTy = body in f end)  *)
      "(let " ^ func.var_name ^ " :: " ^ show_unsized_ty func.var_ty ^ " = "
      ^ " \\ " ^ string_of_params params ^ " -> " ^ haskell_str body ^ " in " ^ func.var_name ^")"
    | Let (x,v,body) -> "(let " ^ x.var_name ^ " ="
      ^ haskell_str v ^ " in " 
      ^ haskell_str body ^")"
    | ExtRef (name, _) -> name
    | Case (e, ty, clauses) -> 
      "(case " ^ haskell_str e ^ " of " ^ 
      (match ty with
      | TyCons ("int", _, _) ->
        (match clauses with
        | [(_, e1); ([nprime], e2)] -> 
          "  0 -> " ^ haskell_str e1 ^ 
          "; _ -> let " ^ nprime.var_name ^ " = " ^ haskell_str e ^"-1 in " ^ haskell_str e2 
        | _ -> raise (Util.Impossible "match dispatch: Nat pattern not found"))
      | TyCons ("list", _, _) -> 
        (match clauses with
        | [(_, e1); ([h; t], e2)] -> 
          "  [] -> " ^ haskell_str e1 ^ 
          "; " ^ h.var_name ^ ":" ^ t.var_name ^ " -> " ^ haskell_str e2
        | _ -> raise (Util.Impossible 
        (Format.sprintf "match dispatch: List pattern not found on %s" 
        (String.concat " " (List.map (fun (_, e) -> (show_exp e)) clauses)))
        ))
      | _ -> (* Normal constructor case *)
        let constructors = TypeUtil.lookup_constructors data_constructors ty in
        (String.concat "| "
          (List.map2 
          (fun (vars, body) (cname, _) -> cname ^ "(" ^ var_lst_string vars ^ ") => " ^ haskell_str body)
          clauses constructors)))
      ^ ")"

(******************** top level printer for multiple mutually-recursive expressions ********************)

(* define set of mutually recursive functions & expose the first one, eg
(fun m1 x = ...
  and m2 x = ...
  ...
  ;;)
*)
let mutual_recursive_funcs (es : exp list): string =
  String.concat "\n\n" (List.map (fun e -> 
    match e with 
    | Letrec (func, params, body) -> 
      func.var_name ^ " :: " ^ show_unsized_ty func.var_ty ^ "\n"
      ^ func.var_name ^ " " ^ string_of_params params ^ " = "
      ^ haskell_str body
    | _ -> raise (Util.Impossible "mutual_recursive_funcs: bad exp given"))
    es)

let hs_complete_string (fs : exp list list) (input : string): string = 
  let fundefs, codelist = List.fold_left (fun (fundefs, codelst) es -> 
    fundefs ^ (mutual_recursive_funcs es)
    , first_func_name es :: codelst)
    ("",[]) fs in

    let main = 
      "codeList = ["^ String.concat "," codelist ^ "]\n"
      ^ "main = do forM_ codeList $ \\ code -> do print "^input in 

    header ^ "\n\n"
    ^ fundefs ^ "\n\n"
    ^ main

let hs_  =
    (module struct
      let data_constructors = data_constructors
      let std_lib = std_lib
      let printer = hs_complete_string 
end : Language)