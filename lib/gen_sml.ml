open Exp
open Library

let data_constructors : data_constructors_t = [
    ["true", [] --> tBool; 
     "false", [] --> tBool ];
    ["0", [] --> tNat ihat;
     "1+", [tNat i] --> tNat ihat]; (* Succ*)
    ["[]", [] --> tList ihat tX;
     "(::)", [tX; tList i tX] --> tList ihat tX]
    ]

let std_lib = [
  "(+)",    [tNat i; tNat Inf] --> tNat Inf;
  "nat_min",    [tNat i; tNat Inf] --> tNat i; (* minus*)
  (* "odd",    [tNat Inf] --> tBool;
  "even",   [tNat Inf] --> tBool; *)
  "(&&)",   [tBool; tBool] --> tBool;
  "(||)",   [tBool; tBool] --> tBool;
  "not",    [tBool] --> tBool;
  "(==)",   [tX; tX] --> tBool;
  "42",     tNat Inf; (* it is useful to have some large constants, because Succ consumes fuel*)
  "560",    tNat Inf;
  "1000000",tNat Inf;
  "10 :: 50 :: []", tList Inf (tNat Inf);
  "concat"  ,[tList i (tNat Inf); tList Inf (tNat Inf)] --> tList Inf (tNat Inf);
  "map"     ,[([tNat Inf] --> tNat Inf); tList i (tNat Inf)] -->  tList i (tNat Inf);
  ]

(*************************************************************************************************************************)

let header : string =  
"fun nat_min (x : int) (y : int): int = if y >= x then 0 else (x-y);; (* defn of minus for naturals *)
"

(******************* HELPERS *******************)
(* string of variable names with space separators*)
let var_lst_string (vs : var list) : string = String.concat " " (List.map (fun v -> v.var_name) vs)

let rec show_unsized_ty ty = 
  match ty with
  | TyVar (name, _) -> name
  | TyCons (name, [], _) -> name 
  | TyCons (name, tys, _) -> "(" ^ String.concat ", " (List.map (fun ty -> show_unsized_ty ty) tys) ^ ")" ^ name 
  | TyArrow(_, doms, cod) ->
     "(" ^ List.fold_right (fun ty acc -> show_unsized_ty ty ^ " -> " ^ acc) doms "" 
     ^ show_unsized_ty cod ^ ")"

(* type signature for functions *)
let type_sig_string (f : var) (params : var list) : string =
  match f.var_ty with
  | TyArrow(_, _, cod) ->
    String.concat " " (List.map (fun v -> "(" ^ v.var_name ^ ":" ^ show_unsized_ty v.var_ty ^ ")") params)
    ^ " : " ^ show_unsized_ty cod
  | _ -> raise (Util.Impossible "type_sig_string: not a function type")

let is_infix f = String.equal "(" (String.sub f 0 1)

let make_infix f = String.sub f 1 (String.length f - 2)

(******************** main printer function for single expression ********************)

  let rec ml_str (e : exp) : string = 
    match e with 
    | Var x -> x.var_name
    | App (func, args) ->  (* (func args) *)
      (match func, args with
      | ExtRef (f, _), [e1; e2] when is_infix f ->
         "(" ^ ml_str e1 ^
        " " ^ make_infix f ^ " " ^
        ml_str e2 ^ ")"
      | _, [] ->  ml_str func ^ "()"
      | _, _ -> "(" ^ ml_str func ^ " " ^ String.concat " " (List.map ml_str args) ^ ")")      
    | Letrec (func, params, body) -> (*  (let fun f (params) : retTy = body in f end)  *)
      "(let fun " ^ func.var_name ^ " " 
      ^ type_sig_string func params ^ " =\n"
      ^ ml_str body ^ " in " ^ func.var_name ^" end)"
    | Let (x,v,body) -> "(let val " ^ x.var_name ^ " : " ^ show_unsized_ty x.var_ty ^ " =\n"
      ^ ml_str v ^ " in \n" 
      ^ ml_str body ^" end)"
    | ExtRef (name, _) -> name
    | Case (e, ty, clauses) -> 
      "(case " ^ ml_str e ^ " of \n" ^ 
      (match ty with
      | TyCons ("int", _, _) ->
        (match clauses with
        | [(_, e1); ([nprime], e2)] -> 
          "  0 => " ^ ml_str e1 ^ 
          "\n| _ => let val " ^ nprime.var_name ^ " = " ^ ml_str e ^"-1 in " ^ ml_str e2 ^ " end"
        | _ -> raise (Util.Impossible "match dispatch: Nat pattern not found"))
      | TyCons ("list", _, _) -> 
        (match clauses with
        | [(_, e1); ([h; t], e2)] -> 
          "  [] => " ^ ml_str e1 ^ 
          "\n| " ^ h.var_name ^ "::" ^ t.var_name ^ " => " ^ ml_str e2
        | _ -> raise (Util.Impossible "match dispatch: List pattern not found"))
      | _ -> (* Normal constructor case *)
        let constructors = TypeUtil.lookup_constructors data_constructors ty in
        (String.concat "| "
          (List.map2 
          (fun (vars, body) (cname, _) -> cname ^ "(" ^ var_lst_string vars ^ ") => " ^ ml_str body ^ "\n")
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
  "fun " ^
  String.concat "\nand " (List.map (fun e -> 
    match e with 
    | Letrec (func, params, body) -> func.var_name ^ type_sig_string func params ^ " =\n"
      ^ ml_str body
    | _ -> raise (Util.Impossible "mutual_recursive_funcs: bad exp given"))
    es)
  ^ ";;\n"

let ml_complete_string (fs : exp list list) (input : string): string = 
  let fundefs, code_list = List.fold_left (fun (fundefs, codelst) es -> 
    fundefs ^ (mutual_recursive_funcs es)
    , first_func_name es :: codelst)
    ("",[]) fs in

    header ^ "\n\n"
    ^ fundefs ^ "\n\n"
    ^ "val code_list = [" ^ String.concat ", " code_list ^ "];;\n"
    ^ "print(\"[\"^String.concatWith \",\" (map (fn code => Int.toString " ^input^") code_list) ^ \"]\\n\")" 

let sml_  =
    (module struct
      let data_constructors = data_constructors
      let std_lib = std_lib
      let printer = ml_complete_string 
end : Language)