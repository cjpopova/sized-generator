open Exp
open Library

(* TODO: needs tracer*)

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
  (* NOTE: enable following APIs with List.* notation *)
  (* "head"   ,[tList i tX] --> tX; *)
  (* "tail"   ,[tList i tX] --> tX;
  "take"   ,[tList i tX; tNat Inf] --> tList i tX;
  "list-ref",[tList i tX; tNat Inf] --> tX;
  "append"  ,[tList i tX; tList Inf tX] --> tList Inf tX; (* size algebra expressivity *)
  "concat"  ,[tList i (tList Inf tX)] --> tList Inf tX;
  make-list (1-fuel cost to make large constant size lists) *)

  (* higher order danger zone:
  map      ,[(tX --> tY), tList i tX] -->  tList i tY;
  foldr    ,N/A
  *)
  ]

(*************************************************************************************************************************)

let header : string =  
"[@@@ocaml.warning \"-26-27-39\"] (* supress unused variable, unused rec flag warnings ~ equivalent to ocamlc <thisfile> -w -26-17-39 *)
let nat_min (x : int) (y : int): int = if y >= x then 0 else (x-y);; (* defn of minus for naturals *)
"

(******************* HELPERS *******************)
(* string of variable names with space separators*)
let var_lst_string (vs : var list) : string = String.concat " " (List.map (fun v -> v.var_name) vs)

(* type signature for functions *)
let type_sig_string (f : var) (params : var list) : string =
  let rec show_unsized_ty ty = 
  match ty with
  | TyVar (name, _) -> name
  | TyCons (name, [], _) -> name 
  | TyCons (name, tys, _) -> "(" ^ String.concat ", " (List.map (fun ty -> show_unsized_ty ty) tys) ^ ")" ^ name 
  | TyArrow(_, doms, cod) ->
     "(" ^ List.fold_right (fun ty acc -> show_unsized_ty ty ^ " -> " ^ acc) doms "" 
     ^ show_unsized_ty cod ^ ")"
  in
  match f.var_ty with
  | TyArrow(_, _, cod) ->
    String.concat " " (List.map (fun v -> "(" ^ v.var_name ^ ":" ^ show_unsized_ty v.var_ty ^ ")") params)
    ^ " : " ^ show_unsized_ty cod
  | _ -> raise (Util.Impossible "type_sig_string: not a function type")

let is_infix f = String.equal "(" (String.sub f 0 1)

let make_infix f = String.sub f 1 (String.length f - 2)

(******************** main printer function for single expression ********************)
let ml_string (e : exp) : string =
  (* main recursive printer *)
  let rec ml_str (e : exp) : string = 
    match e with 
    | Var x -> x.var_name
    | Lambda (_, _) -> raise (Util.Unimplemented (Format.sprintf "ml_string: Lambda"))
    | App (func, args) ->  (* (func args) *)
      (match func, args with
      | ExtRef (f, _), [e1; e2] when is_infix f ->
         "(" ^ ml_str e1 ^
        " " ^ make_infix f ^ " " ^
        ml_str e2 ^ ")"
      | _, [] ->  ml_str func ^ "()"
      | _, _ -> "(" ^ ml_str func ^ " " ^ String.concat " " (List.map ml_str args) ^ ")")      
    | Letrec (func, params, body) -> (*  (let rec f (params) : retTy = body in f)  *)
      "(let rec " ^ func.var_name ^ " " 
      ^ type_sig_string func params ^ " =\n"
      ^ ml_str body ^ " in " ^ func.var_name ^")"
    
    | NLetrec (func, params, func_body, let_body)  ->
      "(let rec " ^ func.var_name ^ " " 
      ^ type_sig_string func params ^ " =\n"
      ^ ml_str func_body ^ " in \n" 
      ^ ml_str let_body ^")"

    | ExtRef (name, _) -> name
    | Case (e, ty, clauses) -> (* (match e with | D (x ...) -> e_1) ... ) *)
      "(match " ^ ml_str e ^ " with \n" ^ 
      (match ty with
      | TyCons ("int", _, _) ->
        (match clauses with
        | [(_, e1); ([nprime], e2)] -> 
          "| 0 -> " ^ ml_str e1 ^ 
          "\n| _ -> let " ^ nprime.var_name ^ " = " ^ ml_str e ^"-1 in " ^ ml_str e2
        | _ -> raise (Util.Impossible "match dispatch: Nat pattern not found"))
      | TyCons ("list", _, _) -> 
        (match clauses with
        | [(_, e1); ([h; t], e2)] -> 
          "| [] -> " ^ ml_str e1 ^ 
          "\n| " ^ h.var_name ^ "::" ^ t.var_name ^ " -> " ^ ml_str e2
        | _ -> raise (Util.Impossible "match dispatch: List pattern not found"))
      | _ -> (* Normal constructor case *)
        let constructors = TypeUtil.lookup_constructors data_constructors ty in
        (String.concat "| "
          (List.map2 
          (fun (vars, body) (cname, _) -> cname ^ "(" ^ var_lst_string vars ^ ")" ^ ml_str body ^ "\n")
          clauses constructors)))
      ^ ")"

  in ml_str e

(******************** top level printer for multiple mutually-recursive expressions ********************)
let ml_complete_string (es : exp list) (input : string): string =
  (* helper *)
  let letrec_string func params body =
    func.var_name ^ " " 
    ^ type_sig_string func params ^ " =\n"
    ^ ml_string body
  in
  (* let rec f1 ... = ... and f2 ... = ... *)
  match es with 
  | Letrec (func, params, body) :: t ->
    header ^ "\n\n" ^
    "let rec " ^ letrec_string func params body ^ 
    (if List.is_empty t then "" else "\nand\n") ^
      String.concat "\nand\n" (List.map (fun e -> 
        match e with 
        | Letrec (func, params, body) -> letrec_string func params body
        | _ -> raise (Util.Impossible "ml_complete_string: bad exp given"))
        t)
    ^ "\n in " ^ func.var_name ^ " " ^ input (* call to the first function *)
  | _ -> raise (Util.Impossible "ml_complete_string: bad exp list given")
  


let ml_  =
    (module struct
      let data_constructors = data_constructors
      let std_lib = std_lib
      let printer = ml_complete_string
    end : Language)