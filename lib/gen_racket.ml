open Exp
open Library


let tBool = TyCons ("bool", [], ihat) (* technically bools are unsized but this simplifies substitution *)
let tNat sexp = TyCons ("int", [], sexp)
let tList sexp ty = TyCons ("list", [ty], sexp)


let data_constructors : data_constructors_t = [
    ["true", [] --> tBool; 
     "false", [] --> tBool ];
    ["0", [] --> tNat ihat;
     "add1", [tNat i] --> tNat ihat]; (* Succ*)
    ["'()", [] --> tList ihat tX;
     "cons", [tX; tList i tX] --> tList ihat tX]
    ]

let std_lib = [
  "+",    [tNat i; tNat Inf] --> tNat Inf;
  "nat_min",    [tNat i; tNat Inf] --> tNat i; (* minus*)
  "odd",    [tNat Inf] --> tBool;
  "even",   [tNat Inf] --> tBool;
  "and",   [tBool; tBool] --> tBool;
  "or",   [tBool; tBool] --> tBool;
  "not",    [tBool] --> tBool;
  "==",   [tX; tX] --> tBool;
  "42",     tNat Inf; (* it is useful to have some large constants, because Succ consumes fuel*)
  "560",    tNat Inf;
  "1000000",tNat Inf;
  "10 :: 50 :: []", tList Inf (tNat Inf);
  (* "head"   ,[tList i tX] --> tX; *)
  "tail"   ,[tList i tX] --> tX;
  "take"   ,[tList i tX; tNat Inf] --> tList i tX;
  "list-ref",[tList i tX; tNat Inf] --> tX;
  "append"  ,[tList i tX; tList Inf tX] --> tList Inf tX; (* size algebra expressivity *)
  "concat"  ,[tList i (tList Inf tX)] --> tList Inf tX;
  (* make-list (1-fuel cost to make large constant size lists) *)

  (* higher order danger zone:
  map      ,[(tX --> tY), tList i tX] -->  tList i tY;
  foldr    ,N/A
  *)
  ]

(*************************************************************************************************************************)

(******************* HELPERS *******************)
(* string of variable names with space separators*)
let var_lst_string (vs : var list) : string = String.concat " " (List.map (fun v -> v.var_name) vs)

(******************** main printer function for single expression ********************)
  (* main recursive printer *)
  let rec rkt_str (e : exp) : string = 
    match e with 
    | Var x -> x.var_name
    | App (func, args) ->  (* (func args) *)
      "(" ^ rkt_str func ^ " " ^ String.concat " " (List.map rkt_str args) ^ ")"
    
    | Letrec (func, params, body) -> (*  (letrec ([f (λ (params) body)]) f)  *)
      "(letrec ([" ^ func.var_name ^ " (λ (" ^ var_lst_string params ^ ") \n"
      ^ rkt_str body ^ ")])\n" ^ func.var_name ^")"
    
    | Let (x, v, let_body)  -> (*  Nested letrec := (letrec ([f (λ (params) e_func_body)]) e_let_body) *)
      "(let ([" ^ x.var_name ^ " \n" 
      ^ rkt_str v ^ "])\n" 
      ^ rkt_str let_body ^")"

  
    | ExtRef (name, _) -> name
    
      | Case (e, ty, clauses) -> (* (match e [(D x ...) e_1)] ... ) *)
      "(match " ^ rkt_str e ^ "\n" ^ 
      (match ty with
      | TyCons ("int", _, _) ->
        (match clauses with
        | [(_, e1); ([nprime], e2)] -> 
          "[0 " ^ rkt_str e1 ^ "]\n[_ (let ([" ^ nprime.var_name ^ " (sub1 "  ^ rkt_str e ^")])\n"
          ^ rkt_str e2 ^ ")]"
        | _ -> raise (Util.Impossible "match dispatch: Nat pattern not found"))
      | TyCons ("list", _, _) -> 
        (match clauses with
        | [(_, e1); ([h; t], e2)] -> 
          "['() " ^ rkt_str e1 ^ "]\n[(cons " ^ h.var_name ^ " " ^ t.var_name ^ ") " ^ rkt_str e2 ^ "]"
        | _ -> raise (Util.Impossible "match dispatch: List pattern not found"))
      | _ -> (* Normal constructor case *)
        let constructors = TypeUtil.lookup_constructors data_constructors ty in
        (String.concat "\n"
          (List.map2 
          (fun (vars, body) (cname, _) -> "[(" ^ cname ^ " " ^ var_lst_string vars ^ ")" ^ " " ^ rkt_str body ^ "]")
          clauses constructors))) 
      ^ ")"


(******************** top level printer for multiple mutually-recursive expressions ********************)

let rkt_complete_string (fs : exp list Seq.t) (input : string): string =
  let fundefs, codelst = Seq.fold_left (fun (fundefs, codelst) es -> 
    fundefs ^ 
    String.concat ""
    (List.map (fun e -> 
      match e with 
      | Letrec (func, params, body) -> 
        "(define (" ^ func.var_name ^ " " ^ var_lst_string params ^")\n" ^ rkt_str body ^ ")\n"
      | _ -> raise (Util.Impossible "rkt_complete_string: bad exp given")) es)
    , "(cons "^first_func_name es^" "^codelst^")")
    ("","'()") fs in

  (match !Debug.test_type with
    | 430 ->
    "(define (map f ll)
      (match ll
          ['() '()]
          [(cons code rst) (cons (f code) (map f rst))]))\n"
    | 3027 -> "#lang racket/base
    (require racket/match)\n"
    | _ -> "#lang racket\n")

  ^ "(define (nat_min x y)
  (let ([z (- x y)])
    (if (< z 0) 0 z)))\n\n" 
  (* (define m0 (λ (x...) e...)) ...*)
  ^ fundefs
  ^ "\n(let ([code-list "
  (* (cons m0 (cons m1 ..'()..)) *)
  ^ codelst
  ^ "])
  (map (λ (code) " ^input^ ") code-list))"

let racket_  =
    (module struct
      let data_constructors = data_constructors
      let std_lib = std_lib
      let printer = rkt_complete_string
    end : Language)