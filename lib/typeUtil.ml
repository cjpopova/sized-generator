open Exp;;

(*********************** TYPE COMPARISON ******************************)

(* size_exp comparison*)
let rec ($<=) (sexp1 : size_exp) (sexp2 : size_exp) : bool = 
  match sexp1 with
  | Inf -> false
  | (SVar _) -> true (* NOTE: assume they have the same size variable? 
                        are we ever comparing size_exps with different variables in the simple algebra? *)
  | (SHat e1) -> 
    match sexp2 with
    | Inf -> true
    | (SVar _) -> false
    | (SHat e2) -> e1 $<= e2

let rec is_same_ty tyl1 tyl2 = (* type-equal? *) (*CJP: todo add subtyping*)
  match (tyl1, tyl2) with
  | (TyCons (name1, _, sexp1), TyCons (name2, _, sexp2)) ->
    name1 = name2
    && sexp1 $<= sexp2 (* allows size subtyping *)
  | (TyArrow (doms1, cod1), TyArrow (doms2, cod2)) -> 
    List.length doms1 = List.length doms2
    && List.for_all2 is_same_ty doms1 doms2
    && is_same_ty cod1 cod2
  | (_, _) -> false

(* is maybe a function type that produces target? TODO NOT higher order*)
let ty_produces target maybe =
  match maybe with
  | TyArrow (_, cod) -> is_same_ty target cod
  | _ -> false

(********************** CONSTRUCTORS **********************************)

(* NOTE: could be improved. these are cached in generators.main

Returns the std_lib form of *base* datatype constructors, or ones that require no
recursive arguments.
Example (TO TEST): [{ty=tInt;  constructors=["Zero", []; ("Succ", [tInt])]}] -> ["Zero", tyInt]
*)
let base_constructors_to_std_lib (cons : data_constructor_t) : (string * size_ty) list = 
  List.fold_left
    (fun acc {ty=ty; constructors=constructors} -> 
      List.filter_map 
      (fun cc -> if List.is_empty (snd cc) then Some(fst cc, ty) else None)
      constructors
      @ acc)
    []
    cons

(* Same as base_constructors_to_std_lib, but for recursive constructors (eg Succ) *)
let recur_constructors_to_std_lib (cons : data_constructor_t) : (string * size_ty) list = 
  List.fold_left
    (fun acc {ty=ty; constructors=constructors} -> 
      List.filter_map 
      (fun cc -> if List.is_empty (snd cc) then None else Some(fst cc, ty))
      constructors
      @ acc)
    []
    cons

(* get the constructors of a given type *)
let rec lookup_constructors (cons : data_constructor_t) (ty : size_ty) : (string * size_ty list) list =
  match cons with
  | [] -> (match ty with
    | TyCons (name, _, _) -> raise (Util.Impossible (Format.sprintf "lookup: constructors not found: %s" name))
    | TyArrow _ ->  raise (Util.Impossible "lookup: constructors not found "))
  | {ty=t; constructors=constructors} :: rst ->
    if is_same_ty t ty then constructors else lookup_constructors rst ty

(************************ SIZE ALGEBRA ***********************************)


(* Pseudocode for reachable, produces. sigma is the target type

reachable sigma t = t \subtype sigma || produces sigma t
produces sigma t = 
  TyArrow(doms, cod) = t
  List.for_all (fun dom -> 
        let dom_st = subst_size dom (t ~=~ sigma) (* SEE BELOW: substitute size variable in the domain with target size variables *)
        exists (x:t) in Gamma . reachable dom_st t)
    doms

Example: 
  sigma = Nat khat (* notice this uses a fresh size variable k. the stuff we've created during generation
  is also k-sized. the library functions are i-sized, and will need substitution *)
  Gamma = [(x : Nat khat); (x' : Nat k); (Succ : Nat i -> Nat ihat); (id : Nat i -> Nat i)]

  produces sigma id = 
    let dom_st = subst_size (Nat i) i **khat** = Nat khat
    exists (x : Nat khat) in Gamma . reachable (Nat khat) (Nat khat)

  produces sigma Succ = 
    let dom_st = subst_size (Nat i) i **k** = Nat k 
    exists (x' : Nat k) in Gamma . reachable (Nat k) (Nat k) *)
  
  (* both (id x) and (Succ x') are ways to produce sigma.
  the issue: how did i identify khat and k for the substitution below?
  by comparing codomains
  1. i ~=~ khat -> khat
  2. ihat ~=~ khat -> k

  (* return type:
  first element : string = name of size variable in the context
  second elemnt : sexp = size expression in the function's type to substitute
  *)
  let (~=~) sexp target = 
    match (sexp, target) with
    | _         , Inf        -> ??? (* see Inf1 below*)
    | Inf       , _          -> None (* incompatible since the target is sized but the producer is unsized *)
    | (SVar i)  , _          -> Some (i, target) (* note that target can be arbitrarily large *)
    | SHat iexp , SHat kexp  -> iexp ~=~ kexp
    | _         , _          -> None (* Example: SHat iexp, SVar k is incompatible because in our size algebra we won't be able to deconstruct k when we need to unhat i eventually *)


  Inf1: if we're trying to produce something of size Inf but we want to call a recursive function,
    we still need to provide SOME sized value of the same datatype, but we don't care what. so we
    could just pick one of the available sized types in the context

  TODO: do some more examples to prove this works before coding
  *)














(* OLD STUFF *)
let rec substitute_size_exp (theta : size_exp) (i : string) (e : size_exp) : size_exp = 
  match theta with
  | Inf -> Inf
  | (SVar x) -> if x = i then e else (SVar x)
  | (SHat theta') -> (SHat (substitute_size_exp theta' i e))

    (*
  substitute : sized_ty size_exp -> sized_ty
  substitute (UBool, _) _ = (UBool, inf)
  substitute (UNat, e1) e2 = (UNat, (substitute_size_exp e1 e2)
  *)

