open Exp;;

(************************ SIZE ALGEBRA HELPERS ***********************************)

(* get the size variable from a size expression
this is the |_s_| procedure from Barthe Tutorial p. 43 *)
let rec size_var_of_sexp sexp = 
  match sexp with
  | Inf -> None
  | SVar _ -> Some sexp
  | SHat sexp -> size_var_of_sexp sexp

let rec size_var_of_ty ty = 
  match ty with
  | TyCons (_, _, sexp) -> size_var_of_sexp sexp 
  | TyArrow (ty_params, _) -> 
    List.fold_left 
    (fun acc ty -> if Option.is_some acc then acc else size_var_of_ty ty)
    None
    ty_params

(* size_exp comparison*)
let rec ($<=) (sexp1 : size_exp) (sexp2 : size_exp) : bool = 
  match sexp1 with
  | Inf -> sexp2 = Inf (* Inf $<= Inf *)
  | (SVar _) -> true (* NOTE: assume they have the same size variable? 
                        are we ever comparing size_exps with different variables in the simple algebra? *)
  | (SHat e1) -> 
    match sexp2 with
    | Inf -> true
    | (SVar _) -> false
    | (SHat e2) -> e1 $<= e2

  (* input:
  sexp = size expression of the (maybe function)'s codomain
  target = size expression of the target type
  return type:
  first element = name of size variable in the context (LHS)
  second element size expression in the function's type to substitute in (RHS)
  *)
let rec size_exp_helper sexp target = 
    match (sexp, target) with
    | _         , Inf        -> raise (Util.Impossible "size_exp_helper: INF1 CASE")  (* see Inf1 below*)
    | Inf       , _          -> None (* incompatible since the target is sized but the producer is unsized *)
    | (SVar i)  , _          -> Some (i, target) (* note that target can be arbitrarily large *)
    | SHat iexp , SHat kexp  -> size_exp_helper iexp kexp
    | _         , _          -> None (* Example: SHat iexp, SVar k is incompatible because in our size algebra we won't be able to deconstruct k when we need to unhat i eventually *)

(* TODO: eventually i should be an size_exp not just a string*)
let rec subst_size_exp (sexp : size_exp) (i : string) (e : size_exp) : size_exp = 
  match sexp with
  | Inf -> Inf
  | (SVar x) -> if x = i then e else raise (Util.Impossible (Format.sprintf "subst_size_exp: bad SVar name encountered: %s" x))
  | (SHat sexp') -> (SHat (subst_size_exp sexp' i e))

let rec subst_size_of_ty (theta : size_ty) (i : string) (e : size_exp) : size_ty = 
  match theta with
  | TyCons(name, params, sexp) -> TyCons(name, params, subst_size_exp sexp i e)
  | TyArrow(doms, cod) -> TyArrow(List.map (fun ty -> subst_size_of_ty ty i e) doms, subst_size_of_ty cod i e)

let size_exp_of_ty ty =
  match ty with
  | TyCons(_, _, sexp) -> sexp
  | _ -> raise (Util.Impossible (Format.sprintf "size_exp_of_ty: called on function: %s" (show_size_ty ty)))

(*********************** TYPE COMPARISON ******************************)

let rec is_same_ty maybe target = (* type-equal? *) (*CJP: todo add subtyping*)
  match (maybe, target) with
  | (TyCons (name1, _, sexp1), TyCons (name2, _, sexp2)) ->
    name1 = name2
    && sexp1 $<= sexp2 (* allows size subtyping *)
  | (TyArrow (doms1, cod1), TyArrow (doms2, cod2)) -> 
    List.length doms1 = List.length doms2
    && List.for_all2 is_same_ty doms2 doms1 (* flipped for subtyping *)
    && is_same_ty cod1 cod2
  | (_, _) -> false
and
(* is maybe a function type that produces target? TODO NOT higher order*)
ty_produces maybe target (env : env) =
  match maybe with
  | TyArrow (doms, cod) -> 
    is_same_ty cod target (* this part doesn't care about size variable names*)
    && List.for_all (fun dom ->
      match size_exp_helper (size_exp_of_ty cod) (size_exp_of_ty target) with (* usage of size_exp_of_ty constrains this to first-order*)
      | None -> false
      | Some (iexp, kexp) ->
        let dom_st = subst_size_of_ty dom iexp kexp in
        List.exists (fun var -> reachable var.var_ty dom_st env) env
      )
      doms
  | _ -> false
and reachable maybe t env = is_same_ty maybe t || (ty_produces maybe t env)

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
      (fun cc -> if List.is_empty (snd cc) then None else Some(fst cc, ty)) (* TODO this should produce a function type*)
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

reachable sigma t = is_same_ty t sigma || (produces sigma t)
produces sigma t = 
  TyArrow(doms, cod) = t
  is_same_ty cod sigma && (* this part doesn't care about size variable names*)
  List.for_all (fun dom -> 
        let dom_st = subst_size dom (t ~=~ sigma) (* SEE BELOW: substitute size variable in the domain with target size variables *)
        exists (x:t) in Gamma . reachable dom_st t)
    doms

Example: 
  sigma = Nat khat (* notice this uses a fresh size variable k. the stuff we've created during generation
  is also k-sized. the library functions are i-sized, and will need substitution *)
  Gamma = [(x : Nat khat); (x' : Nat k); (Succ : Nat i -> Nat ihat); (id : Nat i -> Nat i)]

  (* both (id x) and (Succ x') are ways to produce sigma: *)
  produces sigma id = 
    let dom_st = subst_size (Nat i) i **khat** = Nat khat
    exists (x : Nat khat) in Gamma . reachable (Nat khat) (Nat khat)

  produces sigma Succ = 
    let dom_st = subst_size (Nat i) i **k** = Nat k 
    exists (x' : Nat k) in Gamma . reachable (Nat k) (Nat k) *)
  
  (* The issue: how did i identify khat and k for the substitution below?
  by comparing codomains
  1. i ~=~ khat -> khat
  2. ihat ~=~ khat -> k

  (* input:
  sexp = size expression of the maybe function's codomain
  target = size expression of the target type

  return type:
  first element : string = name of size variable in the context (LHS)
  second element : sexp = size expression in the function's type to substitute in (RHS)
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
    could just pick one of the compatible available sized types in the context
    this clause will never happen in the CASE rule below because we're always picking something sized for the head of the CASE
    but it may happen for other scenarios. for now assume we're just going generate size preserving function

  ----------------------------------------

  CASE RULE
  let head:var = {_; ty= Nat khat} (* we select something sized from the context for the head of the case *)
  data_cons = ["Zero", []; ("Succ", [tInt (SVar "i")])]
  when we generate the variables for the context of the clauses, we need a (tInt SVar "k") for the Succ case
  so we'd do
  let Some(iexp,kexp) = constructor.codomain ~=~ khat
  let params = Exp.new_var (subst_size constructor.dom iexp kexp) (* ignore list stuff*)


  observations:
  - we're trying to preserve an invariant that the target type is always sized with variables we can generate
  - reduces to the same issue as the application like Harry was saying :') 

  *)
