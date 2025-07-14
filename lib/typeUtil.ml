open Exp;;

(************************ SIZE ALGEBRA HELPERS ***********************************)

(* get the size variable from a size expression
this is the |_s_| procedure from Barthe Tutorial p. 43 *)
(* let rec size_var_of_sexp sexp = 
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
    ty_params *)

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

  (*  SEE NOTES at the bottom of this file
  input:
  sexp = size expression of the (maybe function)'s codomain
  target = size expression of the target type
  return type:
  first element = name of size variable in the context (LHS)
  second element size expression in the function's type to substitute in (RHS)
  *)
type unificationResult =
  | UAny
  | USome of string * size_exp
  | UNone

let rec unify_size_exp sexp target = 
    match (sexp, target) with
    | _         , Inf        -> UAny (* see Inf1 notes below*)
    | (SVar i)  , _          -> USome (i, target) (* note that target can be arbitrarily large *)
    | SHat iexp , SHat kexp  -> unify_size_exp iexp kexp
    | _         , _          -> UNone 
    (* Example: SHat iexp, SVar k is incompatible because in our size algebra: we won't be able to deconstruct k when we need to unhat i eventually 

--------------------------------
substitution/unification resources
- leo's blockchain paper w/ unsubstitution (UNHELPFUL)
- https://en.wikipedia.org/wiki/Unification_(computer_science)
- https://www.csd.uwo.ca/~mmorenom/cs2209_moreno/read/read6-unification.pdf // unification and substitution
- unification algorithm in GG (generating good generators)
- https://dl.acm.org/doi/pdf/10.1145/357162.357169 (linked from wikipedia, For first-order syntactical unification, Martelli and Montanari[5])

    *)

(* NOTE: eventually `i` should be an size_exp not just a string*)
let rec subst_size_exp (sexp : size_exp) (i : string) (e : size_exp) : size_exp = 
  match sexp with
  | Inf -> Inf
  | (SVar x) -> if x = i then e else raise (Util.Impossible (Format.sprintf "subst_size_exp: bad SVar name encountered: %s" x))
  | (SHat sexp') -> (SHat (subst_size_exp sexp' i e))

let rec subst_size_of_ty (theta : size_ty) (i : string) (e : size_exp) : size_ty = 
  match theta with
  | TyCons(name, params, sexp) -> TyCons(name, params, subst_size_exp sexp i e)
  | TyArrow(doms, cod) -> TyArrow(List.map (fun ty -> subst_size_of_ty ty i e) doms, subst_size_of_ty cod i e)

(* returns the size expression of the type
NOTE: assumes first-order *)
let size_exp_of_ty ty =
  match ty with
  | TyCons(_, _, sexp) -> sexp
  | _ -> raise (Util.Impossible (Format.sprintf "size_exp_of_ty: called on function: %s" (show_size_ty ty)))



(*********************** TYPE COMPARISON ******************************)

(* compare size_tys without size expression comparison *)
let rec is_same_flatty maybe target = 
  match (maybe, target) with
  | (TyCons (name1, _, _), TyCons (name2, _, _)) ->
    name1 = name2
    (* && sexp1 $<= sexp2 allows size subtyping *)
  | (TyArrow (doms1, cod1), TyArrow (doms2, cod2)) -> 
    List.length doms1 = List.length doms2
    && List.for_all2 is_same_flatty doms2 doms1 (* flipped for subtyping *)
    && is_same_flatty cod1 cod2
  | (_, _) -> false


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

(* unify function with its target by making size variable substitution to the function *)
and ty_unify_producer maybe target =
  match maybe with
  | TyArrow (doms, cod) -> 
    if is_same_ty cod target then (* this part doesn't care about size variable names*)
    (match unify_size_exp (size_exp_of_ty cod) (size_exp_of_ty target) with (* usage of size_exp_of_ty constrains this to first-order*)
      | UAny -> None (* TODO: check if arguments are available *)
      | USome (iexp, kexp) -> 
        let doms_st = List.map (fun dom -> subst_size_of_ty dom iexp kexp) doms in
      Some (TyArrow(doms_st, subst_size_of_ty cod iexp kexp))
      | UNone -> None)
      else None
  | _ -> None
(* if `maybe` is a function type that produces target AND are arguments available in the environment,
  returns size-substituted `maybe` 
  NOTE: NOT higher order*)
and ty_produces maybe target (env : env) =
  match ty_unify_producer maybe target with
  | Some TyArrow (doms, cod) -> 
    if List.for_all (fun dom -> (List.exists (fun var -> reachable var.var_ty dom env) env)) doms
      then Some (TyArrow(doms, cod))
      else None
  | _ -> None
and reachable maybe t env = is_same_ty maybe t || Option.is_some (ty_produces maybe t env)

(********************** CONSTRUCTORS **********************************)

(* get the constructors of a given type *)
let rec lookup_constructors (cons : data_constructor_t) (ty : size_ty) : data_info =
  match cons with
  | [] -> (match ty with
    | TyCons (name, _, _) -> raise (Util.Impossible (Format.sprintf "lookup_constructors: can't find: %s" name))
    | TyArrow _ ->  raise (Util.Impossible "lookup_constructors: called with function type"))
  | {ty=t; constructors=constructors} :: rst ->
    if is_same_flatty t ty then {ty=t; constructors=constructors} else lookup_constructors rst ty

(*********************** MORE HELPERS *********************************)

(* TODO: generalize size_up 
for now, cheat and assume substitution [k:=khat]*)
let size_up_ty ty = subst_size_of_ty ty "k" (SHat (SVar "k"))

(************************ SIZE ALGEBRA ***********************************)
(* Pseudocode for reachable, produces. sigma is the target type

reachable sigma t = is_same_ty t sigma || (produces sigma t)
produces sigma t = 
  TyArrow(doms, cod) = t
  is_same_ty cod sigma && (* this part doesn't care about size variable names*)
  List.for_all (fun dom -> 
        let dom_st = subst_size dom (unify t sigma) (* SEE BELOW: substitute size variable in the domain with target size variables *)
        exists (x:t) in Gamma . reachable dom_st t)
    doms

Example: 
  sigma = Nat khat (* notice this uses a fresh size variable k. the stuff we've created during generation
  is also k-sized. the library functions are i-sized, and will need substitution *)
  Gamma = [(x : Nat khat); (x' : Nat k); (Zero : forall i, Nat ihat); (Succ : forall i, Nat i -> Nat ihat); (id : forall i, Nat i -> Nat i)]

  (* both (id x) and (Succ x') are ways to produce sigma: *)
  produces sigma id = 
    let dom_st = subst_size (Nat i) i **khat** = Nat khat
    exists (x : Nat khat) in Gamma . reachable (Nat khat) (Nat khat)

  produces sigma Succ = 
    let dom_st = subst_size (Nat i) i **k** = Nat k 
    exists (x' : Nat k) in Gamma . reachable (Nat k) (Nat k) 
  
  unify i khat = (i, khat)
  unify ihat khat = (i, k) (* note that (ihat, khat) isn't the BEST answer because it doesn't tell you how to substitute occurences of i sans hat*)

    Inf1: if we're trying to produce something of size Inf but we want to call a recursive function,
    we still need to provide SOME sized value of the same datatype, but we don't care what. so we
    could just pick one of the compatible available sized types in the context
    this clause will never happen in the CASE rule below because we're always picking something sized for the head of the CASE
    but it may happen for other scenarios. for now assume we're just going generate size preserving function
  *)
