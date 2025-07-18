open Exp;;

(******************* SUBSTITUTION & QUANTIFICATION ****************************)

(* e1[e2:=e3] *)
let rec subst_size_exp e1 e2 e3 = 
  if e1=e2 then Some e3 
  else match e1 with
  | SVar _ -> None
  | Inf -> Some e1
  | SHat e1' -> match subst_size_exp e1' e2 e3 with
    | Some r -> Some (SHat r)
    | None -> None

let subst_size_exp_err e1 e2 e3 = 
  match subst_size_exp e1 e2 e3 with
  | Some e4 -> e4
  | None -> raise (Util.Impossible (Format.sprintf "subst_size_exp failed on: %s %s %s" 
                                    (show_size_exp e1)
                                    (show_size_exp e2)
                                    (show_size_exp e3)))
let rec subst_size_of_ty (theta : size_ty) (e1 : size_exp) (e2 : size_exp) : size_ty = 
  match theta with
  | TyCons(name, params, sexp) -> TyCons(name, params, subst_size_exp_err sexp e1 e2)
  | TyArrow(q, doms, cod) -> 
    TyArrow(q, List.map (fun ty -> subst_size_of_ty ty e1 e2) doms, subst_size_of_ty cod e1 e2)

(* returns the size expression of the type
NOTE: assumes first-order *)
let size_exp_of_ty ty =
  match ty with
  | TyCons(_, _, sexp) -> sexp
  | _ -> raise (Util.Impossible (Format.sprintf "size_exp_of_ty: called on function: %s" (show_size_ty ty)))

(* given a function ∀k.t, return function ∀k.t[k:=khat]*)
let size_up_ty ty = 
  match ty with
  | TyArrow(Some k, _, _) -> subst_size_of_ty ty k (SHat k)
  | _ -> raise (Util.Impossible (Format.sprintf "cannot size up non quantified-function: %s" (show_size_ty ty)))

(* remove the quantifier from a function type*)
let unquantify_ty ty = 
  match ty with
  | TyArrow(_, doms, cod) -> TyArrow(None, doms, cod)
  | _ -> raise (Util.Impossible (Format.sprintf "cannot unquantify non-function: %s" (show_size_ty ty)))

(* replace the size expression on the type
NOTE: first-order; higher-order version might use subst instead *)
let resize_ty ty sexp =
  match ty with
  | TyCons(name, ty_params, _) -> TyCons(name, ty_params, sexp)
  | _ -> raise (Util.Impossible (Format.sprintf "resize_ty: called on function: %s" (show_size_ty ty)))


(*********************** TYPE COMPARISON ******************************)

(* size_exp comparison*)
let rec ($<=) (sexp1 : size_exp) (sexp2 : size_exp) : bool = 
    match sexp1, sexp2 with
  | SVar a, SVar b -> a = b (* variable names must match *)
  | SVar _, SHat e -> sexp1 $<= e
  | _, Inf -> true
  | SHat e1, SHat e2 -> e1 $<= e2
  | _, SHat e2 -> sexp1 $<= e2
  | _ -> false

(* type comparison, parametrized by size comparison *)
let rec gen_compare_ty maybe target (size_comp : size_exp -> size_exp -> bool) = 
  match (maybe, target) with
  | (TyCons (name1, _, sexp1), TyCons (name2, _, sexp2)) ->
    name1 = name2
    && size_comp sexp1 sexp2
  | (TyArrow (_, doms1, cod1), TyArrow (_, doms2, cod2)) -> 
    List.length doms1 = List.length doms2
    && List.for_all2 (fun x y -> gen_compare_ty x y size_comp) doms2 doms1 (* flipped for subtyping *)
    && gen_compare_ty cod1 cod2 size_comp
  | (_, _) -> false

let is_same_flatty maybe target = (* compare size_tys without size expression comparison *)
  gen_compare_ty maybe target (fun _ _ -> true)
let is_size_subtype_ty maybe target = (* use size subtyping *)
  gen_compare_ty maybe target (fun sexp1 sexp2 -> sexp1 $<= sexp2)

(******************* UNIFICATION ****************************)

(* Pseudocode (explained top down):

reachable σ Γ =
  ∃ x:τ ∈ Γ . τ ⊑ σ
  ∨ ∃ f:τ ∈ Γ . produces f σ Γ

ty_produces
  f : _ . \tau ... -> θ (* unquantified *)
  hole : T =
If θ ⊑ T   &&   ∀ t ∈ ty_params . reachable t (Γ \ f)
  then Some (_ . ty_params -> θ)
  else None
  
ty_produces
  f : ∀k. τ ... -> θ (* quantified *)
  hole : T =
Find α s.t. θ[k:=α] ⊑ T (* UNIFICATION *)
Let ty_params = τ ... [k:=α]
If ∀ t ∈ ty_params . reachable t (Γ \ f)
then Some (∀k. ty_params -> θ[k:=α])
else None

unify θ T = α





Examples of ty_produces for quantified functions: 
  T = Nat khat (* notice this uses a fresh size variable k. the stuff we've created during generation is also k-sized. the library functions are i-sized, and will need substitution *)
  Γ = [(x : Nat khat); (x' : Nat k); (Zero : ∀i. Nat ihat); (Succ : ∀i. Nat i -> Nat ihat); (id : ∀i. Nat i -> Nat i)]
  
  Both (id x) and (Succ x') are ways to produce T:

  ty_produces id T = 
    α = khat
    ty_params = i[i:=khat] = khat

  ty_produces Succ T = 
    α = k 
    ty_params = i[i:=k] = k

Another example with Inf:
  T = Inf
  ty_produces id T = 
    α = Any
    ty_params = i[i:=Inf] = Inf

  Since anything can produce Inf size, the size of the arguments also reduces to Inf.
  

  

Unification examples:
  unify i khat = (i, khat)
  unify ihat khat = (i, k)
  unify ihat k = None (result ihat would be too large / we can't deconstruct k)
 
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

(* unify function with its target by making size variable substitution to the function *)
let rec ty_unify_producer maybe target =
  match maybe with
  | TyArrow (None, _, cod) -> (* Unquantified *)
    if is_size_subtype_ty cod target 
      then Some maybe
      else None
  | TyArrow (Some k, doms, cod) -> (* Quantified *)
    if is_same_flatty cod target then (* before we check sizes, check the rest of the codomain type  *)
    (match unify_size_exp (size_exp_of_ty cod) (size_exp_of_ty target) with (* unify the size of the codomain*)
      | UAny -> None (* TODO: check if arguments are available *)
      | USome (iexp, kexp) ->
        let doms_st = List.map (fun dom -> subst_size_of_ty dom (SVar iexp) kexp) doms in
        let cod_st =  subst_size_of_ty cod (SVar iexp) kexp in
        Some (TyArrow(Some k, doms_st, cod_st))
      | UNone -> None)
      else None
  | _ -> None
(* if `maybe` is a function type that produces target AND are arguments available in the environment,
  returns size-substituted `maybe` 
  NOTE: NOT higher order*)
and ty_produces maybe target (env : env) =
  let smaller_env = List.filter (fun v -> v.var_ty != maybe) env in (* NOTE: set comprehension would be more efficient *)
  match ty_unify_producer maybe target with
  | Some TyArrow(q, doms, cod) -> 
    if List.for_all (fun dom -> reachable dom smaller_env) doms
      then Some (TyArrow(q, doms, cod))
      else None
  | _ -> None
and reachable t env = List.exists 
  (fun {var_ty=var_ty; _} -> is_size_subtype_ty var_ty t || Option.is_some (ty_produces var_ty t env))
  env

(********************** CONSTRUCTORS **********************************)

(* get the constructors of a given type *)
let rec lookup_constructors (cons : data_constructor_t) (ty : size_ty) : data_info =
  match cons with
  | [] -> (match ty with
    | TyCons (name, _, _) -> raise (Util.Impossible (Format.sprintf "lookup_constructors: can't find: %s" name))
    | TyArrow _ ->  raise (Util.Impossible "lookup_constructors: called with function type"))
  | {ty=t; constructors=constructors} :: rst ->
    if is_same_flatty t ty then {ty=t; constructors=constructors} else lookup_constructors rst ty