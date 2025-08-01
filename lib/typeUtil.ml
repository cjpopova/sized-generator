open Exp;;

(*
There are 2 main algorithms for type stuff implemented in this file:
- size subtype: does this monomorphic variable subtype hole_ty? do their sizes have the same base size variable (|_s_|) and subtype?
- producer unification: does this polymorphic function produce something that unifies with hole_ty?

Their usage:
-------------------------------------------------------------
var_steps                               is_size_subtype
APPREF/fresh_call_ref_step              find θ such that T = θ[k := α] using safe_subst
APP/INDIR                               producer unification 
APP/recur                               producer unification w/ reachable 
APP/std_lib                             producer unification
base_std_lib_steps                      is_size_subtype
RECUR_constructors                      producer unification w/ reachable 
BASE_constructors                       producer unification (reachable is not necessary because there should be no arguments)
-------------------------------------------------------------
*)

(******************* SUBSTITUTION & QUANTIFICATION ****************************)

(* e1[e2:=e3] *)
let rec subst_size_exp e1 e2 e3 : size_exp = 
  if e1=e2 then e3
  else match e1 with
  | SHat e1' -> SHat (subst_size_exp e1' e2 e3)
  | _ -> e1

let rec subst_size_of_ty (theta : size_ty) (e1 : size_exp) (e2 : size_exp) : size_ty = 
  match theta with
  | TyVar (name, sexp) -> TyVar(name, subst_size_exp sexp e1 e2)
  | TyCons(name, params, sexp) -> TyCons(name, params, subst_size_exp sexp e1 e2)
  | TyArrow(q, doms, cod) -> 
    TyArrow(q, List.map (fun ty -> subst_size_of_ty ty e1 e2) doms, subst_size_of_ty cod e1 e2)

(* returns the size expression of the type
NOTE: assumes first-order *)
let size_exp_of_ty ty =
  match ty with
  | TyVar (_, sexp) -> sexp
  | TyCons(_, _, sexp) -> sexp
  | _ -> raise (Util.Impossible (Format.sprintf "size_exp_of_ty: called on: %s" (show_size_ty ty)))

(*** SPECIALTY HELPERS ***)

(* e1[e2:=e3] 
special variant of size substitution for APPREF rule that guards against invalid substitutions *)
let rec safe_subst_size_exp e1 e2 e3 : size_exp option = 
  if e1=e2 then Some e3 
  else match e1 with
  | SVar _ -> None
  | Inf -> Some e1
  | SHat e1' -> match safe_subst_size_exp e1' e2 e3 with
    | Some r -> Some (SHat r)
    | None -> None

(* given a function ∀k.t, return function ∀k.t[k:=khat]*)
let size_up_ty ty = 
  match ty with
  | TyArrow(Q k, _, _) -> subst_size_of_ty ty k (SHat k)
  | _ -> raise (Util.Impossible (Format.sprintf "cannot size up non quantified-function: %s" (show_size_ty ty)))

(* remove the quantifier from a function type*)
let unquantify_ty ty = 
  match ty with
  | TyArrow(Q k, doms, cod) -> TyArrow(U k, doms, cod)
  | _ -> raise (Util.Impossible (Format.sprintf "cannot unquantify non-function: %s" (show_size_ty ty)))

(* replace the size expression on the type
NOTE: first-order; higher-order version might use subst instead *)
let resize_ty ty sexp =
  match ty with
  | TyCons(name, ty_params, _) -> TyCons(name, ty_params, sexp)
  | _ -> raise (Util.Impossible (Format.sprintf "resize_ty: called on: %s" (show_size_ty ty)))


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
  | _, TyVar _ -> true (* because this size_exp on TyVar should be Inf, this is always true *)
  | (TyCons (name1, params1, sexp1), TyCons (name2, params2, sexp2)) ->
    name1 = name2 
    && List.for_all2 (fun t1 t2 -> gen_compare_ty t1 t2 size_comp) params1 params2
    && size_comp sexp1 sexp2
  | (TyArrow (_, doms1, cod1), TyArrow (_, doms2, cod2)) -> 
    List.length doms1 = List.length doms2
    && List.for_all2 (fun x y -> gen_compare_ty x y size_comp) doms2 doms1 (* flipped for subtyping *)
    && gen_compare_ty cod1 cod2 size_comp
  | (_, _) -> false

let is_flat_subtype_ty maybe target = (* compare size_tys without size expression comparison *)
  gen_compare_ty maybe target (fun _ _ -> true)
let is_size_subtype_ty maybe target = (* use size subtyping *)
  gen_compare_ty maybe target (fun sexp1 sexp2 -> sexp1 $<= sexp2)

(******************* TYPE UNIFICATION ****************************)
(* Algorithm based on https://www.cs.cornell.edu/courses/cs3110/2011sp/Lectures/lec26-type-inference/type-inference.htm *)

(* maintain two lists for substitution:
- the strings in types correspond to names of TyVars
- types supercede sizes: since types carry sizes, type substitution occurs before size substitution
- possible invariant: Inf never appears on the LHS of pair?
*)
type substitution_hat = {
  types : (string * size_ty) list;
  sizes : (size_exp * size_exp) list
}
[@@deriving show]
let rec sexp_unifier sexp target : size_exp * size_exp = 
    match (sexp, target) with
    | Inf, Inf -> Inf, Inf
    | SHat i, Inf -> sexp_unifier i Inf
    | SVar _, _ -> (sexp, target)
    | SHat iexp , SHat kexp  -> sexp_unifier iexp kexp
    | _         , _          -> raise (Util.Impossible (Format.sprintf "size unification failed on %s, %s" (show_size_exp sexp) (show_size_exp target)))

(* merge two substitutions *)
let substitution_hat_combine (s1 : substitution_hat) (s2 : substitution_hat) : substitution_hat = 
  { types=s1.types @ s2.types;
    sizes=s1.sizes @ s2.sizes}

(* flip the pairs in the size substitution for subtyping *)
let substitution_hat_flip (s : substitution_hat) : substitution_hat = 
  let flip ll = List.map (fun (x,y) -> (y,x)) ll in
  { types=s.types; sizes=flip s.sizes } (* NOTE: don't flip types??? i just made a bad data representation *)

(* type level substitution *)
let rec subst (s : size_ty) (x : string) (t : size_ty) : size_ty =
  match t with
  | TyVar (y, _) -> if x = y then s else t
  | TyCons (name, params, sexp) -> TyCons(name, List.map (subst s x) params, sexp)
  | TyArrow(q, params, cod) -> TyArrow(q, List.map (subst s x) params, subst s x cod)

let apply_hat (s : substitution_hat) (t : size_ty) : size_ty = 
  let t' = List.fold_right (fun (x, u) -> subst u x) s.types t in (* fold in type substitution *)
  List.fold_right (fun (i, sexp) u -> if i = Inf then u else subst_size_of_ty u i sexp) s.sizes t' (* fold in size substitution, skipping substitutions of the form [Inf:=_] *)

let rec unify_one_hat maybe target : substitution_hat  = 
  match (maybe, target) with
  | TyVar (x, _), _ -> {types=[(x, target)]; sizes=[]}  (* size unification is subsumed by type unification. also TyVar's sexp is always Inf *)
  | _, TyVar (x, _) -> {types=[(x, maybe)]; sizes=[]}  
  | TyCons (name1, params1, sexp1), TyCons (name2, params2, sexp2) ->
    if name1 = name2 (* this is where type-subtyping would go ... if we had any *)
      then let param_subst = unify_hat (List.combine params1 params2) in
      (* we throw out param_subst.size because we shouldn't have sizes inside containers *)
        {param_subst with sizes = [sexp_unifier sexp1 sexp2] } (* {param_subst with sizes = sexp_unifier sexp1 sexp2 :: param_subst.sizes} *)
      else raise (Util.UnificationError "names don't match")
  | TyArrow (_, doms1, cod1), TyArrow (_, doms2, cod2) -> 
    if List.length doms1 = List.length doms2
      then (* NOTE: higher-order b.s.: unify the codomain, applying that substitution, then unifying and flipping the domains *)
        let t = unify_one_hat cod1 cod2 in
        let doms2 = List.map (apply_hat t) doms2 in
        let doms1 = List.map (apply_hat t) doms1 in
        substitution_hat_combine (substitution_hat_flip (unify_hat (List.combine doms2 doms1))) t
      else raise (Util.UnificationError "help3")
  | _, _ -> raise (Util.UnificationError "help4")

and unify_hat (s : (size_ty * size_ty) list) : substitution_hat =
  match s with 
  | [] -> { types=[]; sizes=[] }
  | (x, y) :: t ->
      let t2 = unify_hat t in
      let t1 = unify_one_hat (apply_hat t2 x) (apply_hat t2 y) in (* apply existing substitution into the current term *)
      substitution_hat_combine t1 t2

(******************* UNIFICATION ****************************)

(* Pseudocode

ty_unify_producer
  (f : _ . τ ... -> θ) (* unquantified *)
  (hole : T)
  : size_ty option = If θ ⊑ T then Some f else None
  
ty_unify_producer
  (f : ∀i. τ ... -> θ) (* quantified *)
  (hole : T)
  : size_ty option =
  if ∃ substitution σ s.t. θ σ ⊑ T (UNIFICATION)
    then Some (∀i. τ ... σ -> θ σ)
    else None

ty_produces f T Γ = 
  let f' = ty_unfiy_producer f T
  if ∀ dom ∈ (doms f') . reachable dom
    then Some f' 
    else None

reachable T Γ : bool=
  ∃ x:τ ∈ Γ . 
    τ ⊑ T
    ∨ ∃ f:τ ∈ Γ . produces f T Γ
*)

(******************************* PRODUCERS *******************************)

(* unify function with its target, and return the substituted function*)
let rec ty_unify_producer (maybe : size_ty) (target : size_ty) : size_ty option =
  match maybe with
  | TyArrow (U _, _, cod) -> 
  (* Unquantified - no substitution required (generated recursive functions are never type-polymorphic,
  and we can't requantify the size, so subtyping works here) *)
  if is_size_subtype_ty cod target then Some maybe else None
  | TyArrow (Q q, doms, cod) -> (* Quantified *)
    (try
      let s = unify_one_hat cod target in
      let doms_st = List.map (fun dom -> apply_hat s dom) doms in  (* apply substitution *)
        let cod_st =  apply_hat s cod in
        Some (TyArrow(Q q, doms_st, cod_st))
    with _ -> None)
  | _ -> None
(* if `maybe` is a function type that produces target AND are arguments available in the environment,
  returns size-substituted `maybe` 
  NOTE: NOT higher order*)
and ty_produces (maybe : size_ty) (target : size_ty) (env : env) : size_ty option =
  let smaller_env = List.filter (fun v -> v.var_ty != maybe) env in (* NOTE: set comprehension would be more efficient *)
  match ty_unify_producer maybe target with
  | Some TyArrow(_, doms, _) as t-> 
    if List.for_all (fun dom -> reachable dom smaller_env) doms
      then t
      else None
  | _ -> None
and reachable t env = List.exists 
  (fun {var_ty=var_ty; _} -> is_size_subtype_ty var_ty t || Option.is_some (ty_produces var_ty t env))
  env

(********************** CONSTRUCTORS **********************************)

(* get the constructors of a given type *)
let rec lookup_constructors (cons : data_constructors_t) (ty : size_ty) : func_list =
  match cons with
  | [] -> (match ty with
    | TyCons (name, _, _) -> raise (Util.Impossible (Format.sprintf "lookup_constructors: can't find: %s" name))
    | TyArrow _ -> []
    | TyVar(name,_)-> raise (Util.Impossible (Format.sprintf "lookup_constructors: called on TyVar: %s" name)))
  | flst :: rst ->
    match flst with 
    | (_, TyArrow(_, _, t)) :: _ ->
      if is_flat_subtype_ty ty t then flst else lookup_constructors rst ty (* 7/29 im going to leave this bc idk how to reprogram it *)
    | _ -> []