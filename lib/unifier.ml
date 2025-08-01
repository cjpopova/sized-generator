open Exp
open TypeUtil

(*
The following code (for sizes) has been moved to TypeUtil. i am leaving this for notes



I will use the style of
https://www.cs.cornell.edu/courses/cs3110/2011sp/Lectures/lec26-type-inference/type-inference.htm

*)

(* invariant for substitutions: *)
(* no id on a lhs occurs in any size_ty earlier in the list *)
type substitution = (string * size_ty) list
[@@deriving show]

(* substitute size_ty s for all occurrences of variable x in size_ty t 
t = [x:=s] (* notice the argument order is flipped to make recursion simpler *)
*)
let rec subst (s : size_ty) (x : string) (t : size_ty) : size_ty =
  match t with
  | TyVar (y, _) -> if x = y then s else t (* NOTE: deal with size_ty *)
  | TyCons (name, params, sexp) -> TyCons(name, List.map (subst s x) params, sexp)
  | TyArrow(q, params, cod) -> TyArrow(q, List.map (subst s x) params, subst s x cod)

(* apply a substitution right to left *)
let apply (s : substitution) (t : size_ty) : size_ty =
  List.fold_right (fun (x, u) -> subst u x) s t

(* this is a variant of the unification algorithm based on the following invariants:
- TyVars only appear on one side (because targets are never polymorphic), so circular references cannot occur
- TyVars start on the left but can appear on either side because of the subtype-flipping done to domains

TODO: write better error messages when done
*)



(*************************************************************)

(* now we add sizes. *)

(* old version that is one-sided somehow*)
(* let rec sexp_unifier sexp target : string * size_exp = 
    match (sexp, target) with
    | Inf       , Inf        -> ("", Inf) (* hack*)
    | SHat iexp , Inf        -> sexp_unifier iexp Inf
    | SVar i    , _          -> (i, target) (* note that target can be arbitrarily large *)
    | SHat iexp , SHat kexp  -> sexp_unifier iexp kexp
    | _         , _          -> raise (Util.Impossible (Format.sprintf "size unification failed on %s, %s" (show_size_exp sexp) (show_size_exp target))) *)

let rec sexp_unifier sexp target : size_exp * size_exp = 
    match (sexp, target) with
    | _, Inf | Inf, _ -> sexp, target (* s ⊑ ∞, including ∞^ ⊑ ∞ *)
    | SVar _, _ -> (sexp, target) (* note that target can be arbitrarily large *)
    | SHat iexp , SHat kexp  -> sexp_unifier iexp kexp
    | _         , _          -> raise (Util.Impossible (Format.sprintf "size unification failed on %s, %s" (show_size_exp sexp) (show_size_exp target)))


(*maintain two lists for substitution: *)

type substitution_hat = {
  types : substitution; (* should we ignore the sizes inside here?*)
  sizes : (size_exp * size_exp) list
}
[@@deriving show]

(* some helpers *)
let substitution_hat_combine (s1 : substitution_hat) (s2 : substitution_hat) : substitution_hat = 
  { types=s1.types @ s2.types;
    sizes=s1.sizes @ s2.sizes}

(* flip the pairs in the size substitution for subtyping *)
let substitution_hat_flip (s : substitution_hat) : substitution_hat = 
  let flip ll = List.map (fun (x,y) -> (y,x)) ll in
  { types=s.types; sizes=flip s.sizes } (* TODO: don't flip types??? i just made a bad data representation *)


let apply_hat (s : substitution_hat) (t : size_ty) : size_ty = 
  let t' = List.fold_right (fun (x, u) -> subst u x) s.types t in (* fold in type substitution (MUST be first to match correctly)*)
  List.fold_right (fun (i, sexp) u -> if i = Inf then u else subst_size_of_ty u i sexp) s.sizes t' (* fold in size substitution, skipping [Inf:=_] *)

let rec unify_one_hat maybe target : substitution_hat  = 
  match (maybe, target) with
  | TyVar (x, sexp), _ ->
    (* TODO what if we check, but don't keep, the size unification? since it should be subsumed by the type unification 
      this would would probably be fine as long as we don't have size-carrying contents*)
    {types=[(x, target)]; sizes=[sexp_unifier sexp (size_exp_of_ty target)]}  
  | _, TyVar (x, sexp) ->
    {types=[(x, maybe)]; sizes=[sexp_unifier (size_exp_of_ty maybe) sexp]}  
  | TyCons (name1, params1, sexp1), TyCons (name2, params2, sexp2) ->
    if name1 = name2 (* this is where type-subtyping would go ... if we had any *)
      then let param_subst = unify_hat (List.combine params1 params2) in
      (* we throw out param_subst.size  because we shouldn't have sizes inside containers *)
        {param_subst with sizes = [sexp_unifier sexp1 sexp2] } (* {param_subst with sizes = sexp_unifier sexp1 sexp2 :: param_subst.sizes} *)
      else raise (Util.Impossible "names don't match") (* TODO: this error will actually be raised and needs to be caught by this function's callers*)
  | TyArrow (_, doms1, cod1), TyArrow (_, doms2, cod2) -> 
    if List.length doms1 = List.length doms2
      then (* TODO: higher-order b.s.: unify the codomain, applying that substitution, then unifying and flipping the domains *)
        let t = unify_one_hat cod1 cod2 in
        let doms2 = List.map (apply_hat t) doms2 in
        let doms1 = List.map (apply_hat t) doms1 in
        substitution_hat_combine (substitution_hat_flip (unify_hat (List.combine doms2 doms1))) t
      else raise (Util.Impossible "help3")
  | _, _ -> raise (Util.Impossible "help4")

and unify_hat (s : (size_ty * size_ty) list) : substitution_hat =
  match s with 
  | [] -> { types=[]; sizes=[] }
  | (x, y) :: t ->
      let t2 = unify_hat t in
      let t1 = unify_one_hat (apply_hat t2 x) (apply_hat t2 y) in (* apply existing substitution into the current term *)
      substitution_hat_combine t1 t2