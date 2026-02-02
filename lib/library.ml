open Exp

(* Common sexps/types *)

let i = SVar "i"
let ihat = SHat i
let k = SVar "k"
let j = SVar "j"
let khat = SHat k
let jhat = SHat j
let tX = TyVar("X",Inf)
let tY = TyVar("Y",Inf)

(* Types used in gen_lang files (these are \mathcal{D}, the set of datatypes) *)
let (-->) ty_params ty_body = TyArrow (Q i, ty_params, ty_body) (* all constructors and std_lib are quantified over i*)

let tBool = TyCons ("bool", [], ihat) (* technically bools are unsized but this simplifies substitution *)
let tNat sexp = TyCons ("int", [], sexp)
let tList sexp ty = TyCons ("list", [ty], sexp)

(* function signatures used by main for testing/debugging *)

let nat_func1 = (TyArrow(Q k, [tNat k; tNat Inf], tNat Inf)) (* ∀k. Natk → Nat → Nat*)
let nat_func2 = (TyArrow(Q k, [tNat k; tNat Inf], tNat k)) (* ∀k. Natk → Nat → Natk*)
let nat_func3 = TyArrow (Q k, [tNat k],
                              TyArrow(Q j, [tNat j], tNat Inf)) (* ∀k. Natk → (∀ j. Natj → Nat) *)
let list_func1 = TyArrow(Q k, [tList k (tNat Inf)], tList k (tNat Inf)) (* ∀k. Listk Nat → Listk Nat*)
let list_func2 = TyArrow(Q k, [tList k (tNat Inf)], tList Inf (tNat Inf)) (* ∀k. Listk Nat → List Nat*)
let list_func3 = TyArrow(Q k, [tList k (tNat Inf)], (tNat Inf)) (* ∀k. Listk Nat → Nat*)




(**********************************************)
(* module type shared among language backends *)
module type Language = sig
    val data_constructors : data_constructors_t 
    val std_lib : (string * size_ty) list
    val printer : exp list list -> string -> string
  end;;