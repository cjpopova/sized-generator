open Exp
open Library
open DebugLibrary
open TypeUtil
open Unifier

(********************************** SETUP **********************************)

(* we do a little cheating with printers *)

type sexp_pair = size_exp * size_exp
[@@deriving show]
let sexppair = Alcotest.testable pp_sexp_pair (=)

type size_ty_option = size_ty option
[@@deriving show]
let sizetyopt = Alcotest.testable pp_size_ty_option (=)

let subst_hat = Alcotest.testable pp_substitution_hat (=)

(********************************** TESTS **********************************)

(* wishlist 
- copy the exact examples from typeUtil documentation 
- unification & subst at the type level
*)

let test_unify_size_exp () = 
  let input1 = (SHat Inf), Inf in (* ∞^ ⊑ ∞ *)
  let expected1 = (SHat Inf), Inf in

  let test_list = [input1, expected1] in
  List.fold_left (fun _ ((i1, i2),e) -> Alcotest.(check sexppair) "" e (unify_size_exp i1 i2))
    ()
    test_list

(*********** PRODUCERS ***********)

let test_mono_producer_unification () = 
  (* f, □ *)
  let input0 = [tNat i] --> tNat i, tNat khat in (* id : ∀i . i -> i, Nat k^   ~>  k^ -> k^ *)
  let expected0 = Some ([tNat khat] --> tNat khat) in
  
  let input1 = [tNat i] --> tNat ihat, tNat khat in (* succ : ∀i . i -> i^, Nat k^   ~>  k -> k^ *)
  let expected1 = Some ([tNat k] --> tNat khat) in

  (* TODO this one fails because the UAny case doesn't resize the codomain to Inf *)
  (* let input2 = [tNat i] --> tNat ihat, tNat Inf in (* succ : ∀i . i -> i^, Nat Inf   ~>  Inf -> Inf *)
  let expected2 = Some ([tNat Inf] --> tNat Inf) in *)

  let input3 = TyArrow(None, [tNat k], tNat k), tNat k in (* foo : k -> k, k  ~>   k -> k *)             (* unquantified recursive call *)
  let expected3 = Some (TyArrow(None, [tNat k], tNat k)) in

  let test_list = [
    input0, expected0;
    input1, expected1;
    (* input2, expected2; *)
    input3, expected3;
    ] in
  List.fold_left (fun _ ((maybe, target),e) -> Alcotest.(check sizetyopt) "" e (ty_unify_producer maybe target))
    ()
    test_list

let test_mono_reachable_producer () = 
  (* f, □, Γ *)
  let input0 = [tNat i] --> tNat i, tNat khat, [tNat k] in (* id : ∀i . i -> i, Nat k^, tNat k   ~>  k^ -> k^ *)
  let expected0 = Some ([tNat khat] --> tNat khat) in

  let input1 = TyArrow(None, [tNat k], tNat k), tNat Inf, [tNat khat] in (* foo : k -> k, _, khat  ~>   fail *)      (* unquantified recursive call on too-big argument*)
  let expected1 = None in

  let test_list = [
    input0, expected0;
    input1, expected1;
    ] in
  List.fold_left (fun _ ((maybe, target, ty_env),e) -> 
    let env = List.map (fun ty -> new_var ty) ty_env in (* turn types into vars for environment *)
    Alcotest.(check sizetyopt) "" e (ty_produces maybe target env))
    ()
    test_list

(*********** NEW UNIFIER MODULE ***********)

let test_unify_one_hat () = 
  (* τ, □ *)
  let input0 = tList ihat tX, tList khat tBool in (* List i^ (X ∞), List k^ (Bool ∞) ~> [X=Bool, i=k]*)
  let expected0 = { types=["X", tBool]; sizes=[i, k]} in

  let test_list = [
    input0, expected0;
    ] in
  List.fold_left (fun _ ((maybe, target), e) -> Alcotest.(check subst_hat) "" e (unify_one_hat maybe target))
    ()
    test_list

let test_HO_unify_one_hat () = 
  (* τ, □ *)
  let input1 = [tNat Inf] --> tNat Inf, [tNat i] --> tNat i in
  let expected1 = { types=[]; sizes=[Inf, i; Inf, i]} in (* repeated but whatever*)

  (* to make this go thru, need to change subst_size_exp to not reject substitutions ... 
  but we must reject invalid substitutions for APPREF rule
  maybe just need a new version of subst *)
  let input2 = [tNat k] --> tNat k, [tNat i] --> tNat i in
  let expected2 = { types=[]; sizes=[i, i; k, i]} in 
 

  let test_list = [
    input1, expected1;
    input2, expected2;
    ] in
  List.fold_left (fun _ ((maybe, target), e) -> Alcotest.(check subst_hat) "" e (unify_one_hat maybe target))
    ()
    test_list

(*
withlist for polymorphic producer unification showing substitution on arguments
  list-ref : ∀ i . Nat ∞ -> List i (X ∞) -> (X ∞)           (* i have writte the infs explicitly on the list contents *)

  unify range (X ∞) with □      yields     X = Bool 
  so now we look for 2 arguments:
  □2 : Nat ∞
  □3 : List i (Bool ∞)


  cons : ∀ i . (X ∞) -> List i (X ∞) -> List i^ (X ∞)
*)

let () =
  let open Alcotest in
  run "Everything" [
      "unify_size_exp", [ test_case "unify_size_exp" `Quick test_unify_size_exp  ];
      "ty_unify_producer", [ 
        test_case "monomorphic producer"              `Quick test_mono_producer_unification;  
        test_case "monomorphic reachable producer"    `Quick test_mono_reachable_producer;
        ];
      "new unifier module", [ 
        test_case "unify hat: first order"            `Quick test_unify_one_hat;  
        test_case "unify hat: higher order"           `Quick test_HO_unify_one_hat;  
        ];
    ]