open Exp
open Library
open TypeUtil

(********************************** SETUP **********************************)

let tBoolInf = TyCons ("Bool", [], Inf)

(* we do a little cheating with printers to generate testable types *)

type sexp_opt = size_exp option
[@@deriving show]
let sexpopt = Alcotest.testable pp_sexp_opt (=)

type sexp_pair = size_exp * size_exp
[@@deriving show]
let sexppair = Alcotest.testable pp_sexp_pair (=)

type size_ty_option = size_ty option
[@@deriving show]
let sizetyopt = Alcotest.testable pp_size_ty_option (=)

let sizety = Alcotest.testable pp_size_ty (=)

let subst_hat = Alcotest.testable pp_substitution_hat (=)

type sexp_list = size_exp list
[@@deriving show]
let sexplist = Alcotest.testable pp_sexp_list (=)


type sizety_list = size_ty list
[@@deriving show]
let sizetylist = Alcotest.testable pp_sizety_list (=)


(********************************** TESTS **********************************)

(*********** SUBSTITUTION ***********)
let test_subst_size_of_ty () = 
  (* e1[e2:=e3] *)
  let input1 = [tNat i] --> tNat ihat, i, Inf in (* succ[i/∞] = ∞ --> ∞^ *)
  let expected1 = [tNat Inf] --> tNat (SHat Inf) in

 let test_list = [
    input1, expected1;
    ] in
  List.iteri (fun n ((i1, i2, i3),e) -> Alcotest.(check sizety) (string_of_int n) e (subst_size_of_ty i1 i2 i3))
    test_list

let test_safe_subst_size_exp () = 
  (* e1[e2:=e3] *)
  let input1 = ihat, i, k in (* i^[i/k] = k^*)
  let expected1 = Some khat in

  let input2 = i, ihat, k in (* i[i^/k] = FAIL *)
  let expected2 = None in

  let input3 = i, Inf, k in (* i[∞/k] = FAIL. NOTE: this blocks you from using an inf-size variable in the APPREF rule, which is whatever *)
  let expected3 = None in

  let test_list = [
    input1, expected1;
    input2, expected2;
    input3, expected3;
    ] in
  List.iteri (fun n ((i1, i2, i3),e) -> Alcotest.(check sexpopt) (string_of_int n) e (safe_subst_size_exp i1 i2 i3))
    test_list

(*********** TYPE COMPARISON ***********)

let test_size_subtype () = 
  let input1 = tList i (tNat Inf), tList ihat (tNat Inf) in
  let expected1 = true in

  let input2 = tList i (tNat Inf), tList k (tNat Inf) in
  let expected2 = false in

  let input3 = tList i (tNat Inf), tList Inf (tNat Inf) in
  let expected3 = true in

  (* NOTE: add higher order case? *)

  let test_list = [
    input1, expected1;
    input2, expected2;
    input3, expected3;
    ] in
  List.iteri (fun n ((i1, i2),e) -> Alcotest.(check bool) (string_of_int n) e (is_size_subtype_ty i1 i2))
    test_list


(*********** TYPE UNIFICATION ***********)

let test_unify_size_exp () = 
  let input1 = (SHat Inf), Inf in
  let expected1 = Inf, Inf in

  let input2 = ihat, Inf in
  let expected2 = i, Inf in

  let input3 = ihat, khat in
  let expected3 = i, k in

  let test_list = [
    input1, expected1;
    input2, expected2;
    input3, expected3;
  ] in
  List.iteri (fun n ((i1, i2),e) -> Alcotest.(check sexppair) (string_of_int n) e (sexp_unifier i1 i2))
    test_list

    
(* see possible errors in typeUtil - these boil down to sexp_unifier or uninteresting errors from the rest of unify_hat*)
let test_unification_errors () = 
  let input1 = tList Inf (tNat Inf), tList i (tNat Inf) in (*List ∞, List i, ~> FAIL *)

  let test_list = [
    input1;
    ] in
  List.iteri (fun n (maybe, target) -> Alcotest.match_raises (string_of_int n)
    (function
      | Util.UnificationError _ -> true
      | _ -> false)
    (fun _ -> let _ = unify_one_hat maybe target in ()))
    test_list


let test_unify_one_hat () = 
  (* τ, □ *)
  let input0 = tList ihat tX, tList khat tBoolInf in (* List i^ (X ∞), List k^ (Bool ∞) ~> [X=Bool, i=k]*)
  let expected0 = { types=["X", tBoolInf]; sizes=[i, k]} in

  let input1 = tList ihat tX, tList Inf tBoolInf in (* List i^ (X ∞), List k^ (Bool ∞) ~> [X=Bool, i=k]*)
  let expected1 = { types=["X", tBoolInf]; sizes=[i, Inf]} in

  let test_list = [
    input0, expected0;
    input1, expected1;
    ] in
  List.iteri (fun n ((maybe, target), e) -> Alcotest.(check subst_hat) (string_of_int n) e (unify_one_hat maybe target))
    test_list

(* let test_HO_unify_one_hat () = 
  (* τ, □ *)
  let input1 = [tNat Inf] --> tNat Inf, [tNat i] --> tNat i in
  let expected1 = { types=[]; sizes=[Inf, i; Inf, i]} in (* repeated but whatever*)

  let input2 = [tNat k] --> tNat k, [tNat i] --> tNat i in
  let expected2 = { types=[]; sizes=[i, i; k, i]} in 

  let test_list = [
    input1, expected1;
    input2, expected2;
    ] in
  List.iteri (fun n ((maybe, target), e) -> Alcotest.(check subst_hat) (string_of_int n) e (unify_one_hat maybe target))
    test_list *)

(*
wishlist for polymorphic producer unification showing substitution on arguments
  list-ref : ∀ i . Nat ∞ -> List i (X ∞) -> (X ∞)           (* i have writte the infs explicitly on the list contents *)

  unify range (X ∞) with □      yields     X = Bool 
  so now we look for 2 arguments:
  □2 : Nat ∞
  □3 : List i (Bool ∞)


  cons : ∀ i . (X ∞) -> List i (X ∞) -> List i^ (X ∞)
*)

(*********** PRODUCERS ***********)

let test_mono_producer_unification () = 
  (* f, □ *)
  let input0 = [tNat i] --> tNat i, tNat khat in (* id : ∀i . i -> i, Nat k^   ~>  k^ -> k^ *)
  let expected0 = Some ([tNat khat] --> tNat khat) in
  
  let input1 = [tNat i] --> tNat ihat, tNat khat in (* succ : ∀i . i -> i^, Nat k^   ~>  k -> k^ *)
  let expected1 = Some ([tNat k] --> tNat khat) in

  let input2 = [tNat i] --> tNat ihat, tNat Inf in (* succ : ∀i . i -> i^, Nat Inf   ~>  Inf -> Inf^ *)
  let expected2 = Some ([tNat Inf] --> tNat (SHat Inf)) in

  let input3 = TyArrow(U k, [tNat k], tNat k), tNat k in (* foo : k -> k, k  ~>   k -> k *)             (* unquantified recursive call *)
  let expected3 = Some (TyArrow(U k, [tNat k], tNat k)) in

  let input4 =  [tNat i; tNat Inf] --> tNat Inf, tNat Inf in (* add : ∀i. Nati -> Nat -> Nat, Nat inf ~> add *)
  let expected4 = Some ([tNat Inf; tNat Inf] --> tNat Inf) in

  let test_list = [
    input0, expected0;
    input1, expected1;
    input2, expected2;
    input3, expected3;
    input4, expected4;
    ] in
  List.iteri (fun n ((maybe, target),e) -> Alcotest.(check sizetyopt) (string_of_int n) e (ty_unify_producer maybe target))
    test_list

let test_mono_reachable_producer () = 
  (* f, □, Γ *)
  let input0 = [tNat i] --> tNat i, tNat khat, [tNat k] in (* id : ∀i . i -> i, Nat k^, tNat k   ~>  k^ -> k^ *)
  let expected0 = Some ([tNat khat] --> tNat khat) in

  let input1 = TyArrow(U k, [tNat k], tNat k), tNat Inf, [tNat khat] in (* foo : k -> k, _, khat  ~>   fail *)      (* unquantified recursive call on too-big argument*)
  let expected1 = None in

  let input2 = [tNat i] --> tNat ihat, tNat k, [tNat k] in (* Succ, k, [k] - this actually fails in unify_size_exp on the codomain so this test case could be simplified *)
  let expected2 = None in

  let input3 = [tNat i] --> tNat ihat, tNat khat, [tNat khat] in (* Succ, k^, [k^] - quantified - don't have small enough argument *)
  let expected3 = None in

  let input4 = TyArrow(U k, [tNat k], tNat k), tNat Inf, [tNat i] in (* foo : k -> k, _, i  ~>   fail *)      (* unquantified recursive call on wrong size variable*)
  let expected4 = None in

  let input5 = [tNat i; tNat Inf] --> tNat Inf, tNat Inf, [ (* does + produce Nat Inf under this environment? *)
      [tNat (SVar "i75")] --> tNat Inf ;
      tNat (SHat (SVar "i75")) ;
      tNat Inf ;
      [tNat k; tNat Inf] --> tNat Inf ;
      tNat khat ;
    ] in
  let expected5 = Some([tNat Inf; tNat Inf] --> tNat Inf) in

  let test_list = [
    input0, expected0;
    input1, expected1;
    input2, expected2;
    input3, expected3;
    input4, expected4;
    input5, expected5;
    ] in
  List.iteri (fun n ((maybe, target, ty_env),e) -> 
    let env = List.map (fun ty -> new_var ty) ty_env in (* turn types into vars for environment *)
    Alcotest.(check sizetyopt) (string_of_int n) e (ty_produces maybe target env))
    test_list

(*********** LET_FUNCTION ***********)

let let_base_helper () =
  let input1 = tNat i, [tNat j; tNat (SHat j); tNat Inf] in (* Nat ∞, {Nat j, Nat j^; Nat ∞} -> [j, j^, ∞]*)
  let expected1 = [j; (SHat j); Inf] in

 let test_list = [
    input1, expected1;
    (* input2, expected2; *)
    ] in
  List.iteri (fun n ((dom, ty_env), e) -> 
    let env = List.map (fun ty -> new_var ty) ty_env in
    Alcotest.(check sexplist) (string_of_int n) e (helper dom env))
    test_list

let let_base_computeT () = 
  let input1 = TyArrow(Q k, [tNat k], tNat k), [tNat j; tNat Inf] in 
  let expected1 = [tNat j; tNat Inf] in (* ∀k.Nat^k -> Nat^k, {Nat j, Nat ∞} -> [Nat^j, Nat∞]*)

  let input2 = TyArrow(Q k, [tNat k; tList Inf (tNat Inf)], tNat k), [tNat j; tNat Inf] in 
  let expected2 = [] in (* rejected: 2nd argument isn't reachable because environment doesn't have lists*)

 let test_list = [
    input1, expected1;
    input2, expected2;
    ] in
  List.iteri (fun n ((fTy, ty_env), e) -> 
    let env = List.map (fun ty -> new_var ty) ty_env in
    Alcotest.(check sizetylist) (string_of_int n) e (computeT fTy env))
    test_list

(*******************************************************)

let () =
  let open Alcotest in
  run "Everything" [
      "substitution", [ 
        test_case "subst_size_of_ty" `Quick test_subst_size_of_ty;
        test_case "safe_subst_size_exp" `Quick test_safe_subst_size_exp;
      ];
      "type_comparison",   [ test_case "size_subtype"   `Quick test_size_subtype  ];
      "unification", [ 
        test_case "unify_size_exp"                    `Quick test_unify_size_exp;
        test_case "unify_size_exp errors"             `Quick test_unification_errors;  
        test_case "unify hat: first order"            `Quick test_unify_one_hat;  
        (* test_case "unify hat: higher order"           `Quick test_HO_unify_one_hat;   *)
      ];
      "ty_unify_producer", [ 
        test_case "monomorphic producer"              `Quick test_mono_producer_unification;  
        test_case "monomorphic reachable producer"    `Quick test_mono_reachable_producer;
        ];
      "let_base", [
        test_case "helper"                            `Quick let_base_helper;
        test_case "computeT"                          `Quick let_base_computeT
        
      ]
    ]