open Exp;;

(************************************ TRANSITIONS ************************************************)

let steps_generator (hole : hole_info) (acc : rule_urn)
                    (rule : generate_t -> hole_info -> 'a -> unit -> exp)
                    (weight : hole_info -> 'a -> float)
                    (generate : generate_t)
                    (collection : 'a list) =
  List.fold_left (fun acc a ->
                  Urn.insert acc (weight hole a) (Urn.Value (rule generate hole a)))
             acc collection

let singleton_generator (weight : hole_info -> 'a -> float)
                        (rule : generate_t -> hole_info -> unit -> exp)
                        (hole : hole_info) (acc : rule_urn)
                        (generate : generate_t) =
  Urn.insert acc (weight hole ()) (Urn.Value (rule generate hole))

(************************************ WEIGHTS ************************************************)


let c (w : float) (_ : hole_info) _ = w
let w_const n = c n
let w_fuel_base n m (hole : hole_info) _ = Int.to_float hole.fuel *. n +. m
let w_fuel_depth (hole : hole_info) _ = Int.to_float (max 0 (hole.fuel - hole.depth))

let w_fuel n = w_fuel_base n 0.

(************************************ GENERATORS ************************************************)

(*
τ ⊑ T
--------------------- (VAR)
Γ, x : τ ⊢ □ : T ↝ x
*)
let var_steps weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
  (*Debug.run (fun () -> Printf.eprintf "considering var\n"); *)
  let ref_vars = List.filter (fun v -> 
    match v.var_ty with
    | TyArrow(U _,  _, _) -> false (* NOTE: don't allow unquantified funcs to fill holes. 
    prevents issue where APPREF's function □ is accidentally filled with a recursive call 
    on an inappropriately sized argument. there may be better solutions but it technically
    doesn't limit program space because indir_call_recur_step still creates valid recursive apps *)
    | _ -> TypeUtil.is_size_subtype_ty v.var_ty hole.ty)
    hole.env in
  steps_generator hole acc
                Rules.var_step weight generate ref_vars


(*
Γ, x : (d^ihat τ), f : (d^i τ) → θ ⊢
□ : θ[i := ihat] ↝ e
-------------------------------------- (REC)
Γ ⊢ □ : ∀i.(d^i τ) → θ ↝ funrec x.e
*)
let funrec_steps weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
   (*Debug.run (fun () -> Printf.eprintf "considering letrec\n"); *)
  match hole.ty with
  | TyArrow (Q _, _, _) -> singleton_generator weight (Rules.funrec_step None) hole acc generate
  | _ -> acc

(* generate a fresh arrow type for an application using existing variables as arguments

τ_1 ⊑ τ_2
θ[k := α] ⊑ T
Γ, x : τ  ⊢  □ : ∀k.(d^k τ_2) → θ ↝ e
-------------------------------------- (APPREF)
Γ, x : (d^α τ_1)   ⊢   □ : T ↝ (e x)

Generally, this rule requires you to find θ such that T = θ[k := α] (precondition 2 above is written with subtyping)
Instead of unsubstituting, we'll just do θ = T[α := k] where α is the size expression of the variable.
Only successful substitution are kept. This dismisses cases such as T=k, α=khat where there is not a well-formed function.

NOTE: For now, we pick only 1 var at a time for unary function. Each element of var_tys is a SINGLE function:
Where the production judgement has a lambda hole of this type:
  □ : ∀k.(d^k τ_2) → θ
We pass the following type into Rules:
  □ : ∀k. τ^α → T[α := k] 
where τ was the type of the variable
*)
let fresh_call_ref_step weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
  match hole.ty with
  | TyCons _ -> (* NOTE: Only allow first-order holes to be filled *)
   (*(* Debug.run (fun () -> Printf.eprintf "considering fresh_call\n"); *)*)
  let k = new_s_var () in
  let var_tys : (var * size_ty) list = List.filter_map (fun var -> match var.var_ty with
    | TyCons _ -> (* NOTE: Only allow first order variables on RHS of application *)
    (* Debug.run (fun () -> Printf.eprintf "\t%s\n" (show_var var));  *)
    (if Option.is_some(TypeUtil.safe_subst_size_exp (TypeUtil.size_exp_of_ty hole.ty) (TypeUtil.size_exp_of_ty var.var_ty) k)
      then Some (var, 
        TyArrow(Q k, 
          [(TypeUtil.resize_ty var.var_ty k)], (* τ^α: replace variable's size expression with k *)
          TypeUtil.subst_size_of_ty hole.ty (TypeUtil.size_exp_of_ty var.var_ty) k)) (* T[α := k] *)
      else None)
    | _ -> None)
    hole.env in
  steps_generator hole acc
                  Rules.fresh_call_ref_step weight generate var_tys
    | _ -> acc

(* application of function w/ arguments, all from the environment 

τ_1 ⊑ τ_2
θ[k := α] ⊑ T
------------------------------------------------------- (INDIR)
Γ, x : (d^α τ_1), f : ∀k.(d^k τ_2) → θ ⊢ □ : T ↝ (f x)
*)

(* helper function for 2 different versions of INDIR:
- non-recursive applications
- recursive applications
*)
let indir_call weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn)
                      (filter_ty : var -> bool) =
  let gamma_refs : (var * size_ty) list = List.filter_map
    (fun v -> if filter_ty v
      then (match TypeUtil.ty_produces v.var_ty hole.ty hole.env with
        | Some subst_tyArrow -> Some (v, subst_tyArrow)
        | None -> None) 
      else None)
    hole.env in
  steps_generator hole acc
                  Rules.indir_call_ref_step weight generate gamma_refs

let indir_call_ref_step weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
   (*Debug.run (fun () -> Printf.eprintf "considering indir_call\n"); *)
  indir_call weight generate hole acc (* quantified functions are not recursive *)
    (fun v -> match v.var_ty with | TyArrow(Q _, _, _) -> true | _ -> false)
let indir_call_recur_step weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
   (*Debug.run (fun () -> Printf.eprintf "considering indir_call\n"); *)
  indir_call weight generate hole acc (* non-quantified functions are recursive *)
    (fun v -> match v.var_ty with | TyArrow(U _, _, _) -> true | _ -> false)

(*
θ[k := α] = T
Γ                       ⊢ □₁ : ∀k.(d^k τ_1) → θ ↝ e₁
Γ, f : ∀k.(d^k τ_1) → θ ⊢ □₂ : T                ↝ e₂
------------------------------------------------------- (NEST_LETREC)
Γ, x : (d^α τ_1) ⊢ □ : T ↝ (letrec f = e₁ in e₂)

This rule introduces a recursive function without immediately producing it in □₂, allowing it to be used arbitrarily.
The type of □₁ is a function from (some sized type available in the environment) to T
I am not bothering with subtyping here.
This is similar to appref in its size subsitution, so I'll have to copy that rule.
NOTE: unary assumption
This won't increase the number of recursive calls within the body, but it might increase (or decrease) 
the number of times a recursive call is started because we don't control e_2. You could increase the number
of times by increasing the weight of indir_call_ref_step.


TODO 2026-01-09: how do we extend to base-types, eg s.t. 
let x : base-type = e1 in e2
How do we choose base-type intelligently?
- something accepted by the domain of a function in the environment (eg can be consumed)

Actually, this could pick a type we can't produce (for example if we're generating foo, and we pick foo's domain when we don't have access to something SMALL enough)
  ... the type we pick should also be REACHABLE.

*)
let let_function weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
  match hole.ty with
  | TyCons _ -> (* TODO: Only allow first-order holes to be filled - this shouldn't be a requirement?? *)
    (*Debug.run (fun () -> Printf.eprintf "considering nest_letrec\n"); *)
    (* construct a function type*)
    let k = new_s_var () in
    let types : size_ty list = (* possible τ_1 s*)
    List.filter_map (fun var -> match var.var_ty with
      | TyCons _ -> (* NOTE: Only allow first order as the function domain *)
      (* Debug.run (fun () -> Printf.eprintf "\t%s\n" (show_var var));  *)
      (if Option.is_some(TypeUtil.safe_subst_size_exp (TypeUtil.size_exp_of_ty hole.ty) (TypeUtil.size_exp_of_ty var.var_ty) k)
        then Some (
          TyArrow(Q k, 
            [(TypeUtil.resize_ty var.var_ty k)], (* τ^α: replace variable's size expression with k *)
            TypeUtil.subst_size_of_ty hole.ty (TypeUtil.size_exp_of_ty var.var_ty) k)) (* T[α := k] *)
        else None)
      | _ -> None)
        hole.env in
      steps_generator hole acc
        Rules.let_step weight generate types
  | _ -> acc

(* attempt #2*)
(* let let_base2 weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
  (*Debug.run (fun () -> Printf.eprintf "considering nest_letrec\n"); *)

  (* list of all reachable types in the environment *)
  (* NOTE: higher-order functions are excluded here *)
  let rec get_reachable (t : size_ty) : size_ty list = 
  match t with
    | TyCons _ -> [TypeUtil.resize_ty t Inf]
    | TyArrow (U _, _, cod) -> if is_func cod 
      then                               get_reachable(cod)  
      else TypeUtil.resize_ty cod Inf :: get_reachable(cod) 
      
    | TyArrow (Q _, _, cod) -> if is_func cod 
      then                               get_reachable(cod)(* ok now what do we do with the sizes?? see notebook - for now subst with Inf*)  
      else TypeUtil.resize_ty cod Inf :: get_reachable(cod) 
      
    | _ -> []
  in
  let types = List.map (fun v -> get_reachable v.var_ty) hole.env in
  steps_generator hole acc
        Rules.let_step weight generate (List.flatten types) *)

(* attempt #3 *)

let let_base2 weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
  (*Debug.run (fun () -> Printf.eprintf "considering nest_letrec\n"); *)
  let types : SizeTySet.t = SizeTySet.of_list (List.fold_left (fun acc v -> 
    TypeUtil.computeT v.var_ty hole.env @ acc) 
    []
    hole.env)
  in
  steps_generator hole acc
        Rules.let_step weight generate (SizeTySet.to_list types)

(************************)

(* application of function from std_lib with arguments from the environment (analagous to INDIR above) *)
let std_lib_steps (std_lib_m : (string * size_ty) list)
                   weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
   (*Debug.run (fun () -> Printf.eprintf "considering std_lib\n"); *)
  let lib_refs : (string * size_ty) list = List.filter_map 
    (fun ref -> let (name, ty) = ref in
      match TypeUtil.ty_produces ty hole.ty hole.env with
      | Some subst_ty -> Some(name, subst_ty)
      | None -> None)
    std_lib_m in
  (* Debug.run (fun () -> Printf.eprintf ("std_lib_steps filtered refs: %s\n") 
    (List.fold_left (fun acc (name, _) -> name ^ " " ^ acc) "" lib_refs)); *)
  steps_generator hole acc
                Rules.call_std_lib_step weight generate lib_refs

(* values from std_lib. analagous to VAR *)
let base_std_lib_steps (base_std_lib : (string * size_ty) list)
                      weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
   (*Debug.run (fun () -> Printf.eprintf "considering base_std_lib\n"); *)
  let lib_refs = List.filter_map
    (fun ref -> let (_, ty) = ref in
      if (TypeUtil.is_size_subtype_ty ty hole.ty) then (Some ref) else None)
    base_std_lib in
  (* Debug.run (fun () -> Printf.eprintf ("std_lib_steps filtered refs: %s\n") 
    (List.fold_left (fun acc (name, _) -> name ^ " " ^ acc) "" lib_refs)); *)
  steps_generator hole acc
                Rules.std_lib_step weight generate lib_refs

(* helper *)
let filter_constructors (data_cons : data_constructors_t) (hole : hole_info) : func_list =
  let constructors = TypeUtil.lookup_constructors data_cons hole.ty in
  List.filter_map (fun (name, constructor_ty) ->
    match TypeUtil.ty_produces constructor_ty hole.ty hole.env with
    | Some subst_ty -> Some(name, subst_ty)
    | None -> None)
    constructors 

(* Call recursive constructors such as Succ or Cons. Analagous to INDIR *)
let recur_constructor_steps (data_cons : data_constructors_t)
                   weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
   (*Debug.run (fun () -> Printf.eprintf "considering recur_constructor\n"); *)
  match hole.ty with 
  | TyCons _ ->
    steps_generator hole acc
                    Rules.recur_constructor_step weight generate (filter_constructors data_cons hole)
  | _ -> acc

(* Call base constructors such as Zero or Nil. Analagous to INDIR *)
let base_constructor_steps (base_data_cons : data_constructors_t)
                       weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
   (*Debug.run (fun () -> Printf.eprintf "considering base_constructor\n"); *)
  match hole.ty with 
  | TyCons _ ->
    steps_generator hole acc
                  Rules.base_constructor_step weight generate (filter_constructors base_data_cons hole)
  | _ -> acc

(* 
cₖ : θₖ → d
Γ, y : θₖ ⊢ □ₖ : T  ↝ eₖ
1 ≤ k ≤ n
------------------------------------------------------- (MATCH)
Γ, x : (d^α τ) ⊢ □ : T ↝ 
(match e with 
  | c₁ y ... -> e₁ 
   ... 
  | cₙ y ... -> eₙ)

The "head" (scrutinee) of the match must be a variable. 
match_head_count prevents us from using the same variable more than once (in one branch - it does not check across branches of the AST)
*)
let match_steps (data_cons : data_constructors_t)
                   weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
   (*Debug.run (fun () -> Printf.eprintf "considering case\n"); *)
  let var_constructors : (var * func_list) list = 
    List.filter_map Fun.id 
    (List.map2 
      (fun var count -> 
        match var.var_ty with 
        | TyCons _ when count < 1 -> Some (var, TypeUtil.lookup_constructors data_cons var.var_ty)
        | _ -> None)
      hole.env
      hole.match_head_count) in
  steps_generator hole acc
                Rules.match_step weight generate var_constructors


(********************************************************)

let main (lib : library) : generators_t =
  let { std_lib=std_lib; data_cons=data_cons} = lib in 
  (* partition std_lib and data_cons into base (value) and callable (function) *)
  let (base_std_lib, call_std_lib) = List.partition (fun (_, ty) -> match ty with TyCons _ -> true | _ -> false ) std_lib in
  let (base_data_cons, recur_data_cons) = List.fold_left
    (fun (base_acc, recur_acc) constructors -> 
      let (base, recur) = List.partition (fun (_ , ty) -> 
        match ty with 
        | TyArrow(_, [], _) -> true (* base constructors have no arguments *)
        | _ -> false)
        constructors in
      (base::base_acc, recur::recur_acc))
    ([], [])
    data_cons in
  [
    var_steps                       ( w_const 2.        );
    indir_call_ref_step             ( w_fuel      2.    );
    indir_call_recur_step           ( w_fuel      3.    );
    let_base2                       ( w_fuel      2.    );
    std_lib_steps call_std_lib      ( w_fuel      4.    );
    base_std_lib_steps base_std_lib ( w_const 1.        );
    recur_constructor_steps recur_data_cons     ( w_fuel_base 2. 0. );
    base_constructor_steps base_data_cons ( w_const 1.  );
    match_steps data_cons            ( w_fuel_base 1. 0. );
  ]
  @
  if !Debug.test_type == 430 then []
  else [ (* The following features are not supported in 430's subset of Racket because they create recursive functions that aren't top-level definitions *)
    funrec_steps                    ( w_fuel_base 2. 1. ); 
    fresh_call_ref_step             ( w_fuel_base 1. 0. ); 
    let_function                    ( w_fuel      3.   ); 
  ]