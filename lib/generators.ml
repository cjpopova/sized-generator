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


let var_steps weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
  let ref_vars = List.filter (fun v -> TypeUtil.is_same_ty v.var_ty hole.ty) hole.env in
  steps_generator hole acc
                  Rules.var_step weight generate ref_vars

(* NOTE: make this distinct from letrec
*)
let lambda_steps weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
  match hole.ty with
  | TyArrow _ ->
    singleton_generator weight Rules.func_constructor_step hole acc generate
  | _ -> acc

let letrec_steps weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
  match hole.ty with
  | TyArrow (ty_params, _) ->
    if List.exists (fun ty -> Inf != TypeUtil.size_exp_of_ty ty) ty_params then (* At least one sized argument *)
    singleton_generator weight Rules.letrec_constructor_step hole acc generate
    else acc
  | _ -> acc

(* application *)
let fresh_call_ref_step weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
  (* pick some random subset of Gamma. at least variable must be a sized constructor 
  NOTE for now, we'll allow unary functions of any sized variable in the environment
  *)
  let args = List.filter (fun var -> match var.var_ty with 
    | TyCons(_, _, SHat _) -> true 
    | TyCons(_, _, SVar _) -> true 
    | _ -> false)
    hole.env in
  steps_generator hole acc
                  Rules.fresh_call_ref_step weight generate args

let indir_call_ref_step weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
  let gamma_refs : (var * size_ty) list = List.filter_map
    (fun v -> match TypeUtil.ty_produces v.var_ty hole.ty hole.env with
    | Some subst_tyArrow -> Some (v, subst_tyArrow)
    | None -> None) hole.env in
  steps_generator hole acc
                  Rules.indir_call_ref_step weight generate gamma_refs

let std_lib_steps (std_lib_m : (string * size_ty) list)
                   weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
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

let base_std_lib_steps (base_std_lib : (string * size_ty) list)
                      weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
  let lib_refs = List.filter_map
    (fun ref -> let (_, ty) = ref in
      if (TypeUtil.is_same_ty ty hole.ty) then (Some ref) else None)
    base_std_lib in
  (* Debug.run (fun () -> Printf.eprintf ("std_lib_steps filtered refs: %s\n") 
    (List.fold_left (fun acc (name, _) -> name ^ " " ^ acc) "" lib_refs)); *)
  steps_generator hole acc
                Rules.std_lib_step weight generate lib_refs

let recur_constructor_steps (data_cons : data_constructor_t)
                   weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
  match hole.ty with 
  | TyCons _ ->
    let {ty=t_hat; constructors=constructors} = TypeUtil.lookup_constructors data_cons hole.ty in
    let reachable_cons = List.filter_map (fun (name, ty_params) ->
      match TypeUtil.ty_produces (TyArrow(ty_params, t_hat)) hole.ty hole.env with (* turn constructor into a function to check reachable *)
      | Some subst_ty -> Some(name, subst_ty)
      | None -> None)
      constructors in 
    steps_generator hole acc
                    Rules.recur_constructor_step weight generate reachable_cons
  | _ -> acc

let base_constructor_steps (base_data_cons : data_constructor_t)
                       weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
  match hole.ty with 
    | TyCons _ ->
    let names : string list = List.fold_left
      (fun acc {ty=ty; constructors=cons} -> 
        if (TypeUtil.is_same_ty ty hole.ty) then (List.map (fun (name, _) -> name) cons) @acc else acc)
      []
      base_data_cons in
    (* Debug.run (fun () -> Printf.eprintf ("std_lib_steps filtered names: %s\n") 
      (List.fold_left (fun acc (name, _) -> name ^ " " ^ acc) "" names)); *)
    steps_generator hole acc
                  Rules.base_constructor_step weight generate names
  | _ -> acc

(* NOTE: for now, we allow only variables with a size-hat to be at the head of `case` *)
let case_steps (data_cons : data_constructor_t)
                   weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
  let var_constructors : (var * data_info) list = 
    (List.filter_map 
      (fun var -> 
        match var.var_ty with 
        | TyCons (_, _, SHat _) -> Some (var, TypeUtil.lookup_constructors data_cons var.var_ty)
        | _ -> None)
      hole.env) in
  steps_generator hole acc
                Rules.case_step weight generate var_constructors


(********************************************************)

let main (lib : library) : generators_t =
  let { std_lib=std_lib; data_cons=data_cons} = lib in 
  (* partition std_lib and data_cons into base (value) and callable (function) *)
  let (base_std_lib, call_std_lib) = List.partition (fun (_, ty) -> match ty with TyCons _ -> true | _ -> false ) std_lib in
  let (base_data_cons, recur_data_cons) = List.fold_left
    (fun (base_acc, recur_acc) {ty=ty; constructors=constructors} -> 
      let (base, recur) = List.partition (fun cc -> List.is_empty (snd cc)) constructors in
      ({ty=ty; constructors=base}::base_acc, {ty=ty; constructors=recur}::recur_acc))
    ([], [])
    data_cons in
  [
    var_steps                       ( w_const 2.        );
    lambda_steps                    ( w_fuel_base 5. 1. );
    (* letrec_steps                    ( w_fuel_base 4. 1. ); *)
    fresh_call_ref_step             ( w_fuel_base 2. 0. );
    indir_call_ref_step             ( w_fuel_base 2. 1. );
    std_lib_steps call_std_lib      ( w_fuel_base 1. 0. );
    base_std_lib_steps base_std_lib ( w_const 1.        );
    recur_constructor_steps recur_data_cons     ( w_fuel_base 1. 0. );
    base_constructor_steps base_data_cons ( w_const 1.  );
    case_steps data_cons            ( w_fuel_base 3. 0. );
  ]