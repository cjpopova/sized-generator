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

let lambda_steps weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
  match hole.ty with
  | TyArrow _ ->
    singleton_generator weight Rules.func_constructor_step hole acc generate
  | _ -> acc

let letrec_steps weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
  match hole.ty with
  | TyArrow _ ->
    singleton_generator weight Rules.letrec_constructor_step hole acc generate
  | _ -> acc

let indir_call_ref_step weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
  let gamma_refs : var list = List.filter
    (fun v -> TypeUtil.ty_produces hole.ty v.var_ty) hole.env in 
  steps_generator hole acc
                  Rules.indir_call_ref_step weight generate gamma_refs

(* NOTE could be improved: The next 2 rules are different wrappers around std_lib_step. 
1. base_data_steps includes the base constructor steps (eg true, false, 0, [], leaf)
2. std_lib_steps includes the std_lib combined (in main) with the non-base constructors of data type (eg Succ, cons, node)
*)
let base_std_lib_steps (base_std_lib : (string * size_ty) list)
                       weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
  let lib_refs = List.filter_map
    (fun ref -> let (_, ty) = ref in
      if (TypeUtil.is_same_ty hole.ty ty) then (Some ref) else None)
    base_std_lib in
  (* Debug.run (fun () -> Printf.eprintf ("std_lib_steps filtered refs: %s\n") 
    (List.fold_left (fun acc (name, _) -> name ^ " " ^ acc) "" lib_refs)); *)
  steps_generator hole acc
                Rules.std_lib_step weight generate lib_refs

let std_lib_steps (std_lib_m : (string * size_ty) list)
                   weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
  let lib_refs = List.filter_map (* NOTE: this type filtering could be more efficient *)
    (fun ref -> let (_, ty) = ref in
      if (TypeUtil.is_same_ty hole.ty ty) || (TypeUtil.ty_produces hole.ty ty) then (Some ref) else None)
    std_lib_m in
  (* Debug.run (fun () -> Printf.eprintf ("std_lib_steps filtered refs: %s\n") 
    (List.fold_left (fun acc (name, _) -> name ^ " " ^ acc) "" lib_refs)); *)
  steps_generator hole acc
                Rules.std_lib_step weight generate lib_refs

(* NOTE: for now, we allow only variables (any variables) to be at the head of `case` *)
let case_steps (data_cons : data_constructor_t)
                   weight (generate : hole_info -> exp) (hole : hole_info) (acc : rule_urn) =
  let var_constructors : (var * ((string * size_ty list) list)) list = 
    List.map 
      (fun var -> (var, TypeUtil.lookup_constructors data_cons var.var_ty))
      hole.env in
  steps_generator hole acc
                Rules.case_step weight generate var_constructors


(********************************************************)

let main (lib : library) : generators_t =
  let { std_lib=std_lib; data_cons=data_cons} = lib in 
  let std_lib=TypeUtil.recur_constructors_to_std_lib data_cons @ std_lib in
  let base_std_lib=TypeUtil.base_constructors_to_std_lib data_cons in
  [
    var_steps                       ( w_const 2.        );
    lambda_steps                    ( w_fuel_base 10. 1. );
    indir_call_ref_step             ( w_fuel_base 2. 1. );
    letrec_steps                    ( w_fuel_base 4. 1. );
    base_std_lib_steps base_std_lib           ( w_const 1.        ); (* base constructors always available*)
    std_lib_steps std_lib           ( w_fuel_base 1. 0. ); (* recursive constructors & the rest of std_lib require >0 fuel *)
    case_steps data_cons            ( w_fuel_base 4. 0. ); (* NOTE: not sure about weight *)
  ]