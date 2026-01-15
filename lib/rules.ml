open Exp;;

let var_step (_ : generate_t) (_ : hole_info) (var : var) =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating VAR: %s\n") (show_var var));
  Var var

(***************************************************************)

(* Creates a funrec (named function with recursive call) *)
let funrec_step (f : var option) (generate : generate_t) (hole : hole_info)=
  let hat_func = TypeUtil.size_up_ty hole.ty in 
  match hat_func with
  | TyArrow (_, ty_params, ty') ->
     fun () ->
     Debug.run (fun () -> Printf.eprintf ("creating letrec\n"));
     let new_ty = TypeUtil.unquantify_ty hole.ty in
     let f = if Option.is_some f 
      then {(Option.get f) with var_ty=new_ty}
      else Exp.new_var new_ty ~prefix:"f" in
     let xs = List.map (fun t -> Exp.new_var t) ty_params in
     let body_hole = { hole with ty=ty'; env=f::xs@hole.env } in
     Exp.Letrec (f, xs, generate body_hole)
  | _ -> fun () ->
         raise (Util.Impossible "letrec constructor on non-function type")

(* let mutualrec_constructor_step (generate : generate_t) (hole : hole_info) (mutual_f : var) =
  (* App f' xs ... 
  where xs are existing bindings from the environment
  and f' will be picked by generators.ml from the list of mutuals in `hole`
  we will check f' with ty_produces to ensure arguments are available
  otherwise the same as indir_call_ref_step
  *)
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating mutualrec\n"));
  let xs = List.map (fun t -> Exp.new_var t) ty_params in
  let body_hole = { hole with ty=ty'; env=xs@hole.env } in
  Exp.App (mutual_f, generate body_hole) *)

(***************************************************************)

(* Construct an application of a fresh function to existing arguments *)
let fresh_call_ref_step (generate : generate_t) (hole : hole_info) (var, func_ty : var * size_ty) = (* NOTE: this is unary *)
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating APPREF (argument = %s)\n") (show_var var));
  (* NOTE: do something fun with the types (see 7-11 meeting note)*)
  let func_hole = {hole with ty=func_ty} in
  App(generate func_hole, List.map (fun v -> Var v) [var])

let indir_call_ref_step (generate : generate_t) (hole : hole_info) (var, ty : Exp.var * size_ty) =
  fun () ->
  match ty with
  | TyArrow (_, ty_params, _) -> 
    Debug.run (fun () -> Printf.eprintf ("creating INDIR call to %s\n") (var.var_name));
    let args = List.map (fun t -> generate { hole with ty=t}) ty_params in
    Exp.App (Exp.Var var, args)
  | _ -> raise (Util.Impossible "indir_call_ref_step on non-function type")
  
let let_step (generate : generate_t) (hole : hole_info) (tau1 : Exp.size_ty)  =
  fun () ->
  let x = Exp.new_var tau1 ~prefix:"n" in
  Debug.run (fun () -> Printf.eprintf ("creating let with %s : %s\n") (x.var_name) (show_size_ty x.var_ty));
  let val_hole = { hole with ty=tau1; env=hole.env} in
  let let_env = {x with var_ty=tau1}::hole.env in (*  extend environment in the body *)
  let body_hole = { hole with ty=hole.ty; env=let_env } in
  Exp.Let (x, generate val_hole, generate body_hole)
  
(***************************************************************)

let call_std_lib_step (generate : generate_t) (hole : hole_info) ((name, ty) : (string * Exp.size_ty))  =
  fun () ->
  match ty with
  | TyArrow (_, ty_params, _) -> (* single order assumes that the codomain is hole.ty. eg we can get to the target type in a single arrow*)
      Debug.run (fun () -> Printf.eprintf ("creating call std_lib reference: %s\n") name);
      let args = List.map (fun t -> generate { hole with ty=t}) ty_params in
    Exp.App (ExtRef (name, ty), args)
  | _ -> raise (Util.Impossible "call_std_lib on non-function type")

let std_lib_step (_ : generate_t) (_ : hole_info) ((name, ty) : (string * Exp.size_ty))  =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating std_lib reference: %s\n") name);
  ExtRef (name, ty)

let recur_constructor_step (generate : generate_t) (hole : hole_info) (name, ty : string * size_ty) =
  fun () ->
  match ty with
  | TyArrow (_, ty_params, _) -> (* single order assumes that the codomain is hole.ty. eg we can get to the target type in a single arrow*)
    Debug.run (fun () -> Printf.eprintf ("creating constructor reference: %s\n") name);
    let args = List.map (fun t -> generate { hole with ty=t}) ty_params in
    App(ExtRef(name, hole.ty), args)
  | _ -> raise (Util.Impossible "recur_constructor_step on non-function type")

let base_constructor_step (_ : generate_t) (hole : hole_info) (name , _ : string * size_ty) =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating base constructor reference: %s\n") name);
  ExtRef(name, hole.ty)

(***************************************************************)

let case_step (generate : generate_t) (hole : hole_info) 
              (var, constructors : var * func_list) =
  fun () ->
    Debug.run (fun () -> Printf.eprintf ("creating case with %s\n") (show_var var));
    let new_binders : var list list = 
      List.map (fun (name, constructor_ty) ->
      match TypeUtil.ty_unify_producer constructor_ty var.var_ty with (* turn constructor into a function to check reachable *)
      | Some TyArrow(_, subst_ty_params, _) -> List.map (fun dom_ty -> Exp.new_var dom_ty) subst_ty_params
      | _ -> raise (Util.Impossible (Format.sprintf "case_step: unification issue with %s" name)))
      constructors in 
    let clause_bodies =   
      List.map 
      (fun plst -> generate { hole with env=plst@hole.env})
      new_binders in
    Exp.Case(Var var, var.var_ty, List.combine new_binders clause_bodies) 