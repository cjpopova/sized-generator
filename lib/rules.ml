open Exp;;

let var_step (_ : generate_t) (_ : hole_info) (var : var) =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating var reference\n"));
  Var var

(* Creates a lambda *)
let func_constructor_step (generate : generate_t) (hole : hole_info) =
  match hole.ty with
  | FlatTyArrow (ty_params, ty') ->
     fun () ->
     Debug.run (fun () -> Printf.eprintf ("creating lambda\n"));
     let xs = List.map (fun t -> Exp.new_var t) ty_params in
     let body_hole = { hole with ty=ty'; env=xs@hole.env } in
     Exp.Lambda (xs, generate body_hole)
  | _ -> fun () ->
         raise (Util.Impossible "function constructor on non-function type")

(* Creates a letrec (named function with recursive call)*)
let letrec_constructor_step (generate : generate_t) (hole : hole_info) =
  match hole.ty with
  | FlatTyArrow (ty_params, ty') ->
     fun () ->
     Debug.run (fun () -> Printf.eprintf ("creating letrec\n"));
     let f = Exp.new_var hole.ty in
     let xs = List.map (fun t -> Exp.new_var t) ty_params in
     let body_hole = { hole with ty=ty'; env=f::xs@hole.env } in
     Exp.Letrec (f, xs, generate body_hole)
  | _ -> fun () ->
         raise (Util.Impossible "letrec constructor on non-function type")

(* NOTE: this could be reused for indir_call_ref_step if you're smarter*)
let firstorder_application (generate : generate_t) (hole : hole_info) (name : string) (ty : Exp.flat_ty) = 
  match ty with
  | FlatTyArrow (ty_params, _) -> (* single order assumes that the codomain is hole.ty. eg we can get to the target type in a single arrow*)
    let args = List.map (fun t -> generate { hole with ty=t}) ty_params in
    Exp.App (ExtRef (name, ty), args)
  | _ -> raise (Util.Impossible "higher order application on non-function type")

  (* std_lib references, including direct references and applications *)
let std_lib_step (generate : generate_t) (hole : hole_info) ((name, ty) : (string * Exp.flat_ty))  =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating std_lib reference\n"));
  if TypeUtil.is_same_ty hole.ty ty then
    ExtRef (name, ty)
  else 
    firstorder_application generate hole name ty

let indir_call_ref_step (generate : generate_t) (hole : hole_info) (var : Exp.var) =
  fun () ->
  match var.var_ty with
  | FlatTyArrow (ty_params, _) -> 
    Debug.run (fun () -> Printf.eprintf ("creating INDIR call reference (%s)\n") (var.var_name));
    let args = List.map (fun t -> generate { hole with ty=t}) ty_params in
    Exp.App (Exp.Var var, args)
  | _ -> raise (Util.Impossible "indir_call_ref_step on non-function type")

