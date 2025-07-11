open Exp;;

let var_step (_ : generate_t) (_ : hole_info) (var : var) =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating var reference: %s\n") (show_var var));
  Var var

(* Creates a lambda *)
let func_constructor_step (generate : generate_t) (hole : hole_info) =
  match hole.ty with
  | TyArrow (ty_params, ty') ->
     fun () ->
     Debug.run (fun () -> Printf.eprintf ("creating lambda (Ty=%s) \n") (show_size_ty hole.ty));
     let xs = List.map (fun t -> Exp.new_var t) ty_params in
     let body_hole = { hole with ty=ty'; env=xs@hole.env } in
     Exp.Lambda (xs, generate body_hole)
  | _ -> fun () ->
         raise (Util.Impossible "function constructor on non-function type")

(* Creates a funrec (named function with recursive call) *)
let letrec_constructor_step (generate : generate_t) (hole : hole_info) =
  match hole.ty with
  | TyArrow (ty_params, ty') ->
     fun () ->
     Debug.run (fun () -> Printf.eprintf ("creating letrec\n"));
     let f = Exp.new_var hole.ty in
     let xs = List.map (fun t -> Exp.new_var t) ty_params in
     let body_hole = { hole with ty=ty'; env=f::xs@hole.env } in
     Exp.Letrec (f, xs, generate body_hole)
  | _ -> fun () ->
         raise (Util.Impossible "letrec constructor on non-function type")


let indir_call_ref_step (generate : generate_t) (hole : hole_info) (var : Exp.var) =
  fun () ->
  match var.var_ty with
  | TyArrow (ty_params, _) -> 
    Debug.run (fun () -> Printf.eprintf ("creating INDIR call reference (%s)\n") (var.var_name));
    let args = List.map (fun t -> generate { hole with ty=t}) ty_params in
    Exp.App (Exp.Var var, args)
  | _ -> raise (Util.Impossible "indir_call_ref_step on non-function type")



(* NOTE: this could be reused for indir_call_ref_step if you're smarter*)
let firstorder_application (generate : generate_t) (hole : hole_info) (name : string) (ty : Exp.size_ty) = 
  match ty with
  | TyArrow (ty_params, _) -> (* single order assumes that the codomain is hole.ty. eg we can get to the target type in a single arrow*)
    let args = List.map (fun t -> generate { hole with ty=t}) ty_params in
    Exp.App (ExtRef (name, ty), args)
  | _ -> raise (Util.Impossible "higher order application on non-function type")

let call_std_lib_step (generate : generate_t) (hole : hole_info) ((name, ty) : (string * Exp.size_ty))  =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating call std_lib reference: %s\n") name);
  firstorder_application generate hole name ty
let std_lib_step (_ : generate_t) (_ : hole_info) ((name, ty) : (string * Exp.size_ty))  =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating std_lib reference: %s\n") name);
  ExtRef (name, ty)

let constructor_step (generate : generate_t) (hole : hole_info) ((name, ty_params) : (string * size_ty list)) =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating constructor reference: %s\n") name);
  let args = List.map (fun t -> generate { hole with ty=t}) ty_params in
  App(ExtRef(name, hole.ty), args)

let base_constructor_step (_ : generate_t) (hole : hole_info) (name : string) =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating base constructor reference: %s\n") name);
  App(ExtRef(name, hole.ty), [])



let case_step (generate : generate_t) (hole : hole_info) 
              ((var, constructors) : var * (string * size_ty list) list) =
  fun () ->
    Debug.run (fun () -> Printf.eprintf ("creating case with %s\n") (show_var var));
    let params : var list list = 
      List.map 
      (fun (_, ty_params) -> 
        List.map (fun ty -> 
          (* NOTE: would be more efficient to return the substitution from TypeUtils & pass the result of the call in
          generators.ml into here *)
          (match TypeUtil.unify_size_exp (SHat (SVar "i")) (TypeUtil.size_exp_of_ty var.var_ty) with (* assume that constructors in library have size ihat*)
          | None -> raise (Util.Impossible (Format.sprintf "case_step: help"))
          | Some (iexp, kexp) ->
            let dom_st = TypeUtil.subst_size_of_ty ty iexp kexp in
            Exp.new_var dom_st))
          ty_params)
      constructors in
    let clause_bodies =   
      List.map 
      (fun plst -> generate { hole with env=plst@hole.env})
      params in
    Exp.Case(Var var, var.var_ty, List.combine params clause_bodies)