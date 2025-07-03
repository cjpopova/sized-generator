type hole_info = {
    label : Exp.exp_label;
    ty_label : Type.flat_ty;
    prev : Exp.exp_label option;
    fuel : int;
    vars : (Exp.var * Type.flat_ty) list;
    depth : int;
  }

(* ValInt, ValBool, etc *)
let base_constructor_step (prog : Exp.program) (hole : hole_info) exp' =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("Creating base constructor\n"));
  prog.set_exp hole.label {exp=exp'; ty=hole.ty_label; prev=hole.prev; choices=Urn.empty};
  []
  (*match prog.ty.get_ty hole.ty_label with
  | TyInt ->
     fun () ->
     set exp'; []
  | _ -> raise (Util.Impossible "bad base type")*)


let var_step (prog : Exp.program) (hole : hole_info) (var, _) =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating var reference\n"));
  prog.set_exp hole.label {exp=Exp.Var var; ty=hole.ty_label; prev=hole.prev; choices=Urn.empty};
  []

(* Creates a lambda *)
let func_constructor_step (prog : Exp.program) (hole : hole_info) =
  let set exp = prog.set_exp hole.label {exp=exp; ty=hole.ty_label; prev=hole.prev; choices=Urn.empty} in
  match hole.ty_label with
  | FlatTyArrow (ty_params, ty') ->
     fun () ->
     Debug.run (fun () -> Printf.eprintf ("creating lambda\n"));
     let xs = List.map (fun _ -> prog.new_var ()) ty_params in
     let body = prog.new_exp {exp=Exp.Hole; ty=ty'; prev=Some hole.label; choices=Urn.empty} in
     set (Exp.Lambda (xs, body));
     [body]
  | _ -> fun () ->
         raise (Util.Impossible "function constructor on non-function type")

(* Creates a letrec (named function with recursive call)*)
let letrec_constructor_step (prog : Exp.program) (hole : hole_info) =
  let set exp = prog.set_exp hole.label {exp=exp; ty=hole.ty_label; prev=hole.prev; choices=Urn.empty} in
  match hole.ty_label with
  | FlatTyArrow (ty_params, ty') ->
     fun () ->
     Debug.run (fun () -> Printf.eprintf ("creating letrec\n"));
     let xs = List.map (fun _ -> prog.new_var ()) ty_params in
     let body = prog.new_exp {exp=Exp.Hole; ty=ty'; prev=Some hole.label; choices=Urn.empty} in
     set (Exp.Letrec (prog.new_var (), xs, body));
     [body]
  | _ -> fun () ->
         raise (Util.Impossible "letrec constructor on non-function type")

(* NOTE: this could be reused for indir_call_ref_step if you're smarter*)
let firstorder_application (prog : Exp.program) (hole : hole_info) (name : string) (ty : Type.flat_ty) = 
  match ty with
  | FlatTyArrow (ty_params, _) -> (* single order assumes that the codomain is hole.ty_label. eg we can get to the target type in a single arrow*)
    let func = prog.new_exp {exp=ExtRef (name, ty);
                              ty = ty;
                              prev=Some hole.label;
                              choices=Urn.empty} in
      let args = List.map (fun ty -> prog.new_exp {exp=Exp.Hole;
                                                  ty=ty;
                                                  prev=Some hole.label;
                                                  choices=Urn.empty}) ty_params in
  prog.set_exp hole.label {exp=Exp.App (func, args); ty=hole.ty_label; prev=hole.prev; choices=Urn.empty};  args
  | _ -> raise (Util.Impossible "higher order application on non-function type")

  (* std_lib references, including direct references and applications *)
let std_lib_step (prog : Exp.program) (hole : hole_info) ((name, ty) : (string * Type.flat_ty))  =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating std_lib reference\n"));
  if TypeUtil.is_same_ty hole.ty_label ty then
    (prog.set_exp hole.label {exp=ExtRef (name, ty); ty=hole.ty_label; prev=hole.prev; choices=Urn.empty}; 
    [])
  else 
    firstorder_application prog hole name ty


let indir_call_ref_step (prog : Exp.program) (hole : hole_info) ((ref, doms) : (Exp.var * Type.flat_ty) * Type.flat_ty list)=
  fun () ->
  let (var, ty) = ref in
  Debug.run (fun () -> Printf.eprintf ("creating INDIR call reference (%s)\n") (Exp.Var.to_string var));
  let func = prog.new_exp {exp=Exp.Var var;
                           ty=ty;
                           prev=Some hole.label;
                           choices=Urn.empty} in
  let args = List.map (fun ty -> prog.new_exp {exp=Exp.Hole;
                                               ty=ty;
                                               prev=Some hole.label;
                                               choices=Urn.empty}) doms in
  prog.set_exp hole.label {exp=Exp.App (func, args); ty=hole.ty_label; prev=hole.prev; choices=Urn.empty};
  args

