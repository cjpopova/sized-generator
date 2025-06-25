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
  prog.set_exp hole.label {exp=exp'; ty=hole.ty_label; prev=hole.prev};
  []
  (*match prog.ty.get_ty hole.ty_label with
  | TyInt ->
     fun () ->
     set exp'; []
  | _ -> raise (Util.Impossible "bad base type")*)


let var_step (prog : Exp.program) (hole : hole_info) (var, _) =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating var reference\n"));
  prog.set_exp hole.label {exp=Exp.Var var; ty=hole.ty_label; prev=hole.prev};
  []

(* Creates a lambda *)
let func_constructor_step (prog : Exp.program) (hole : hole_info) =
  let set exp = prog.set_exp hole.label {exp=exp; ty=hole.ty_label; prev=hole.prev} in
  match hole.ty_label with
  | FlatTyArrow (ty_params, ty') ->
     fun () ->
     Debug.run (fun () -> Printf.eprintf ("creating lambda\n"));
     let xs = List.map (fun _ -> prog.new_var ()) ty_params in
     let body = prog.new_exp {exp=Exp.Hole; ty=ty'; prev=Some hole.label} in
     set (Exp.Lambda (xs, body));
     [body]
  | _ -> fun () ->
         raise (Util.Impossible "function constructor on non-function type")

