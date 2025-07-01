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

(* Creates function call/application *)
let function_call_step (prog : Exp.program) (hole : hole_info) = 
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating function call (fuel=%n)\n") hole.fuel);
  let n = Int.of_float (sqrt (Float.of_int (Random.int hole.fuel))) + 1 in
  let tys = List.init n (fun _ -> TypeUtil.random_type (hole.fuel / n) prog) in (* random types for the arguments. these will be smaller than fuel*)
  let func = prog.new_exp {exp=Exp.Hole;
                           ty=(FlatTyArrow (tys, hole.ty_label)); (* function : args -> hole_type*)
                           prev=Some hole.label;
                           choices=Urn.empty} in
  let args = List.map (fun ty -> prog.new_exp {exp=Exp.Hole;
                                               ty=ty;
                                               prev=Some hole.label;
                                               choices=Urn.empty}) tys in
  let holes = [func] @ args in
  prog.set_exp hole.label {exp=Exp.App (func, args); ty=hole.ty_label; prev=hole.prev; choices=Urn.empty};
  holes

