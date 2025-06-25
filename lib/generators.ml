type hole_info = Rules.hole_info
type rule_urn = (unit -> Exp.exp_label list) Urn.t
type t = ((Exp.program -> hole_info -> rule_urn -> rule_urn) list)

(************************************ HELPERS ************************************************)

(* finds all the variables in scope of a hole *)
let find_vars (prog : Exp.program) (e : Exp.exp_label) =
  let rec find_binds (e : Exp.exp_label) =
    match (prog.get_exp e).prev with
    | None -> []
    | Some ep ->
      let node = prog.get_exp ep in
      let exp_binds =
        match node.exp with
         | Let (x, rhs, body) ->
           if (e == body)
           then [(x, (prog.get_exp rhs).ty)]
           else []
         (* | Match (scr, _, (fst, rst, body)) ->
           if (e == body)
           then let lst_ty = (prog.get_exp scr).ty in
                match prog.ty.get_ty lst_ty with
                | TyList ty' -> [(fst, ty'); (rst, lst_ty)]
                | _ -> raise (Util.Impossible "match scrutinee does not have list type")
           else []*)
         | Lambda (params, _) -> 
           (match node.ty with
            | FlatTyArrow (ty_params, _) -> List.combine params ty_params
            | _ -> raise (Util.Impossible "lambda does not have arrow type"))
         | _ -> [] in
      exp_binds @ find_binds ep
  in
  find_binds e

let exp_depth (prog : Exp.program) (e : Exp.exp_label) =
  let rec exp_depth' e acc =
    let node = prog.get_exp e in
    match node.prev with
    | None -> acc
    | Some e' -> exp_depth' e' (acc + 1) in
  exp_depth' e 0

(************************************ TRANSITIONS ************************************************)

let steps_generator (prog : Exp.program) (hole : hole_info) (acc : rule_urn)
                    (rule : Exp.program -> hole_info -> 'a -> unit -> Exp.exp_label list)
                    (weight : hole_info -> 'a -> float)
                    (collection : 'a list) =
  List.fold_left (fun acc a ->
                  Urn.insert acc (weight hole a) (Urn.Value (rule prog hole a)))
             acc collection

let singleton_generator weight f prog hole acc =
  Urn.insert acc (weight hole ()) (Urn.Value (f prog hole))

(************************************ WEIGHTS ************************************************)


let c (w : float) (_ : hole_info) _ = w
let w_const n = c n
let w_fuel_base n m (hole : hole_info) _ = Int.to_float hole.fuel *. n +. m
let w_fuel_depth (hole : hole_info) _ = Int.to_float (max 0 (hole.fuel - hole.depth))

let w_fuel n = w_fuel_base n 0.

(************************************ GENERATORS ************************************************)

let base_constructor_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  (* TODO: sample base type (in this case, just Int) *)
  match hole.ty_label with
  | FlatTyInt ->
     let vals = [Exp.ValInt 0; Exp.ValInt 1; Exp.ValInt 2; Exp.ValInt (-1); Exp.ValInt 42] in
     steps_generator prog hole acc
                     Rules.base_constructor_step weight vals
  | _ -> acc

  let var_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let ref_vars = List.filter (fun b -> Type.is_same_ty (snd b) hole.ty_label) hole.vars in
  steps_generator prog hole acc
                  Rules.var_step weight ref_vars

let lambda_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  match hole.ty_label with
  | FlatTyArrow _ ->
    singleton_generator weight Rules.func_constructor_step prog hole acc
  | _ -> acc



let main : t =
  (* fun std_lib_m -> *)
  [
    base_constructor_steps          ( w_const 2.        );
    var_steps                       ( w_const 2.        );
    lambda_steps                    ( w_fuel_base 2. 1. );
    (* std_lib_steps std_lib_m         ( w_const 1.        );
    not_useless_steps               ( w_fuel_base 2. 1. );
    let_insertion_steps             ( w_fuel_depth      );
    palka_rule_steps                ( w_fuel 2.         );
    std_lib_palka_rule_steps        ( w_fuel 2.         );
    s Rules.ext_function_call_step  ( w_fuel 1.         );
    (* s Rules.function_call_step      ( w_fuel 1.         );*)
    palka_seq_steps                 ( w_fuel 1.         ); *)
  ]