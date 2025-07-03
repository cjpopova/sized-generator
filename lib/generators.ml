type hole_info = Rules.hole_info
type rule_urn = Exp.rule_urn
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
         | Lambda (params, _) -> 
           (match node.ty with
            | FlatTyArrow (ty_params, _) -> List.combine params ty_params
            | _ -> raise (Util.Impossible "lambda does not have arrow type"))
         | Letrec (func, params, _) -> 
           (match node.ty with
            | FlatTyArrow (ty_params, _) -> (func, node.ty) :: List.combine params ty_params
            | _ -> raise (Util.Impossible "letrec does not have arrow type"))
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

(* CJP TODO 7/3: make choices explicit
choose : -> choice
produce : choice -> <producer function starting with unit eg rule whatever>

  in terms of singleton_generator, maybe not calling f until the sample step?

  currently, 
  type t = ((Exp.program -> hole_info -> rule_urn -> rule_urn) list)
  main : (string * Type.flat_ty) list -> t
  
  
  but then we need ???
  - 

  Another option: instead of rule_urn, have (string * rule) urn
  eg give a name to the function
  which can probably be provided by main or the generators here
  but only if we can list all elements of the urn

*)



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


let var_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let ref_vars = List.filter (fun b -> TypeUtil.is_same_ty (snd b) hole.ty_label) hole.vars in
  steps_generator prog hole acc
                  Rules.var_step weight ref_vars

let lambda_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  match hole.ty_label with
  | FlatTyArrow _ ->
    singleton_generator weight Rules.func_constructor_step prog hole acc
  | _ -> acc

let letrec_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  match hole.ty_label with
  | FlatTyArrow _ ->
    singleton_generator weight Rules.letrec_constructor_step prog hole acc
  | _ -> acc

let indir_call_ref_step weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let gamma_refs : ((Exp.var * Type.flat_ty) * Type.flat_ty list) list= List.filter_map
    (fun ref -> let (_, ty) = ref in 
    match (TypeUtil.ty_produces hole.ty_label ty) with
    | None -> None
    | Some (doms) -> Some (ref, doms))
    hole.vars in 
  steps_generator prog hole acc
                  Rules.indir_call_ref_step weight gamma_refs

let std_lib_steps std_lib_m weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let lib_refs = List.filter_map (* NOTE: this type filtering could be more efficient *)
    (fun ref -> let (_, ty) = ref in
      if (TypeUtil.is_same_ty hole.ty_label ty) || (Option.is_some (TypeUtil.ty_produces hole.ty_label ty)) then (Some ref) else None)
    std_lib_m in
  (* Debug.run (fun () -> Printf.eprintf ("std_lib_steps filtered refs: %s\n") 
    (List.fold_left (fun acc (name, _) -> name ^ " " ^ acc) "" lib_refs)); *)
  steps_generator prog hole acc
                  Rules.std_lib_step weight lib_refs

(********************************************************)

let main (std_lib_m : (string * Type.flat_ty) list) : t =
  [
    var_steps                       ( w_const 2.        );
    lambda_steps                    ( w_fuel_base 2. 1. );
    indir_call_ref_step             ( w_fuel_base 2. 1. );
    letrec_steps                    ( w_fuel_base 2. 1. );
    std_lib_steps std_lib_m         ( w_const 1.        );
  ]