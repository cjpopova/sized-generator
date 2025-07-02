type hole_info = Rules.hole_info

(************************************ MAIN LOOP ************************************************)

let assert_hole (exp : Exp.exp) =
  match exp with
  | Exp.Hole -> ()
  | _ -> raise (Util.Impossible "worklist exp is not a hole")

let sample n = Random.float n

let generate_exp (steps : Generators.t) (fuel : int) (prog : Exp.program) (e : Exp.exp_label) =
  let node = prog.get_exp e in
  Debug.run (fun () -> assert_hole node.exp);
  let hole : hole_info = {
    label=e; (* e is the (label of the) hole we're going to fill*)
    ty_label=node.ty;
    prev=node.prev;
    fuel=fuel;
    vars=Generators.find_vars prog e; (* CJP TODO this should be gamma *)
    depth=Generators.exp_depth prog e; (* CJP this could also be tracked but w/e*)
  } in
  (* this need to replace w/ a sampling step that picks one choice from steps based on weight*)
  let steps = List.fold_left (fun acc g -> g prog hole acc) Urn.empty steps in
  let rec sample_lp urn =
    match Urn.remove_opt sample urn with
    | Some (_, base, rest) -> (
       try
         (match base with
          | Urn.Value v -> v
          | Urn.Nested urn -> sample_lp (urn()))
       with
         Urn.EmptyUrn _ -> sample_lp rest
    )
    | None -> raise (Urn.EmptyUrn (Format.sprintf "%s" (Type.show_flat_ty hole.ty_label))) in
  (* TODO: backtracking *)
  (* (Urn.sample sample steps) *)
  sample_lp steps () (* calls the selected rule *)

let rec generate (steps : Generators.t) (fuel : int) (prog : Exp.program) (e : Exp.exp_label) =
  let holes = generate_exp steps fuel prog e in (* one step *)
  let new_fuel = if fuel > 0 then fuel - 1 else 0 in
  List.iter (fun hole -> generate steps new_fuel prog hole) holes (* recurse over new holes returned by `generate_exp` *)

let generate_fp (steps : Generators.t) (size : int) (ty : Type.flat_ty) : Exp.program = (* this is the entry point*)
  let prog = Exp.make_program ty in
  try
    let _ = generate steps size prog prog.head in prog
  with
    Urn.EmptyUrn msg -> (PrettyPrinter.pretty_print prog; raise (Urn.EmptyUrn msg))