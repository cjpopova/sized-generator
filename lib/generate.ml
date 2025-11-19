open Exp;;
(************************************ MAIN LOOP ************************************************)

let sample n = Random.float n

let generate_exp (steps : (hole_info -> rule_urn -> rule_urn) list) (hole : hole_info) : exp = 
  let steps = List.fold_left (fun acc g -> g hole acc) Urn.empty steps in
  let rec sample_lp urn = (* TODO: replace w/ Justine's *)
    match Urn.remove_opt sample urn with
    | Some (_, base, rest) -> (
       try
         (match base with
          | Urn.Value v -> v
          | Urn.Nested urn -> sample_lp (urn()))
       with
         Urn.EmptyUrn _ -> sample_lp rest
    )
    | None -> raise (Urn.EmptyUrn (Format.sprintf "%s" (show_size_ty hole.ty))) in
  sample_lp steps () (* calls the selected rule *)

let generate_fp (steps : generators_t) (size : int) (tys : size_ty list) : exp list = (* this is the entry point*) (* NOTE: CHANGED TO LISTS*)
  (* assume pre-allocated list of names for mutually recursive functions.
  for the sake of simplicity, I will assume the type is identical to the start type 
  assume: list of length 2*)
  (* let mutuals = [new_var ty; new_var ty] in  *)

  (* let hole : hole_info = {
    fuel=size+1;
    env=[];
    depth=0;
    ty=ty
  } in *)
  (* todo some kind of loop to generate each mutual w/ friends in its environment *)
  let rec generate_exp_wrapper (hole: hole_info) : exp = (* generate_exp_wrapper : generate_t *)
      let hole = { hole with 
        fuel = if hole.fuel > 0 then hole.fuel - 1 else 0;
        depth = hole.depth+1
      } in
      Debug.run (fun () -> Printf.eprintf ("generate_exp: %s\n") (show_hole_info hole));
      generate_exp (List.map (fun s -> s generate_exp_wrapper) steps) hole
    in
  try
    (* note: right now, I am hardcoding 2 mutually recursive functions. this should be generalized to as many as necessary, and need a function to get something like the 
    powerset or all combinations of elements in the list to populate the environment*)
    match tys with
    | [ty1; ty2] -> (* TODO: inconsistency between vars & tys*)
      (let hole1 : hole_info = {
        fuel=size+1;
        env=[ty2];
        depth=0;
        ty=ty1
      } in
      let hole2 : hole_info = {
        fuel=size+1;
        env=[ty1];
        depth=0;
        ty=ty2
      } in
    [
      Rules.letrec_constructor_step generate_exp_wrapper hole1 () (* force letrec as first rule *) ;
      Rules.letrec_constructor_step generate_exp_wrapper hole2 () (* force letrec as first rule *) ;
      
    ])
  | _ -> raise (Util.Unimplemented (Format.sprintf "Supports exactly 2 mutually recursive functions" ))
  with
    Urn.EmptyUrn msg -> raise (Urn.EmptyUrn msg)
