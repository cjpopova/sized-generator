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
    | None -> raise (Urn.EmptyUrn (Format.sprintf "%s" (show_flat_ty hole.ty))) in
  sample_lp steps () (* calls the selected rule *)

let generate_fp (steps : generators_t) (size : int) (ty : flat_ty) : exp = (* this is the entry point*)
  let hole : hole_info = {
    fuel=size+1;
    env=[];
    depth=0;
    ty=ty
  } in
  let rec generate_exp_wrapper (hole: hole_info) : exp = 
      let hole = { hole with 
        fuel = if hole.fuel > 0 then hole.fuel - 1 else 0;
        depth = hole.depth+1
      } in
      generate_exp (List.map (fun s -> s generate_exp_wrapper) steps) hole
    in
  try
    generate_exp_wrapper hole
  with
    Urn.EmptyUrn msg -> raise (Urn.EmptyUrn msg)
