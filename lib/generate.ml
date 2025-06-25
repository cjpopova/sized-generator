type worklist = {
    pop : unit -> Exp.exp_label option;
    add : int * Exp.exp_label-> unit;
  }
type state = {
    worklist : worklist;
    mutable fuel : int;
  }

type hole_info = Rules.hole_info

let make_state (fuel : int) : state =
  let holes = ref [] in
  let pop () =
    match !holes with
    | [] -> None
    | h ->
       let (hole, holes') = Choose.choose_frequency_split h in
       holes := holes';
       Some hole in
  let add e = holes := e :: !holes in
  {
    fuel = fuel;
    worklist = {
      pop = pop;
      add = add
    }
  }

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
    vars=Generators.find_vars prog e;
    depth=Generators.exp_depth prog e;
  } in
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
  sample_lp steps ()

let generate (steps : Generators.t) (st : state) (prog : Exp.program) : bool =
  match st.worklist.pop () with
  | None -> false
  | Some e ->
    let holes = generate_exp steps st.fuel prog e in (* one step *)
    List.iter (fun hole -> st.worklist.add (st.fuel + 1, hole)) holes; (* extend worklist w/ new holes and more fuel??*)
    (* Debug.run (fun () -> Exp.check prog); *)
    st.fuel <- if st.fuel > 0 then st.fuel - 1 else 0;
    true

let generate_fp (steps : Generators.t) (size : int) (ty : Type.flat_ty) : Exp.program = (* this is the entry point*)
let prog = Exp.make_program ty in
  let st = make_state size in
  st.worklist.add (st.fuel, prog.head);
  let rec lp () =
    match generate steps st prog with
    | false -> prog
    | true -> lp() in
  try
  lp()
  with
    Urn.EmptyUrn msg -> (PrettyPrinter.pretty_print prog; raise (Urn.EmptyUrn msg))