(* random stuff used for debugging RACKET backend with utop *)
open Exp;;
open Library;;
open Gen_racket;;

Debug.debug_mode := true

let steps : generators_t = (Generators.main {std_lib = std_lib; data_cons = data_constructors})

let rec generate_exp_wrapper (hole: hole_info) : exp = 
  let hole = { hole with 
    fuel = if hole.fuel > 0 then hole.fuel - 1 else 0;
    depth = hole.depth+1
  } in
  Debug.run (fun () -> Printf.eprintf ("generate_exp: %s\n") (show_hole_info hole));
  Generate.generate_exp (List.map (fun s -> s generate_exp_wrapper) steps) hole

let example_hole = {
  fuel=10;
  env=[];
  depth=0;
  ty=(TyArrow(Q (SVar "k"), [tList (SVar "k") (tNat Inf)], tList (SVar "k") (tNat Inf)))}

(**********************************************************)

let head_ty = [tList i tX] --> tX
let tail_ty = [tList i tX] --> tX
let take_ty = [tList i tX; tNat Inf] --> tList i tX


(**********************************************************)

let k = SVar "k"
let j = SVar "j"
let khat = SHat k
let jhat = SHat j

let tBoolInf = TyCons ("Bool", [], Inf)

(**********************************************************)


