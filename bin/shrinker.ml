open Exp
open Library
open Analysis

(******************* PARAMETERS ********************)

let input_exp_f = ref ("")
let output_exp_f = ref ("")
let output_code_f = ref("")
let speclist =
[
  ("-input_exp_f", Arg.Set_string input_exp_f, "input_exp_f");
  ("-output_exp_f", Arg.Set_string output_exp_f, "output_exp_f");
  ("-output_code_f", Arg.Set_string output_code_f, "output_code_f");
]

(************** GENERATE *********************)
let () =
  Arg.parse speclist (fun _ -> ())
    "sized_generator [-n <1>] [-size <10>] [-seed <-1>] [-lang <ml>]";
  (* TODO: fix the strings above for args parsing *)
  
  (* generate initial exp by calling generate (hard coded for now) *)

  let init_exps = [ExtRef ("hi", tNat Inf)] in


  let rec shrink(curr_exps) = 
    let new_exps = shrinker curr_exps in
    

  



Printf.printf "==================\n";
