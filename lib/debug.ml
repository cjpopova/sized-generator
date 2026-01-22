let check_sizes = ref false
let test_type = ref 1

let debug_mode = ref false

let run f =
  if !debug_mode
  then f()
  else ()


let say f =
  if !debug_mode
  then Printf.eprintf (f())
  else ()
