Debug.debug_mode := true;;
let p = Generate.generate_fp (Generators.main) 10 
  (* (FlatTyArrow ([Type.FlatTyInt], Type.FlatTyInt))  *)
  Type.FlatTyInt
in PrettyPrinter.pretty_print p;;
