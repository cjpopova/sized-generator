
A well-typed program generator framework written in OCaml.



Required:
```
ocaml
dune
utop (opam install utop)
```


to build:
```
dune build
```

to run:
```
dune exec -- palka_stlc
```


to debug:
```
dune utop lib
...
Debug.debug_mode := true;;
let p = Generate.generate_fp (Generators.main) 100 Type.FlatTyInt in PrettyPrinter.pretty_print p;;
```

Alternatives:
```
Debug.debug_mode := true;;
let p = Generate.generate_fp (Generators.main) 100 (FlatTyArrow ([Type.FlatTyInt], Type.FlatTyInt)) in PrettyPrinter.pretty_print p;;
```

```
OCAMLRUNPARAM=b dune exec -- palka_stlc
```