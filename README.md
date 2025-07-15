
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
OCAMLRUNPARAM=b dune exec -- palka_stlc
```
or:
```
dune utop lib
open DebugLibrary;;
generate_exp_wrapper <hole>
```