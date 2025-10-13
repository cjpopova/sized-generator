# Sized types for program generation
A well-typed program generator framework written in OCaml.

Currently targets Racket.

# Build instructions
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
dune exec -- sized_generator
```


to debug:
```
OCAMLRUNPARAM=b dune exec -- sized_generator
```
or:
```
dune utop lib
open DebugLibrary;;
generate_exp_wrapper <hole>
```