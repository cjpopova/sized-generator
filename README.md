# Sized types for program generation
A sized-typed program generator framework written in OCaml focused on generating recursive, terminating programs.

Languages targeted: Racket, ML

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
use -h to display command line options

to debug:
```
OCAMLRUNPARAM=b dune exec -- sized_generator
```
or:
```
dune utop lib
open DebugLibrary;;
generate_exp_wrapper example hole;;
```