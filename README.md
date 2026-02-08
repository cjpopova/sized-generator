# Sized types for program generation
A sized-typed program generator framework written in OCaml focused on generating recursive, terminating programs.

Languages targeted: Racket, ML SML

# Install
Opam
```
opam init
opam install dune alcotest ppx_deriving sexplib ppx_sexp_conv
core async?
```
The minimum OCaml version is 5.1

# Build/run
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

# Command line options

## Lang, type, and input
These 3 arguments are connected: type is the σ target type to generate; input is how to call a function of that type in that language.

Input: a string of code that calls a function `code` with your arguments in the syntax for the selected language. for example, 
```
(code 5 7)          sml or ml: int -> int -> _
((code 100) 42)     rkt : int -> int -> _
code [100; 42]      ml : int list -> _
```


Type: a sexp string of a sized type. This is the best way to get a string for a given type:
```
#require "ppx_sexp_conv";;
open Exp;;
<build a size_ty, eg Library.nat_func1 >
Sexplib.Sexp.to_string (sexp_of_size_ty Library.nat_func1);;
```

## Test types
- 430: disable production rules not supported by 430's subset of racket & modify racket printing to support etna testing
- 3027: modify racket printing to use racket/base instead of racket; import racket/match
- 0 or any other integer: default production rules & printing


# Example of using the shrinker
```
cd sized_generator; mkdir tmp
dune exec -- sized_generator -lang=rkt -seed=12345 -size=10 -input="(code 5 9)" > tmp/starter_code.rkt
dune exec -- sized_generator -lang=rkt -seed=12345 -size=10 -sexp-print > tmp/starter_sexps.txt
dune exec -- shrinker -input_exp_f tmp/starter_sexps.txt -output_exp_f tmp/next_sexps.txt -output_code_f tmp/next_code.rkt -lang=rkt -input="(code 5 9)" -variant=-1
```