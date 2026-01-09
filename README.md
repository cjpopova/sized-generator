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

# Examples
Here is a minimal human readable example of what you might get from `dune exec -- sized_generator -n=1 -lang=rkt` if it generated the even/odd mutually recursive functions:

```
#lang racket

(define nat_min
  (λ x
    (define y (apply - x))
    (if (negative? y) 0 y)))

(define code-list
  (list
   (letrec ([even (λ (x) (match x [0 #t] [_ (define x2 (sub1 x)) (odd x2)]))]
            [odd (λ (x) (match x [0 #f] [_ (define x2 (sub1 x)) (even x2)]))]) even)))

(map (λ (code) (code 1)) code-list)
```

Same thing for ML:
```
[@@@ocaml.warning "-26-27-39"] (* supress unused variable, unused rec flag warnings ~ equivalent to ocamlc <thisfile> -w -26-17-39 *)
let nat_min (x : int) (y : int): int = if y >= x then 0 else (x-y);; (* defn of minus for naturals *)

let code_list = 
[
  (let rec even x = (match x with | 0 -> true | _ -> let xp = x-1 in odd xp)
  and odd x = (match x with | 0 -> false | _ -> let xp = x-1 in even xp)
  in even);
]

in List.map (fun code -> code 1) code_list
``