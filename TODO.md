# higher order
- [ ] now i need to test SML/NJ, because the printout extraction in compare-langs is broken

4/20
- [ ] we need to parallelize running stuff in ml compilers because they're slow - but this will be a massive pain with writing output to file - we need multiprocessing to take advantage of multiple cores & therefore outputs will be written to separate files (or logs) which we could  join together later

- [ ] also we need to share libraries as much as possible - only printers should be different, and maybe some filtering on libraries to change relevant functions

- [ ] we need a haskell printer

- add higher order
- [x] remove polymorhpism (populate library with monomorphic vairants of list functions, etc)
- [ ] encourage closure sharing (something about variables being used more than once)
- [ ] encourage more mutually recursive functions
- [ ] make large programs

# feature list
- [ ] lists
- [ ] extend support for multary function generation (APP_REF, LET_FUNC, FRESH_CALL_REF)
- [ ] higher order (map, fold, etc) - only check reachable for constructors & recursive applications (we can change calls of `ty_produces` in library calls to `ty_unify_producer` to skip reachable check). remove unifier.ml when done
- [ ] mutual recursion the right way

deprioritized
- [ ] finish let_base (see below - i am not sure what was missing - HO?)
- [ ] subtyping?
  - [ ] Jonathan Chan mentioned even more subsizing - see 2025-dec-njpls.md
- [ ] user-defined datatypes printing not tested; likely needs header
- [ ] add more datatypes, eg trees


strictly future work
- [ ] backend for c/c++
- [ ] expressive size algebra (eg addition of multiple size vars for append)
- [ ] sized contents (eg tracking the size of contents of a list, etc) (this could also be a way of expressing variants, eg the way we need positive/negative variants of natual numbers to express ints, but the variant is a sort of contain that can't have opaque size)
- [ ] nested or mutually inductive data types
- [ ] codata and sequences

  see [2025-07-24](~/meeting-notes/sized-generator-meetings/2025-07-24-ll.md) for commentary on usefulness/complexity of these features


# shrinker
improving the shrinker:
- python->ocaml -step i -variant i
- ocaml->python: stderr message when run out of variants in a step

debugging:
```
dune exec -- shrinker -input_exp_f ../../multistep/original_sexp_2rec.txt -output_exp_f ../../multistep/output_sexp.txt -output_code_f ../../output-code.rkt -lang=rkt -input="(code 5 9)" -variant=-1

dune exec -- shrinker -input_exp_f ../../tmp-shrinker/m66/sexps_after_constify_let_binding.txt -output_exp_f ../../tmp-shrinker/m66/next-sexps.txt -output_code_f ../../tmp-shrinker/m66/next-code.sml -lang=sml -input="(code 5 9)" -variant=-1

```
- [ ] add an option to the shrinker print out code from SEXP



# Implement LET_BASE
- [x] replace Exp.NLetrec with Exp.Let which handles both base and function type let-bindings
- [ ] see size_subst problem in meeting notes