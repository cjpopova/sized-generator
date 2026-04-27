# higher order
- [x] remove polymorhpism (populate library with monomorphic vairants of list functions, etc)
- [ ] encourage closure sharing (something about variables being used more than once)
- [ ] allow higher-order types to be selected when building arrow types
- [ ] multary argument generation (see below)
- [ ] encourage more mutually recursive functions
- [ ] make large programs

# current
- [ ] we need to generate random input lists (in the printers) rather than hardcoding inputs

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

# 2026-04-27 Non termination of the generator
NON TERMINATING GENERATION SEEDS
let type_str = ref (Sexplib.Sexp.to_string (sexp_of_size_ty Library.list_func4))
size 10: 569280, 7382
size 8: 52008, 371485, 17213, 296056

let list_func1 = TyArrow(Q k, [tList k (tNat Inf)], tList k (tNat Inf)) (* ∀k. Listk Nat → Listk Nat*)
size 10: 990586, 688507

minimal example: $dune exec -- sized_generator -lang=ml -seed=874813 -size=8 -debug 2> out.txt
- size 8
- list_func2
- the only list-like things in gen_ml are the int list constructors & "(10 :: 50 :: [])"
- seeds: 874813, 649865, 944407

smaller: size=7 seed=201863

so this doesn't happen with listfunc3 or listfunc1, so the issue is in listfunc2 (i might have actually seen one error with listfunc1)

cause: might be that we are generating CASE (or let) expressions with zero fuel. according to the Urn paper (https://dl.acm.org/doi/epdf/10.1145/3122955.3122959) i suppose this might be possible
```
generate_exp: {hole<0> Γ ⊢ list i91 (int Inf) }
creating case with { Exp.var_name = "x86";
  var_ty =
  (Exp.TyCons ("list", [(Exp.TyCons ("int", [], Exp.Inf))], (Exp.SVar "k")))
  }
```

the nontermination rate is about ~0.5% when seup for the the minimal example above ... it is a lot smaller when all the other options are enabled



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