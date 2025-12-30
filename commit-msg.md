# next steps (big picture)
- implement tracers in new lang backend
- finish analysis on the NLREC branch and merge into main
- implement the nonlocal alternative for mutual rec

# Mutual recursion 

message: Implement naive mutual recur & language backends

- naive mutual recursion for exactly =2 functions will make the functions available in each other's environments
- force letrec_constructor step as the first rule
- implement new language backends for printing in gen_racket, gen_ml


## outstanding issues
TODO: why can't i crash the tracer when it's running for too long? i think it's something to do with calling sys.command, but maybe it's a combo of running it thru dune exec ...
- https://discuss.ocaml.org/t/app-doesnt-respond-to-ctrl-c-sigint-signals-when-running-dune-exec/2908


## implementation of analysis in debugLibrary.ml
```
(* 
assumptions/requirements
- should work on nonlocal mutual recursion generator, too
- can probably assume function name prefix on mutuals, which means we might not need to build an environment of them first

planning
- the exp dump can probably also dump the names of the top-level mutually recursive identifiers for me
- it would be nice if i can also dump the types of things somewhere so it's easier to debug
- metric = how many times is X called from Y? how many times is X called from X? how many times do X AND Y call EACH OTHER?


what if we just construct a call graph of (var, var, int) list (where int represents the # of times X calls Y) and then 
  implement a simple algorithm to check if there are edges from A to B and back (and self-edges are also OK)

  https://backtracking.github.io/ocamlgraph/ocamlgraph/Graph/index.html
  https://anwarmamat.github.io/ocaml/ocamlgraph/
*)

(* assumes *)
type mut_rec_info = {
  mutable a_calls_b : int list;
  mutable b_calls_a : int;
  mutable a_self_call : int;
  mutable b_self_call : int;
}

(* get the variables/function names representing the top-level mutually recursive functions*)
(* let get_top_level_muts (es : exp list) : var list = failwith "Not implemented"

let rec analyze_mutual_recursion (es : exp list) : int =
  let mutuals = get_top_level_muts es in (* initialize the environment*)
   *)
```




# pre-December
- [ ] tuning
  - [ ] discourage nested letrecs in the current form inside loops because they will probably get optimized out anyway?
  - [ ] increase weight of recursive apps 
  - [ ] decrease weight of letrecs themselves
- [ ] experiment with non size preserving functions
- [ ] look at patterns of optimizations


## notes
I believe an invariant of the simple size algebra system (S = v | S^ | ∞ ) is:
□ : T and ∀ (x, τ) ∈ Γ, if x is not a function, then |_T_| = |_τ_|                // abuse of |_s_|notation 
ie the hole and the non-function elements of the environment have the same base size variable
however, if x is a function, then its quantifier is fresh


## changes necessary for racket-style printer
- [ ] better arguments to start with (replace default 100/42)

```
Starting program (application at the end is for fun): 
(letrec ([x61 (λ (x62)
                (match x62
                  [0 0]
                  [(? positive?)
                   (let ([x63 (sub1 x62)])
                     (x61 x63))]))])
   (x61 100))

What we need to track

(define hsh (make-hash)) <---------------------

(letrec ([x61 (λ (x62)
                (match x62
                  [0 0]
                  [(? positive?)
                   (let ([x63 (sub1 x62)])
                     (hash-set! hsh x61 (add1 (hash-ref hsh x61 ))) ; before recursive app, update
                     (x61 x63))]))])
  (hash-set! hsh x61 0) ; in the body of the letrec, initialize & print
  (x61 100)
  (displayln (hash-ref hsh x61)))
```








for later
- [ ] figure out higher order polymorphism issues 
  - [ ] lots of places in generator have disabled higher-order scenarios
  - [ ] only check reachable for constructors & recursive applications (we can change calls of `ty_produces` in library calls to `ty_unify_producer` to skip reachable check)
- [ ] add more datatypes (eg Tree)
- [ ] reintroduce useful rules like LET. IF will be covered by match as long as we can make the head expr of a case expression more complex
- [ ] see features listed in ~meeting-notes/global-todo
- [ ] how to formulate types like INT inductively? rocq has something like variant = neg nat | pos nat. this wouldn't work directly in our system with TyCons because we're not allowed to put sizes inside nested data structure. i think nested inductives are allowed in CIC^ according to "Is Sized Tying for Coq practical" p. 5
- [ ] justine's urn implementation (also rewrites interface between generator & rule)
- [ ] racket-style printer
- [ ] agda-style printer for sized typechecking?

making useful programs
- [ ] need to encourage pattern of case right after letrec/lambda
- [ ] how to produce safe code (eg list-ref within bounds)
- [ ] how to produce more interesting code than ID functions (provide extra arguments?)
- [ ] encourage match on the argument of the function (instead of a different variable from the environment)

## not-useless-recursion
this is our comparison program generator: not-useless with recursion, but no sized types

changes necessary:
- encourage recursive applications/calls
- interface might be inconsistent w/ Justine's/current because it was based on Ben's





## validation
- no sizes on contents
- recursive calls not too big
- types of functions are reasonable (eg can't have letrec : k -> k^ )










# Type unification & parametric polymorphic data types:
`Cons \Pi X : X -> List X -> List X`

The target type will NOT have type variables, eg `forall k . List k Nat -> List k Nat` has the List type instantiated already. so unification will occur when trying to match constructors or std lib functions
this is hopefully first order?? are we ever going to deal with more than one type variable?

https://www.cs.cornell.edu/courses/cs3110/2011sp/Lectures/lec26-type-inference/type-inference.htm
this also has some interesting `match` reference patterns includine `|` and `as`

In Not Useless:
could USE polymorphic functions, but couldn't generate them. for example, seq, foldr are allowed. 
seq is OK because the first expression is independent, whereas they don't have Let because it's just difficult to ensure that the newly bound variable gets used depending on the type selected.

requirements for unification:
1. everytime a polymorphic function is used, we have to 
  fresh its variables (eg each instantion has new variables which are not shared with other instantions)
  unify the hole_ty with the variable s.t. it's instantiated
2. their implementation uses the mutability built into UnionFind because of nonlocality. i don't need this. i can just make the substitution immediately

## implementation
how do we respect subtype ordering (and swapping left & right)
of contrapositivity
with x,t

```
τ ⊑ T
--------------------- (VAR)
Γ, x : τ ⊢ □ : T ↝ x

where ⊑ is now can_unify
and unify sets that variable



can_unify : size_ty -> size_ty -> (string * size_ty) Option

can_unify τ T = (X β)
such that τ[X:=χ] = T
basically the T-App rule?


unify (T-App) : size_ty -> string -> size_ty -> size_ty

unify τ X χ = τ[X:=χ]
basically subst
```


new psuedocode for is_size_subtype_ty
```
match (maybe, target) with
| _, TyVar -> true
... rest of the cases remain the same
```

new psuedocode for produces
```
Previously, 2 cases on size_ty quantifiers: one required substitution & other didn't
now will introduced possible substitution on TyVar
Why is this necessary in my system but not inNot Useless?
seems like a lot of overhead
maybe there is some mutability w/ union find that causes tvars to be instantiated
there is some hack going on where ty_of_external_ty is going to make fresh type variables (see knotty crimes) every time it's called so every instantiation is fresh
so the question is where does the relation between hole_ty and the fresh variables happen

ext_refs : (float * (string * External.ty)) list
```




Affected rules
- std_lib_steps - ty_produces
- base std lib steps - is_size_subtye
- recur & base constructors - ty_produces




