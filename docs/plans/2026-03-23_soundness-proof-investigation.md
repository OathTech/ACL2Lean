# Soundness Proof Investigation: Can We Verify the Rewriter?

Created: 2026-03-23

## Goal

The end state is a fully verified rewriter. For each imported ACL2
theorem, we produce a Lean proof that the kernel checks. The top-level
theorem form (from the verified rewriter plan):

```lean
theorem my_len_my_app (env : Env) :
    eval fuel simpleWorld env formula = SExpr.t := by
  have chain := applySteps_sound fuel simpleWorld env traceSteps
  simp [eval] at chain
  exact chain
```

The core soundness theorem:

```lean
theorem applyStep_sound (fuel : Nat) (w : World) (env : Env)
    (step : RewriteStep) (term : SExpr) :
    eval fuel w env (applyRewriteStep step term) = eval fuel w env term
```

## The Question

Can we prove `applyStep_sound` for the steps in our current trace
format? Specifically, can we do it for simple.lisp as a first test?

## simple.lisp Trace Analysis

The simple.lisp theorem `my-len-my-app` has two subgoals after
induction. Each subgoal is a clause with literals. For each literal
that simplifies to T, we have a chain of REWRITE-STEPs.

### Base case (Subgoal *1/2, 4 steps)

Starting literal: `(EQUAL (MY-LEN (MY-APP X Y)) (BINARY-+ (MY-LEN X) (MY-LEN Y)))`

```
1. definition:my-app  (MY-APP X Y) => Y
2. definition:my-len  (MY-LEN X) => '0
3. definition:fix     (FIX (MY-LEN Y)) => (MY-LEN Y)       [skipped — inner]
4. rewrite:unicity-of-0  (BINARY-+ '0 (MY-LEN Y)) => (MY-LEN Y)
```

Result: `(EQUAL (MY-LEN Y) (MY-LEN Y))` which is T by reflexivity.

### Inductive case (Subgoal *1/1, 7 steps)

Starting literal: same as base case

```
1. rewrite:commutativity-of-+  (on IH literal, skipped)
2. definition:my-app  (MY-APP X Y) => (CONS (CAR X) (MY-APP (CDR X) Y))
3. rewrite:cdr-cons   (skipped — inner)
4. definition:my-len   (MY-LEN (CONS ...)) => (BINARY-+ '1 (MY-LEN (MY-APP (CDR X) Y)))
5. definition:my-len   (MY-LEN X) => (BINARY-+ '1 (MY-LEN (CDR X)))
6. rewrite:commutativity-2-of-+  (skipped — inner)
7. rewrite:commutativity-of-+  (BINARY-+ (BINARY-+ '1 (MY-LEN (CDR X))) (MY-LEN Y))
                                => (BINARY-+ '1 (MY-LEN (MY-APP (CDR X) Y)))
```

Result: `(EQUAL X X)` where both sides are `(BINARY-+ '1 (MY-LEN (MY-APP (CDR X) Y)))`.

## What Each Step Type Needs for Soundness

### Definition steps (rune `:DEFINITION`)

The step says `(f args) => result`. This is justified by:
1. `f` is in `w.defs` with formals and body
2. `eval` of `(f args)` unfolds to `eval` of `body[formals:=args]`
3. The `result` is what `body[formals:=args]` simplifies to under
   the current clause context

**The hard part:** Step 3. The definition step doesn't just unfold —
it unfolds AND simplifies. The RHS `Y` in step 1 isn't the raw body
of `my-app`; it's the result of evaluating the body with the type-alist
knowledge that `(CONSP X)` is false (the base case assumption).

To prove this step sound, we need:
```lean
∀ env, ¬(Logic.toBool (Logic.consp (env.get X))) →
  eval fuel w env (my-app-call X Y) = eval fuel w env Y
```

This requires:
- Unfolding the `my-app` definition
- Showing the IF test `(consp X)` evaluates to NIL (from the clause assumption)
- Showing the IF takes the else branch, producing `Y`

This is multiple eval steps, but they're mechanical given the
definition body and the clause context.

### Rewrite rule steps (rune `:REWRITE`)

The step says `LHS => RHS`. Justified by a previously proved theorem.

For `unicity-of-0`: `(BINARY-+ '0 X) = (FIX X)`. And since `(MY-LEN Y)`
is always a number (type-prescription), `(FIX (MY-LEN Y)) = (MY-LEN Y)`.
So `(BINARY-+ '0 (MY-LEN Y)) = (MY-LEN Y)`.

For `car-cons`, `cdr-cons`: These are axioms in `Logic.lean`:
```lean
theorem car_cons (a d : SExpr) : car (cons a d) = a := rfl
theorem cdr_cons (a d : SExpr) : cdr (cons a d) = d := rfl
```

For `commutativity-of-+`: `(+ A B) = (+ B A)`. This needs a proof
about `Logic.plus` being commutative. We don't have this in `Logic.lean`
yet but it's provable from the rational arithmetic definition.

### The congruence lemma

All step types need: replacing a subterm preserves eval.

```lean
theorem replaceFirst_eval_congr (fuel : Nat) (w : World) (env : Env)
    (term lhs rhs : SExpr)
    (h : eval fuel w env lhs = eval fuel w env rhs) :
    eval fuel w env (replaceFirst term lhs rhs) = eval fuel w env term
```

This is the KEY lemma. It says: if `eval(lhs) = eval(rhs)`, then
replacing `lhs` with `rhs` anywhere in `term` preserves eval.

**This is NOT trivially true.** `eval` is not compositional in the
simple sense — `eval(f(a))` doesn't decompose into `f(eval(a))` for
arbitrary terms. SExpr terms are DATA, and eval interprets them. The
congruence only holds because `replaceFirst` replaces a subterm that
eval will eventually reach and evaluate the same way.

Proving this requires structural induction on `term`, showing that
for each position where `lhs` might appear, the replacement preserves
eval. This is doable but requires careful reasoning about how eval
traverses the term structure.

### The fuel problem

All theorems are parameterized by `fuel`. The step `(my-app X Y) => Y`
is only valid for "sufficient fuel" — enough to unfold my-app's
definition and simplify the IF. The fuel needed depends on the depth
of the computation.

Options:
1. **Existential:** `∃ N, ∀ fuel ≥ N, eval fuel w env (applyStep ...) = ...`
2. **Monotonicity:** Prove eval is monotone in fuel: if it terminates
   at fuel N, it gives the same result for all fuel > N. Then quantify
   over "sufficient fuel."
3. **Specific fuel:** For each theorem, compute the specific fuel needed.

Option 2 is the cleanest for the general theory.

## Critical Issues Found in Review

### The congruence lemma is FALSE as stated

`replaceFirst` does syntactic subterm replacement, but `eval` does
NOT evaluate all subterms. Counterexample: QUOTE.

```
term = (QUOTE (BINARY-+ X Y))
lhs  = (BINARY-+ X Y)
rhs  = (BINARY-+ Y X)
```

`replaceFirst` finds `(BINARY-+ X Y)` inside the QUOTE and replaces it.
But `eval (QUOTE expr)` returns `expr` as raw data without evaluating.
So `eval(QUOTE (+ X Y))` ≠ `eval(QUOTE (+ Y X))` — they're different
SExpr values even though `eval(+ X Y) = eval(+ Y X)`.

**Fix:** Restrict the congruence to "eval-reachable positions" — positions
that eval actually traverses during evaluation. Or prove specific
replacement lemmas per step type rather than a general congruence.

### The soundness theorem needs clause context

The theorem `eval(applyStep step term) = eval(term)` is wrong as
stated. Definition steps depend on branch assumptions:

`(MY-APP X Y) → Y` is only valid when `¬(CONSP X)`.

The correct statement needs hypotheses:
```lean
theorem applyStep_sound (fuel : Nat) (w : World) (env : Env)
    (step : RewriteStep) (term : SExpr)
    (h_justified : eval fuel w env step.lhs = eval fuel w env step.rhs) :
    eval fuel w env (applyRewriteStep step term) = eval fuel w env term
```

This factors the problem: (1) congruence given the hypothesis, and
(2) proving the hypothesis for each specific step and context.

### Fuel monotonicity is non-standard

`eval` returns `.nil` for BOTH fuel exhaustion AND legitimate nil
results (e.g., `eval fuel w env .nil = .nil`). Cannot distinguish
"needs more fuel" from "correctly returned nil."

This means `eval 1 w env (IF NIL X Y)` might return nil (fuel
exhaustion in Y) while `eval 2 w env (IF NIL X Y)` returns the
correct non-nil value. The nil at fuel=1 is indistinguishable from
a legitimate nil result.

**Fix options:**
- Refactor `eval` to return `Option SExpr` (None for fuel exhaustion)
- Use existential fuel: `∃ N, ∀ n ≥ N, eval n w env t = v`
- Track fuel sufficiency separately

### IF-TEST events needed as proof witnesses

The current rewriter ignores IF-TEST events (filtered out by
`ProofStep.rewriteSteps`). But these carry critical information:
they record WHICH branch ACL2 took during IF processing, justified
by the type-alist. Without them, the soundness proof has no record
of branch decisions that justify definition steps.

### Recommended starting point (revised)

Do NOT start with the congruence lemma (it's false as stated). Instead:

1. **Prove the base case directly** — unfold eval step by step for
   the specific formula under specific clause assumptions. This tells
   you what infrastructure you actually need.
2. **Prove arithmetic lemmas** (plus_zero_left, commutativity) since
   they're self-contained. Note: these require reasoning through
   `toRat`/`mkNumber` GCD normalization.
3. **Formalize clause context** — what it means for other literals to
   be false, and how that constrains env.
4. **Address the fuel problem early** — either refactor eval or adopt
   existential fuel bounds.
5. **THEN tackle replacement lemmas**, armed with knowledge of what
   positions actually need replacement.

## Feasibility Assessment

### What we HAVE
- `eval` function (total, fuel-parameterized)
- `Logic.*` lemmas (car_cons, cdr_cons, etc.)
- `replaceFirst` function (structural)
- The World with function definitions
- The trace with composable steps (for simple.lisp)

### What we NEED to build
1. **Congruence lemma** for replaceFirst + eval — the hardest part
2. **Eval monotonicity** for the fuel parameter
3. **Per-rune justification lemmas:**
   - Definition unfolding: follows from eval's function call semantics
   - car-cons, cdr-cons: already in Logic.lean
   - unicity-of-0: `(+ 0 x) = (fix x)` — needs proof about Logic.plus
   - commutativity-of-+: `(+ a b) = (+ b a)` — needs proof about Logic.plus
   - commutativity-2-of-+: `(+ x (+ y z)) = (+ y (+ x z))` — same
4. **Clause context handling** for definition steps that depend on
   branch assumptions

### Assessment

The soundness proof IS feasible for simple.lisp. The main challenges:

1. **The congruence lemma** (replaceFirst preserves eval) is the
   mathematical core. It requires structural induction on SExpr terms
   and reasoning about eval's traversal. Estimated: significant but
   doable, maybe 100-200 lines of Lean.

2. **Arithmetic lemmas** (commutativity, unicity-of-0) need proofs
   about `Logic.plus` which uses rational arithmetic via `toRat`/`mkNumber`.
   These are provable but require careful reasoning about the
   number representation. Estimated: 50-100 lines each.

3. **Eval monotonicity** is standard but tedious — prove by induction
   on the fuel parameter that adding more fuel doesn't change the
   result. Estimated: 50-100 lines.

4. **Clause context** (for definition steps) requires formalizing the
   notion "this step is valid under the assumption that literals L1..Ln
   are false." This is the soundness-proof version of the branch
   assumption problem. For simple.lisp it's manageable (just one
   induction with two cases).

### Recommended starting point

Start with the base case of `my-len-my-app` on simple.lisp:
1. Prove the congruence lemma (general, reusable)
2. Prove the 4 base-case steps sound (specific to simple.lisp but
   establishes the pattern)
3. Show they compose to prove the literal equals T
4. Then generalize to the inductive case (needs induction principle)

This gives us a concrete end-to-end proof while identifying what
infrastructure needs to be built for the general case.
