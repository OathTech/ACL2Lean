# Next Steps: Foundations First

Created: 2026-03-26
Updated: 2026-03-26 — Completed workstream A. Dropped `eval` in favor of `evalOpt`.

## Where we are

The soundness experiment (branch `mdd/soundness-experiment`) explored
a "check-and-replace" architecture: evaluate both sides of a rewrite
step, compare them, apply syntactic replacement, prove this preserves
evaluation. The top-level chain (`replaySteps_sound`) was proved by
induction on the step list, conditional on a congruence lemma
`evalReplace_sound`.

**That congruence lemma is false.** See the analysis below and the
counterexample.

The operational rewriter (Rewriter.lean) works fine — it applies trace
steps and produces correct results (357/371 on sorting corpus). The
issue is purely in the soundness proof layer.

## The evalReplace_sound counterexample

The theorem:
```lean
theorem evalReplace_sound (f : Nat) (w : World) (env : Env)
    (term lhs rhs : SExpr)
    (h_eq : evalOpt f w env lhs = evalOpt f w env rhs) :
    evalOpt f w env (evalReplace term lhs rhs) = evalOpt f w env term
```

is false because of eval's fuel decrement. When `evalOpt` processes a
compound term at fuel `f+1`, it evaluates subexpressions at fuel `f`.
So `lhs` as a standalone term is evaluated at fuel `f`, but `lhs` as a
subterm of `term` is evaluated at fuel `f - k` (where k ≥ 1 is the
nesting depth). The hypothesis gives the equality at the wrong fuel
level.

**Counterexample:** Let `f(x) = x` and `g(x) = x` be identity
functions. Let `env = {x ↦ 42}`, fuel = 2.

- `lhs = (f x)`, `rhs = x`, `term = (g (f x))`
- Hypothesis (fuel 2): `evalOpt 2 (f x) = some 42 = evalOpt 2 x` ✓
- `evalReplace (g (f x)) (f x) x = (g x)`
- `evalOpt 2 (g x)`: fuel'=1, eval `x` at 1 → 42, result `some 42`
- `evalOpt 2 (g (f x))`: fuel'=1, eval `(f x)` at 1: fuel'=0,
  eval `x` at 0 → `none`. Result: `none`
- `some 42 ≠ none` ∎

This affects the original `eval` too (same structure, different
failure value).

## The correct theorem (from soundness-property.md)

The soundness property doc already identified the right form:

```
∀ env, ∃ N, ∀ f ≥ N, eval f w env result = eval f w env formula
```

The existential fuel is essential: pick a fuel level large enough that
everything converges. A correct congruence lemma:

```lean
theorem evalReplace_sound_corrected
    (w : World) (env : Env) (term lhs rhs : SExpr)
    (h_eq : ∃ N, ∀ f ≥ N, evalOpt f w env lhs = evalOpt f w env rhs) :
    ∃ M, ∀ f ≥ M, evalOpt f w env (evalReplace term lhs rhs)
                  = evalOpt f w env term
```

This requires **fuel monotonicity** as infrastructure.

## Plan

Two independent workstreams, then a dependent third.

### Workstream A: Evaluator properties

Goal: establish the basic metatheory of `eval`/`evalOpt`. These
properties are reusable infrastructure regardless of how the proof
replay is structured.

**A1. Fuel monotonicity for evalOpt**

```lean
theorem evalOpt_fuel_mono (f : Nat) (w : World) (env : Env) (t : SExpr) (v : SExpr) :
    evalOpt f w env t = some v → evalOpt (f + 1) w env t = some v
```

Once eval converges, more fuel doesn't change the result. Proof by
structural induction on `f` and case analysis on `t`, mirroring
evalOpt's definition. Standard but tedious — each case of evalOpt
(atoms, IF, LET, function call, builtins) needs its own lemma or
sub-case.

Estimated: 100-200 lines. This is the single most important
infrastructure lemma.

**A2. evalOpt agrees with eval**

```lean
theorem evalOpt_some_eq_eval (fuel : Nat) (w : World) (env : Env)
    (term : SExpr) (v : SExpr) :
    evalOpt fuel w env term = some v → eval fuel w env term = v
```

Already stubbed in EvalOpt.lean:82 with sorry. Same proof structure
as A1 — induction on fuel, case analysis, use the fact that evalOpt
and eval have identical structure.

Estimated: 50-100 lines.

**A3. Convergence composition**

Corollary of A1. If `evalOpt N t = some v`, then for all `f ≥ N`,
`evalOpt f t = some v`. This is the usable form of monotonicity.

```lean
theorem evalOpt_ge_fuel (f N : Nat) (w : World) (env : Env) (t : SExpr) (v : SExpr) :
    evalOpt N w env t = some v → f ≥ N → evalOpt f w env t = some v
```

Estimated: 10-20 lines (iterated application of A1).

**A4. Audit eval/evalOpt structural agreement**

Currently, evalOpt is claimed to be "structurally identical" to eval.
Verify this holds for all cases, especially:
- LET/LET* binding evaluation
- Builtin dispatch (does evalOpt call the same `callBuiltin`?)
- Arity mismatch handling

This is a review task, not a coding task.

### Workstream B: Corrected congruence

Goal: prove the correct version of the replacement-preserves-eval
theorem.

**B1. Corrected evalReplace_sound**

Using the existential-fuel formulation from above. The proof:
1. From `h_eq`, extract N such that lhs and rhs agree at all fuel ≥ N
2. By induction on `term`, show that for large enough fuel (accounting
   for nesting depth), the replacement preserves evalOpt
3. Each inductive case uses fuel monotonicity (A1/A3) to shift from
   the top-level fuel down to the sub-expression fuel

Key sub-cases:
- **Whole-term match** (term = lhs): immediate from h_eq
- **QUOTE**: evalReplace skips inside QUOTE, so trivial
- **Symbol-headed cons** (function call / IF / LET): recurse into
  arguments. Need to show evalOpt of the argument list is preserved.
  Uses A1 to align fuel levels.
- **Non-symbol-headed cons**: needs well-formedness precondition (all
  real ACL2 terms have symbol heads on function calls)

Depends on: A1, A3
Estimated: 100-150 lines

**B2. Corrected replaySteps_sound**

Restate and re-prove the step-chain theorem with existential fuel.
The current proof structure (induction on step list) should carry over
with minimal changes — the key difference is that each step produces
an existential fuel bound, and we take the max.

```lean
theorem replaySteps_sound (w : World) (env : Env)
    (steps : List RewriteStep) (term result : SExpr) (fuel : Nat)
    (h : replaySteps w env steps term fuel = some result) :
    ∃ M, ∀ f ≥ M, evalOpt f w env result = evalOpt f w env term
```

Depends on: B1
Estimated: 30-50 lines (adaptation of existing proof)

**B3. checkStep at sufficient fuel**

The current `checkStep` evaluates at a single fuel level. With
monotonicity, this is fine: if `checkStep` passes at fuel N, then the
equality holds at all fuel ≥ N.

```lean
theorem checkStep_sufficient (w : World) (env : Env)
    (step : RewriteStep) (N : Nat)
    (h : checkStep w env step N = true) :
    ∀ f ≥ N, evalOpt f w env step.lhs = evalOpt f w env step.rhs
```

Depends on: A1
Estimated: 10-20 lines

### Workstream C: Proof tree replay (future)

This is the larger refactor. NOT part of the immediate plan, but
worth scoping now so that A and B are designed to support it.

The flat trace (a list of RewriteStep) has two independent problems:
1. **4% failure rate** on the sorting corpus (14/371 cases) due to
   information loss when serializing the tree to a sequence
2. **Soundness architecture** — the correct proof is a tree with
   scoped hypothesis contexts, not a fold over a flat list

The soundness-property doc (2026-03-24) describes the right
architecture:
- Per-rule soundness (one theorem per rule type)
- Referential transparency (the congruence from B1)
- Simulation invariant (induction over the proof tree)

What this requires on the ACL2 side:
- Explicit sub-proof boundaries in the trace (BEGIN-SUBPROOF /
  END-SUBPROOF)
- Scope information (which hypotheses are active)
- Assumption bindings (variable substitutions in effect)

What this requires on the Lean side:
- A tree-shaped proof trace type (replacing the flat List RewriteStep)
- A tree-walking replay function (replacing the fold)
- Per-rule soundness theorems
- Context/hypothesis management

The work in A and B directly supports C:
- Fuel monotonicity (A1) is needed for composing fuel bounds across
  tree nodes
- The corrected congruence (B1) is the "referential transparency"
  component
- evalOpt agreement (A2) bridges back to the user-facing eval

## What was done (2026-03-26)

### Workstream A: completed

**A1. Fuel monotonicity** — proved. The key insight: factor `evalOpt`
into `evalOptStep` (non-recursive body) + `evalOpt` (fuel-bounded
recursion). Then `evalOptStep_mono` is a one-shot proof about a
non-recursive function, and `evalOpt_fuel_mono` is a 5-line corollary.

**A2. evalOpt_some_eq_eval** — dropped. We decided to standardize on
`evalOpt` as the sole evaluator. `eval` (plain SExpr return) was
deleted. The bridge lemma is no longer needed.

**A3. evalOpt_ge_fuel** — proved. 3-line proof using `Nat.le` induction.

### Consolidation: eval → evalOpt

`eval` and `Evaluator.eval` were both deleted. `evalOpt` is now the
canonical ACL2 evaluator. Rationale: `evalOpt` distinguishes fuel
exhaustion (`none`) from legitimate nil (`some .nil`), which is
essential for soundness proofs. Having two evaluators created a bridge
obligation with no payoff.

Files removed:
- `ACL2Lean/Eval.lean` — replaced by `EvalOpt.lean`
- `ACL2Lean/Evaluator.lean` — legacy partial evaluator
- `Tests/EvaluatorTest.lean` — tests for old evaluator

`bindArgs` and `callBuiltin` (pure utilities) were moved into
`EvalOpt.lean`. All downstream code (`Rewriter.lean`, `WorldGen.lean`,
`SimpleWorld.lean`, `Main.lean`) updated to use `evalOpt`.

### Current sorry inventory

| File | Sorry | Status |
|------|-------|--------|
| `EvalOpt.lean` | (none) | Clean |
| `RewriterSoundness.lean` | `evalReplace_sound` | Known false; left for proof-tree refactor |
| `SimpleWorld.lean` | `my_len_my_app` | Generated stub |
| `WorldGen.lean` | Template generates sorry | By design |
| `DSL.lean` | Test/example code | Not proof-relevant |

### What's next

Workstream C (proof tree replay) is the remaining architectural work.
Prerequisites are met: fuel monotonicity and fuel sufficiency are
proved. The corrected congruence (existential-fuel `evalReplace_sound`)
should be proved as part of the tree replay design, not independently.
