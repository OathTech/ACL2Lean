# Design: Composable Proof Trace Logging

Created: 2026-03-22
Updated: 2026-03-22 — simplified from reconciliation to depth counter + accurate logging

## Problem

ACL2's structured proof trace logs REWRITE-STEP events during recursive
rewriting. A Lean rewriter replays these by applying `replaceFirst`
(find LHS as subterm, replace with RHS) sequentially to the literal.
This works for 93% of cases (344/371) but fails for 27 cases.

All failures trace to one root cause: **the logged steps reference terms
from ACL2's internal rewriting state, which can differ from what the Lean
rewriter sees after applying earlier steps.** Specifically:

1. **Context substitution**: When ACL2 knows `x1 = a` from a branch
   assumption, it rewrites using the substituted form internally. The
   logged step has LHS `(f a ...)` but the Lean rewriter's literal
   still has `(f x1 ...)`.

2. **Inner step leakage**: Some steps logged at depth 0 reference
   subterms created inside a definition expansion, not in the literal.

3. **Summary steps**: `clause-context-resolution` jumps from the
   original literal to the final result, but `replaceFirst` can't
   apply it after earlier steps changed the literal.

## Design Principle

**The trace must be self-contained and composable:**

```
steps.foldl (fun t s => replaceFirst t s.lhs s.rhs) original_literal == final_result
```

Every step's LHS must be a subterm of the literal at the point of
application. Every step must have a single-rune justification for the
soundness proof. No special cases in the Lean rewriter.

## Solution: Depth Counter + Accurate Logging

Two complementary mechanisms:

### Part 1: Depth Counter

ACL2's rewriter is recursive. When expanding a definition, it rewrites
the body, which may trigger further expansions. The depth counter
suppresses REWRITE-STEP events from inside these expansions — their
effects are folded into the outer step's RHS.

- Increment for bkptr ∈ {rhs, body, lambda-body, expansion}
- Only log REWRITE-STEP when depth = 0 (literal level)
- Structural markers (BEGIN-LITERAL, etc.) always log

This is already implemented. The remaining work: audit ALL logging
points to ensure the depth guard is present everywhere.

### Part 2: Accurate Logging

The logged steps must reference terms as they appear in the evolving
literal, not ACL2's internal state. Two specific fixes:

**2a: Context substitutions from branch assumptions.** When a case
split produces an equivalence (e.g., `x1 = a`), the clause is
substituted via `remove-trivial-equivalences`. This IS logged as
`BRANCH-SUBSTITUTION`. The Lean rewriter applies these via `replaceAll`
before per-literal rewrite steps. Verify all substitution paths log.

**2b: Remove clause-context-resolution.** This summary step uses the
original literal as LHS, which breaks composability. If individual
steps compose correctly, it's redundant. If they don't, it masks bugs.

### What Gets Logged (after both parts)

Per literal, the trace contains:
- **BRANCH-SUBSTITUTION** — context variable substitutions (applied first)
- **REWRITE-STEP** — literal-level rewrites (applied in order via replaceFirst)
- **REWRITTEN-LITERAL** — the expected final result (serves as checksum)

### Lean Rewriter Processing

```
1. Apply BRANCH-SUBSTITUTION events via replaceAll (context setup)
2. Apply REWRITE-STEP events via replaceFirst (sequential rewriting)
3. Verify result matches REWRITTEN-LITERAL (checksum)
```

No special cases, no reconciliation, no heuristics.

### Soundness Justifications

| Step type | Rune | Lean verification |
|-----------|------|-------------------|
| REWRITE-STEP (:DEFINITION name) | Definition unfolding | Verify body matches World; eval agrees |
| REWRITE-STEP (:REWRITE name) | Proved equality | Verify theorem is in World or axiom library |
| REWRITE-STEP (:EXECUTABLE-COUNTERPART name) | Ground evaluation | Verify by running eval |
| CONTEXT-SUBST | Branch equivalence | Verify literal is in clause; equality holds |
| EVAL-STEP | Ground evaluation / type-alist | Verify by eval or clause context |

### Why This Design Is Right

1. **The Lean rewriter stays trivial** — a fold of replaceFirst/replaceAll.
   No heuristics, no special cases, no ordering tricks.

2. **Every step has one justification** — the soundness proof handles
   each step type independently.

3. **The ACL2 side owns the complexity** — reconciliation runs in raw
   Lisp where we have full access to the type-alist and clause context.
   ACL2 already computed the right answer; reconciliation just makes
   the trace faithful to how the Lean rewriter will process it.

4. **Composability is guaranteed** — the reconciliation simulates
   replaceFirst, so the output is composable by construction.

5. **No coupling** — the reconciliation uses the same replaceFirst
   semantics as Lean, but the Lean side doesn't need to know about
   reconciliation. It just sees a clean, composable trace.

## Migration Path

1. Implement `subst-first` and `find-variable-mapping` in rewrite.lisp
2. Implement `reconcile-steps` and wire into simplify.lisp
3. Remove depth counter, clause-context-resolution, and no-op step guards
4. Recapture all proof logs
5. Update Lean parser for new event types
6. Verify 371/371 (100%) on sorting corpus

## Files to Modify

- `acl2/rewrite.lisp` — add utility functions, remove depth counter
- `acl2/simplify.lisp` — add reconciliation call, remove clause-context-resolution
- `acl2/axioms.lisp` — register new functions for raw code
- `ACL2Lean/ProofLog.lean` — add new TraceEvent variants + parser
- `ACL2Lean/Rewriter.lean` — add handling for new step types

## Risk: subst-first Fidelity

The ACL2 `subst-first` must EXACTLY match Lean's `replaceFirst`.
Both traverse cons trees depth-first left-to-right. Since SExpr and
Lisp cons cells have the same structure, this is straightforward. But
it must be tested carefully — any divergence breaks composability.

## Risk: Reconciliation Complexity

The reconciliation algorithm is O(n * m) where n = number of steps
and m = size of the literal. For the sorting corpus, both are small
(< 20 steps, < 100 nodes). For larger proofs, this could be a concern.
Monitor and optimize if needed.
