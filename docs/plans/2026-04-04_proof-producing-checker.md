# Plan: Proof-Producing Checker

Created: 2026-04-04

## Goal

Convert the Bool checker (ProofChecker.lean) into a proof-producing
checker that emits Lean proof terms (Expr) for each ACL2 theorem.

## Architecture

The Bool checker dispatches on proof tree node types:
```
checkNode : CheckerContext → ProofNode → Bool
```

The proof-producing checker has the same dispatch:
```
proveNode : CheckerContext → ProofNode → MetaM Expr
```

Each `proveNode` call returns an `Expr` that proves the node's
claim: `eval(lhs) pcEq eval(rhs)` or `eval(lhs) = eval(rhs)`.

## Starting point: equal-self

The simplest rule. `checkEqualSelf` returns `true` if `lhs` is
`(EQUAL x x)` and `rhs` is `'T`. The proof-producing version
constructs an `Expr` that proves:
```
evalOpt f w env (EQUAL x x) = some SExpr.t
```
using `evalOpt_equal_self` from EvalLemmas.lean.

## The tactic: acl2_replay

```lean
syntax "acl2_replay" str : tactic
```

At elaboration time:
1. Read the proof log file
2. Parse the proof tree
3. For each theorem: construct the proof term by walking the tree
4. Emit the proof term

## Implementation order

1. **equal-self rule** — simplest, forces solving infrastructure
2. **definition expansion** — most common node type (T4+T5)
3. **rewrite rule** — uses formula lookup + pattern match (T6+T8)
4. **clause assumption / anonymous rule** — type-set verification
5. **IH application** — rewriting-equivalence
6. **Chain composition** — T1 (or position-specific proofs) + T16
7. **Induction** — T10 generates the case split

## Key design decisions

**Avoid general T1.** The checker knows the exact context at each
step. Instead of `replaceSubterm` + general congruence, construct
position-specific proofs inline using `pcEq_bind` / `pcEqG_mapM`
at each call layer.

**Fuel management.** Each node proof establishes `eval f ... = ...`
for a specific concrete `f`. The checker computes the minimum fuel
needed and uses `evalOpt_ge_fuel` to adjust.

**HashMap lookups.** The checker has the world at elaboration time.
It can verify lookups computationally and emit `rfl`-based or
`decide`-based proofs.

## Prerequisites

All Layer 0-2 lemmas from EvalLemmas.lean (mostly done).
The 2 arithmetic sorrys are NOT blocking — they affect specific
rewrite rules (unicity-of-0) which can be handled later.
