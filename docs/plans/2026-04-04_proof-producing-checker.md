# Plan: Proof-Producing Checker (Track B)

Created: 2026-04-04
Rewritten: 2026-06-05 — after a real-data run showed the producer discharges
**0 of 10** nodes of the real reconstructed proof tree. The previous version of
this plan was premised on the hand proof being a "validated blueprint" and the
handlers "working"; both were false confidence from synthetic tests. That
content has been ripped out. See `docs/audits/2026-06-05_producer-triage.md`.

## Goal (unchanged)

A proof-producing checker that walks the **reconstructed proof tree**
(`ProofLog.parse → buildAllTheoremProofs`, NOT the flat log, NOT synthetic
nodes — see CLAUDE.md) and emits a kernel-checked Lean `Expr` for each ACL2
theorem.

```lean
theorem my_len_my_app (env : Env) :
    ∃ N, ∀ f ≥ N, evalOpt f world env formula = some SExpr.t := by
  acl2_replay "acl2_samples/simple.proof-log"
```

## Current honest status (2026-06-05)

- **Source of truth:** `Tests/ProofProducerRealLog.lean` runs the producer over
  the real reconstructed tree and reports per-node OK / frontier. It currently
  reports **0/10 top-level nodes discharged.** A handler is "working" only when
  this harness says OK — not when a hand-built unit test passes.
- The hand proof (`ACL2Lean/Imported/SimpleWorld.lean`) was deleted except for
  the two standalone totality lemmas (`my_len_total`, `my_app_total`). Its base
  case faithfully mirrored the tree, but its **step case did not** (it computed
  values to integers and used native `Int` arithmetic instead of replaying the
  tree's `commutativity-of-+` / `rewriting-equivalence` / recursive-definition
  nodes) — so it was misleading as a blueprint and is gone.
- The producer handlers are tagged BROKEN-ON-REAL-DATA in `ProofProducer.lean`.
  They encode reusable mechanisms but none discharge a real node yet.

## What the real tree actually needs (the fix sequence)

Measured from `lake exe acl2lean dump-proof-tree acl2_samples/simple.proof-log`
and the 0/10 harness run. Rough dependency order:

1. **parse → world/symbol reflection seam.** The producer's simp side-conditions
   (`proveWorldLookupNone`, `proveWorldDefnLookup`, `bindArgs` lookups) don't
   discharge for the real parsed world+symbols (e.g. the `sym`/package form, and
   opaque `.choose` env values). Pin down how the reconstructed tree's symbols
   and the world Expr must line up so lookups close.
2. **Per-case context driver** (`proveCaseProof`/`proveTheoremProof`): build the
   induction from `InductionStep.scheme`, and per case derive `ctx.vars`
   (variable bindings) and `ctx.facts` (clause-derived recognizer facts like
   `consp x = nil`). Without this, even base-case `definition`/`recognizer`
   nodes hard-fail ("no justification for x → NIL").
3. **Converger coverage + existential convergence in handlers.** Real node args
   are pervasively builtin calls (`car`/`cdr`/`fix`), 2-arg calls
   (`my-app (cdr x) y`), and `binary-+`. Handlers must converge these
   (existential fuel), not the fixed-fuel-only base cases they handle now.
4. **2-arg totality** (`synthTotality2`, for `my-app`), and integer-typed
   convergence for arithmetic — the type fact comes from the emitted
   `:TYPE-PRESCRIPTION` corollary (see the instrumentation lever below), not
   from Lean inference.
5. **Arithmetic rewrite rules** (`unicity-of-0`, `commutativity-of-+`,
   `commutativity-2-of-+`) over integer-typed args.
6. **`rewriting-equivalence`** — the induction-hypothesis application.
7. **`acl2_replay` tactic** wiring the whole pipeline; then the corpus sweep.

## Reuse (still valid)

The parser + tree reconstruction are done and trusted as input: `ProofLog.parse`,
`buildAllTheoremProofs`, and the `CheckerContext`/`buildWorldFromLog`/
`buildFormulaMap`/`buildTypePrescriptionMap` helpers in ProofChecker.lean. The
EvalLemmas library, reflection layer, fuel infra, and `synthTotality1` (1-arg
structural totality) are sound and reusable. Caveat: "reusable" ≠ "sufficient" —
the 0/10 run shows real gaps even in the side-condition provers (#1).

## Generality contract (anti-over-fitting — still binding)

`my-len-my-app` is the FIRST test case, not the spec. Handlers are driven by the
parsed tree + a general lemma library + prior theorems. NEVER pattern-match on
specific function/variable names. Where generality isn't built, **hard-fail**
(the "no papering over" rule) — that marks the frontier, and the real-tree
harness + a corpus sweep test exactly those boundaries.

## Instrumentation lever

We can always emit more from ACL2 rather than infer in Lean. The type facts the
arithmetic rules need are already emitted (`:TYPE-PRESCRIPTION` corollary) and
parsed; for functions whose TP proof `synthTotality*` can't reconstruct
(non-structural recursion), emit the TP proof (`:MEASURE` / `:ORIGIN TPPROOF`).

## Next

Detailed design of steps 1–2 to be done WITH supervision (the synthetic-node
miss came from unsupervised building against fake data). Drive every step off
`Tests/ProofProducerRealLog.lean`.
