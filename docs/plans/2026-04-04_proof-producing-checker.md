# Plan: Proof-Producing Checker (Track B)

Created: 2026-04-04
Updated: 2026-06-05 — Rewritten after `my_len_my_app` was proved end-to-end.
The hand proof validated the hard shapes; this records what to REUSE, what
changed since the original plan, and the phased build.

## Goal

A proof-producing checker that walks the already-parsed proof tree and emits
a kernel-checked Lean `Expr` for each ACL2 theorem — the automated version of
the `my_len_my_app` hand proof in `ACL2Lean/Imported/SimpleWorld.lean`.

```lean
theorem my_len_my_app (env : Env) :
    ∃ N, ∀ f ≥ N, evalOpt f world env formula = some SExpr.t := by
  acl2_replay "acl2_samples/simple.proof-log"
```

## DO NOT REINVENT — reuse the existing pipeline

Parsing and tree reconstruction are DONE. The producer consumes the existing
structures; it does not re-parse.

- **Parse → tree:** `ProofLog.parse` (ProofLog.lean) → `buildAllTheoremProofs`
  (ProofTree.lean) yields `TheoremProof` with `cases : List CaseProof`,
  `induction : Option InductionStep` (the `:INDUCTION :SCHEME` already parsed),
  and per-literal `ProofNode` trees.
- **Context + builders (ProofChecker.lean):** `CheckerContext`,
  `buildWorldFromLog`, `buildFormulaMap`, `buildTypePrescriptionMap`.
- **Matching helpers (ProofChecker.lean):** `extractRewriteRule`,
  `patternMatch`, `applySubst`, `macroExpand`, `replaceInTerm`,
  `clauseJustifies`. The per-rune `Expr`-emitters CALL THESE to get the
  substitution / rewrite position, then emit `Expr` instead of `Bool`.
- **CLI wiring (Main.lean `check-proof`):** the parse→build→check sequence to
  mirror for an emit path.

The producer mirrors the checker's traversal, emitting `Expr`:
```
checkTheoremProof → checkCaseProof → checkLiteralProof → checkNode   (Bool)
proveTheoremProof → proveCaseProof → proveLiteralProof → proveNode   (MetaM Expr)
```

## What CHANGED since the original (2026-04-04) plan

1. **Congruence is settled and simpler.** Original plan said "avoid general T1,
   use `pcEq_bind`/`pcEqG_mapM` position-specific". We found better:
   **`evalOpt_arg_congr`** (one-step, existential-`=` form, no `pcEq`). The
   whole `pcEq`/`EvalCtx`/`replaceSubterm` apparatus was deleted. Composition is
   now: find rewrite position → `evalOpt_arg_congr` lift → `fuel_chain_eq` chain.
   Proved and used in the hand proof.

2. **The Bool checker ignores induction; the producer cannot.**
   `checkTheoremProof` is just `cases.all checkCaseProof` — it trusts ACL2's
   clause structure and treats the IH as a clause literal. The PRODUCER must
   generate a real induction (`acl2_induction_consp` from
   `InductionStep.scheme`) and discharge the IH clause literal from it. This is
   new work, not in the original plan.

3. **Totality / type-prescription synthesis is required and is new.** The hand
   proof needed `my_len_total`/`my_app_total` (per recursive function:
   "converges to a value of the type ACL2's `:TYPE-PRESCRIPTION` gives"). The
   producer must synthesize these per function. **Gated on the instrumentation
   gap:** ACL2 does not currently emit `:MEASURE`, so totality proofs pick
   `acl2Count` (fine for structural recursion, wrong in general). See
   `2026-06-05_step-case-and-tp-emission.md`. Emitting `:MEASURE` (and ideally
   the TP proof, hinted by `:ORIGIN TPPROOF/DEFUN`) makes this ACL2-directed.

## Validated building blocks (all proved, in EvalLemmas.lean)

- Atomic steps: `evalOpt_quote/var/number/nil/if_true/if_false/builtin_1/2/defn_1/2`.
- `evalOpt_equal_self`, `eval_equal_t_implies_eq` (T2 — extracts arg equality
  from `EQUAL = T`, used for the IH node).
- `evalOpt_arg_congr` (+ `evalOpt_cong_unary/bin1/bin2`) — one-step congruence.
- `evalOpt_defn1/2_call_congr`, `evalOpt_builtin2_call_congr` — across-env call
  congruence; the IH-node bridge (no general substitution / T15 needed).
- `acl2_induction_consp` (T10) — consp/cdr induction.
- `logic_plus_int / plus_comm / plus_comm2_int / equal_self`, `mkNumber_one`.
- Fuel: `evalOpt_ge_fuel`, `fuel_chain_eq`, `evalOpt_symbol_converges`.

## The hand proof = the target shape

`SimpleWorld.my_len_my_app` (sorry-free, axiom-clean) is exactly what the
producer must generate automatically for `simple.proof-log`. Per rune:
- `definition` → `evalOpt_defn_1/2` + child IF resolution (`evalOpt_if_*`) +
  `cdr-cons`; recursive my-len/my-app handled by the totality lemmas.
- `equal-self` → `evalOpt_equal_self`.
- `if-simplification` → `evalOpt_if_true/false`.
- `rewrite` (unicity-of-0, cdr-cons, commutativity) → the corresponding Logic
  lemma (`logic_plus_zero_left_int`, `logic_cdr_cons`, `logic_plus_comm[2]`),
  lifted by `evalOpt_arg_congr`.
- `rewriting-equivalence` (IH) → instantiate the induction IH at a clean
  `bindArgs` env, extract via T2, bridge via `*_call_congr`.

## Phased build

- **B0 — Composition framework.** Finish `proveLiteralChain`: auto-find the
  rewrite position of each node and lift via `evalOpt_arg_congr` + chain via
  `fuel_chain_eq` (today it hard-fails on subterm rewrites). Wire
  `proveCaseProof` / `proveTheoremProof` mirroring the checker. Reuses
  `replaceInTerm`/position logic. Target: auto-reproduce a non-inductive
  literal proof.
- **B1 — Rune handlers.** `definition`, `if`, `rewrite`, `recognizer`
  (`equal-self` done). Each emits the validated hand-proof shape using the
  reused matching helpers. Mechanical; mildly parallelizable once B0 locks the
  node-prover interface.
- **B2 — Induction + totality.** `InductionStep.scheme` → `acl2_induction_consp`
  application; per-function totality synthesis. Tackle `:MEASURE` emission here.
  Sequential, the main discovery.
- **B3 — `acl2_replay` tactic.** parse → walk → emit, on `my_len_my_app`. Reuses
  `ProofLog.parse`, `buildAllTheoremProofs`, `addTheoremFromChain`.
- **B4 — Corpus sweep.** Run over ~649 theorems, categorize failures, fix
  handlers. **This is the multi-agent workflow** (fan out per theorem, classify,
  adversarially confirm sorry-free).

## Labor model

B0–B3 are sequential (you + me), with B2 the genuine discovery. B4 is the
workflow. B1's handlers could be a small parallel workflow once the B0
interface is locked, but agent labor is fine.

## Prerequisites

All Layer 0–2 + congruence + totality + bridge lemmas in EvalLemmas.lean are
proved (zero sorry). `evalOpt_substVar` (T15) was deleted — unused.
