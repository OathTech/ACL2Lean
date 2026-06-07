# Proof-tree faithfulness audit (three dimensions)

**Date:** 2026-06-07
**Method:** four decorrelated adversarial reviewers (reconstruction↔log, log↔ACL2,
tree→Lean, tree-as-proof), pointed at primary sources (the `.tree` dumps, the raw
`.proof-log`, the `acl2/` instrumentation, live ACL2). Findings cross-checked;
the two highest-stakes spot-checked by hand. Audited `simple` (my-len-my-app, the
target) + `01-multi-theorem`, `02-rev`, `04-multi-case-induction`, `06-measure`.

A faithful **proof object** = (1) faithful to ACL2's reasoning, (2) sufficient to
become a Lean proof, (3) a valid proof of its own claimed theorem.

## Verdict
All three properties largely hold. Bounded fix list below (tracked as tasks
B1, C1, A2, A3, B2/B3).

### (1) Faithful to ACL2 — strong, one real instrumentation bug
- Reconstruction ↔ log: **exact** — no event dropped/duplicated/reordered/added
  (verified by counts across 5 logs); clause-id linking, branch nesting, IH links
  all correct. Prior bugs stay fixed.
- Log ↔ ACL2 (macro-structure): induction term/scheme, per-subgoal runes,
  defun/TP corollaries, recognizer terms, rewriting-equivalence — verified
  faithful against live ACL2.
- **B1 (instrumentation, §D.1-class, confirmed by hand):** `:UNREWRITTEN-TEST` is
  logged at the raw *formal* level while its event's other terms are call-site
  level — the `sublis-var` patch was applied to the rewrite-step but not the
  co-located if-test. `simple.proof-log:175` `:UNREWRITTEN-TEST (ACL2-NUMBERP X)`
  vs the real `(acl2-numberp (my-len y))` (the `DEFINITION FIX` step has
  `:SUBST ((X MY-LEN Y))`). Fix at `acl2/rewrite.lisp:17522` & `:17385`. Latent
  (reconstruction doesn't consume the field yet) but the log is unfaithful.
- **B2/B3 (meaning hazards):** a step's `:RUNES` is the *cumulative* ttree
  rune-set, not that step's rule (the rule is `:RUNE`); a with-lemma step's
  `:RHS` is the *fully-rewritten* result (folds in nested children), not one rule
  application. Internally consistent; must be interpreted correctly downstream.

### (2) Sufficient to become a Lean proof — structurally yes; one decisive gap
- **C1 (decisive, producer, confirmed by hand):** with-lemma rewrites carry no
  instantiating `:SUBST` (only the 6 definition steps do), so the replay cannot
  faithfully instantiate imported lemmas (commutativity-of-+, unicity-of-0,
  cdr-cons, …) — only re-derive (search, forbidden) or compute-and-equate
  (shortcut, forbidden). fertilize/generalize/eliminate-destructors substitutions
  also dropped. Fix: emit these from ACL2.
- **C2 (reconstruction):** the induction descriptor (scheme→Lean principle, the
  IH's substitution form / step-env relation) isn't materialized; the replay
  would have to infer it.
- Semantic coverage of every primitive the target uses confirmed (post
  `callBuiltin→Option`). Stage-7 `ProofProducer` is unbuilt/orphaned and the
  congruence linchpin + arithmetic lemmas are `sorry` — expected; bounds
  replay-completeness. (Not reconstruction bugs.)

### (3) A valid proof of its own theorem — yes
- **No invalid proofs.** `my-len-my-app` is a sound induction proof of exactly
  its stated theorem (no weakening, IH on a smaller term, exhaustive split, no
  circularity, leaves close); `02-rev`'s 5-theorem chain has acyclic lemma deps;
  others valid where they emit steps.
- **A2/D1 (gap):** type-discharged subgoals (`app-nil *1/1`, `rev-rev *1/1`,
  `true-listp-rev *1.1/1`) are stamped `proved` with no emitted reasoning — real
  tautologies, but nothing to replay; and the type-set `:JUSTIFICATION` runes
  that *are* logged get discarded in reconstruction (`ProofTree.lean:106`).
- **A3 (cosmetic):** renderer drops clause-level `step` children (data present,
  unprinted). `04` is misnamed (its only multi-case induction is a *termination*
  proof, not a theorem).

## Fix list (priority order → tasks)
1. **B1** — `sublis-var` the `:unrewritten-test` (instrumentation; submodule+push).
2. **C1** — emit `:SUBST` on with-lemma rewrites + processor substitutions
   (instrumentation; the replay enabler).
3. **A2** — consume type-set `:JUSTIFICATION` in reconstruction (Lean-side).
4. **A3** — render clause-level `step` children (Lean-side, cosmetic).
5. **B2/B3** — document `:RUNES`/`:RHS` semantics for the replay.

## Could-not-verify (coverage gaps, not bugs)
Forcing-round `[k]` and `Dk` disjunctive clause-ids (no sample exercises them);
the `caseSplit` event path; whether the 923 `if-finish/if-test` occurrences each
leak (mechanism identical to the confirmed one); larger corpus logs.
