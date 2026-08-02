# DP-leaf premise classes (dp-premises sub-arc, 2c)

Written at fold-back (2026-08-01), after the sub-arc's two-reviewer
audit (soundness/fidelity + mechanism, both fold-back-with-fixes, all
fixes applied). Ratification of the class list rides the queued 2b
carve-out item in TODO.md (the "EXTENSION (dp-premises …)" wording).

## What a premise is

`replayDischargeNode` (Totality.lean) composes a verdict-only DP leaf
into the conditional replay: it states the leaf's obligation as a
`dpFactStmt` — the emitted clause lifted over abstract `dpv` values —
and proves it with `proveDpFact` (the carve-out's kernel-checked
decision procedure). A PREMISE is an extra hypothesis of that
statement: a pair `(term, fact)` where `term` is an ACL2-term whose
`dpValExpr` lift becomes a hypothesis of the ∀-statement, and `fact`
is a PROOF of that hypothesis at the leaf's pinned concrete values.
Because every premise fact is applied at the same witnessing
assignment as the opaques and TP corollaries, a contradictory or
vacuous premise set is impossible by construction (audit finding 1),
and a wrong fact is a kernel type error, not a silent success (the
tamper probe died at `Meta.check`).

Premises let the leaf prover see the VALUE-DEFINING LINKS that the DP
abstraction drops (the ORDERED-PERMS gap: `(PERM A A)`'s reflexive
tie, the `TRUE-LISTP-RM` rule content) — content ACL2's own verdict
procedures (tau, type-set, forward-chaining) had in scope when they
issued the verdict.

## The classes (all premise facts proved, none assumed)

1. **LINEAR rules (2b).** Emitted gz `:LINEAR` specs; trigger = the
   emitted max-term one-way-matched against the obligation's OPAQUES
   (deliberately narrower than class 2's targets: pot labels are the
   linear-arithmetic atoms, which the lift represents exactly as
   opaques — audit F2). Premise `(IF hyp (EQUAL l r) 'T)`, fact via
   `linear_premise_fact`. Frontier-errors on non-qualifying shapes
   (curated emission — each spec is expected to instantiate).
2. **RULE content (2c).** Stored `:REWRITE` rules, boolean-strengthened
   shape only (equiv `EQUAL`, rhs `'T`, exactly one hyp), GATED on
   ACL2's tau Signature Form 1 (`tauSigForm1`: conclusion about
   `(fn v1 … vn)` with distinct variable args, recognizer hypothesis
   on one of them) — so the pass can only offer content tau itself
   consumes. Trigger = the stored LHS one-way-matched against ALL
   symbol-headed application subterms of the clause (`ruleTargets`,
   `collectAppSubterms`): a lift-primitive-headed LHS
   (`(TRUE-LISTP (RM E A))`) never appears as an opaque. Premise
   `(IF hyp (EQUAL lhs 'T) 'T)`, fact via `rule_premise_fact`.
   SCOPE CHANGE AFTER THIS CLASS'S AUDIT (pre-merge seams audit F2,
   2026-08-02): the pass's input `ctx.ruleHyps` became O(corpus) when
   the cross-rules channel landed — cross-book rules now reach the
   trigger match. The tau shape gate still applies; the include-book
   provenance gate (queued) is the scope restoration.
   SILENTLY skips non-qualifying rules (policy note at the site: this
   pass scans every stored rule in scope; skipping is the fail-closed
   direction).
3. **EQUIVREFL (2c).** The reflexivity conjunct of an
   equivalence-shaped theorem (`(AND (BOOLEANP (R x y)) (R x x) …)`),
   applied at SYNTACTICALLY reflexive application subterms `(R u u)`.
   Mirrors ACL2's `assoc-equiv+` / `assume-true-false`
   `(equal arg1 arg2)` case verbatim, rune-free exactly as ACL2
   records it. Premise `(NOT (NOT (R u u)))` — double negation because
   the `EvTrue` instance gives only `≠ nil`; the obligation's TP
   booleanp cell closes to `'T` inside the fact (ACL2's tau
   composition). Fact via `equivrefl_premise_fact` on
   `instantiateEvTrueHypAt`'s instance.
4. **Trusted-core primitive recursion in the leaf tactic (2c).**
   `Logic.trueListp_cdr_of_consp` in `dpLeafTactic`'s simp sets —
   the `TRUE-LISTP`/`CDR` link (`type-set-cdr`'s rune-free
   `*ts-proper-cons* → *ts-true-list*` propagation). Not a premise —
   a primitive's own defining equation, the `endp`/`len` bridge
   precedent. ORIENTATION IS LOAD-BEARING: the rewrite runs
   `trueListp (cdr x) → trueListp x` (shrinking); the reverse is a
   growing rewrite that diverges under repeated `consp` evidence
   (mechanism audit F1, demonstrated).

## Shared machinery

All σ-instantiation rides `mkSubstNBridge` (NodeCore.lean) — the
single substN scaffold (pins σ terms as part of the contract, fixing
the linear copy's latent unpinned-σ-term hard-fail, audit F3);
`instantiateEvTrueHypAt` is its premise-free `EvTrue` slice. The
premise passes run inside a BOUNDED 3-round fixpoint (an instantiated
premise can introduce the opaque a later match needs); dedup is on
the premise term over the whole accumulated list, so cross-pass
syntactic collisions collapse.

## Known boundaries / open items

- **Leaf-class gating (soundness audit F1, OPEN for ratification):**
  the passes gate on rule/term SHAPE, not on the leaf's origin (tau
  vs `fake-rune-for-type-set`) — the origin is not plumbed into
  `replayDischargeNode`. Today's corpus fires class 2 only on tau
  leaves (verified against the emitted runes), held by the tau-shape
  gate rather than by leaf provenance.
- **Equivalence provenance (soundness audit F2):** `:rule-classes
  :equivalence` is not emitted; class 3 shape-parses the formula.
  Closing this is fork instrumentation, queued.
- **Premise-construction failure downgrades the leaf (audit F6,
  LOW):** a `throwFrontier` while BUILDING a premise aborts
  `proveAndFinish` and falls back to the premise-free
  `ASSUMED:dp-fact` offer even if the leaf was provable premise-free
  with no premises attempted. Not observed; queued follow-up (a
  per-premise guard must not silently drop premises — needs design).
- **Composed row vs standalone probe:** the sweep's `cond[…]` column
  is the composed replay (premise machinery in scope); the
  `[DISCHARGE:]` column is the standalone probe (none). Legend in
  Tests/DriverCoverage.lean.
