# R7 — `:use` / functional-instantiation soundness (DESIGN DRAFT)

**Status: DRAFT — NOT RATIFIED. Written en route per the 2026-08-01
amendment (Mike AFK; 2d deferred to last). Nothing is built on this
note; it is the material for the arc's planned MDD checkpoint on
Mike's return. Ratification questions are at the bottom.**

## Targets

- `MSORT-IS-ISORT`, `QSORT-IS-ISORT`, `BSORT-IS-ISORT`
  (sorts-equivalent): `:use (:functional-instance …)` of equisort's
  constrained theorems.
- `LEN2-APP-VIA-USE` (recon-tests/05-hints): plain `:use` of a
  same-book theorem instance — same processor, no functional
  substitution.
- Post-2a: the `CONVERT-PERM-TO-HOW-MANY` consumers that would retire
  `dis_convert_perm` (plain `:use` class, cross-book).
- Pairs with R6 (equisort/encapsulate) — see sequencing.

## Ground truth (primary sources, 2026-08-01)

The fork emits, per `apply-top-hints-clause` step, a `:USE-HINT`
payload (`emit/use-hint`; parsed as `TraceEvent.useHint`,
`ProofLog.lean:137`): `:HYPS` (the instantiated lemma instances),
`:CONSTRAINT-CL` (the true root of the step's recorded rewrite chain),
`:APPLICATION-CLAUSES` (survivors after tautology dropping).

Read off `sorts-equivalent.proof-log:2659` (MSORT-IS-ISORT):

- `:HYPS ((EQUAL (MSORT X) (ISORT X)))` — the functional instance of
  the constrained theorem's conclusion **is exactly the goal clause**.
- `:CONSTRAINT-CL` — the IF-conjunction of the six instantiated
  constraint obligations (`HOW-MANY-ISORT` … `ORDEREDP-MSORT`); the
  recorded chain rewrites it to `'T` using the same-book rules, and
  the replay of that chain is DONE (Class B, task #13): the current
  frontier error at `Replay/Driver/Core.lean:1677` fires *after* the
  chain validates — "the instantiated hyp(s) … await
  functional-instantiation/:use soundness".
- `:APPLICATION-CLAUSES NIL` — `(¬hyp ∨ goal)` is a tautology here
  (hyp = goal) and ACL2 drops it.

BSORT-IS-ISORT is the same shape with the weak (IMPLIES-guarded)
variant and one surviving preprocess child. QSORT-IS-ISORT is the
MSORT twin.

**Composition finding (2e, 2026-08-01):** the driver's `useHint` arm
today fires only in the NO-clausify-records branch
(`Core.lean` `| [] =>`), but BSORT-IS-ISORT's Goal node carries BOTH
the `:USE-HINT` payload AND clausify records (the weak variant's
application clause survives tautology-dropping and clausifies). Its
current failure — `replayPreprocessChain` walking the constraint-chain
steps against the GOAL formula — is exactly this: the clausify-bearing
branch never consults the useHint payload. The R7a composition must
route the step stream by the payload (constraint chain on
`constraint-cl`, then the clausify block on the application side)
regardless of which branch the node's record shape lands in.

What ACL2's `apply-top-hints-clause` does: goal clause `G` with `:use`
instances `L₁…Lₙ` becomes (a) the application clause
`(¬L₁ ∨ … ∨ ¬Lₙ ∨ G)` (dropped when tautologous) and (b) for a
functional instance, the constraint clause(s) — the encapsulate
constraints under the functional substitution. ACL2's own soundness
story: any theorem of the constrained world holds for any functions
satisfying the constraints (a META argument — ACL2 does not re-run
the constrained proof).

## The two gaps

1. **Plain `:use` (no functional substitution) — NO new soundness
   principle.** `EvTrue w env (σ Φ)` for a used theorem `Φ` with
   variable substitution σ is exactly what the existing
   premise/rule-hyp machinery derives: the used theorem's replayed
   statement (same-book channel or 2a's cross-book `depProofs`) +
   the `evalOpt_substTerm_substN` transport
   (`instantiateEvTrueHypAt`). The remaining work is CLAUSE
   COMPOSITION, all existing shapes: prove each `Lᵢ` true, peel the
   `¬Lᵢ` literals off the application clause's replay (the spine
   peel), tautology-dropped application clauses need the same
   recomputed-tautology bridge clausify already has. Deterministic,
   fail-closed (formula cross-check against the stored theorem;
   hard-fail if the named theorem isn't in a channel).

2. **Functional instantiation — the real design item.** The log
   records equisort's local witnesses as plain `:DEFUN`s; the
   encapsulate boundary is not emitted (the 2026-07-20 qsort-frontiers
   survey, confirmed still true). So `Development.toWorld` gives
   `ssortfn1/2` the WITNESS bodies, and the replayed statement of the
   constrained theorem is a fact about the witnesses — it cannot
   justify the msort/qsort instances. The missing content is ACL2's
   meta argument, which a kernel-checked replay must render as an
   actual quantification.

## Design options for functional instantiation

**(a) World-parametric constrained theorems — RECOMMENDED.** The L3
invariant already mandates world-parametricity; the generality plan
names encapsulate as "a statement-builder change". Concretely:

- R6 emission: the fork emits the encapsulate boundary — the
  `:CONSTRAINT` list and which `:DEFUN`s are local witnesses
  (BUG-019-adjacent provenance surface, already on the R6 plan).
- The constrained book's theorems get replayed statements of the form
  `∀ w, ConstraintsHold w → ∀ env, EvTrue w env Φ` where
  `ConstraintsHold` is the conjunction of `EvTrue`-statements of the
  emitted constraints (and the signature facts: the constrained names
  are defined with the right arities). The REPLAY of equisort's
  waterfall must go through over this abstract `w`: ACL2 proved those
  theorems using only the constraint rules, so the recorded trees
  reference only constraint runes + world-independent machinery — a
  tree step that dereferences a witness body would hard-fail, which is
  the correct fail-closed behavior (it would mean ACL2 used
  non-exported facts, impossible for exported theorems).
- The `*-IS-ISORT` application then: instantiate `w :=` the
  sorts-equivalent world, discharge `ConstraintsHold` from the
  RECORDED constraint chain (already replaying today), obtain
  `EvTrue w env (instance)`. One subtlety: the parametric theorem is
  about the formula in the CONSTRAINED names (`SSORTFN1`), while the
  instance is in the concrete names (`MSORT`) — the instantiation
  needs the world to map the constrained names to the concrete
  functions' semantics. Two sub-options:
  - (a1) instantiate at a world that literally binds `SSORTFN1` to
    MSORT's definition (an extended world = the book world + alias
    definitions), then bridge `evalOpt w' (Φ in SSORTFN1-names)` to
    `evalOpt w (Φ[MSORT/SSORTFN1])` by a FUNCTION-SUBSTITUTION
    commutation lemma (evaluation commutes with fn renaming when the
    world binds the names to the same bodies). Ordinary proved lemma
    in EvalLemmas — no trusted-core growth.
  - (a2) state the parametric theorem over an abstract INTERPRETATION
    (fn-name → semantics) rather than a world. More machinery, no
    added faithfulness. Not preferred.
- Faithfulness: this renders ACL2's meta argument as a kernel-checked
  ∀-instantiation; the clause tree stays mirrored (the constraint
  chain is the recorded proof; the parametric replay is the recorded
  equisort tree). No inference, no search: every step keyed to
  emitted structure, hard-fail on any missing piece.

**(b) Schema replay (re-run the constrained trees under the
functional substitution).** Rejected: ACL2 does not re-run the proof,
so a re-run is NOT mirroring ACL2's reasoning; it also needs every
tree step to be stable under renaming (true but a large new
obligation class), and it duplicates work per instance.

**(c) Trust the instance (axiom / assumed hypothesis).** Rejected
outright — violates the trust model.

## Sequencing (proposed)

- **R7a — plain `:use`** (LEN2-APP-VIA-USE, convert-perm consumers):
  independent of R6, all machinery exists; a small increment on the
  existing premise/peel architecture. Can land as its own audited
  sub-arc any time after ratification.
- **R7b — functional instantiation** (the `*-IS-ISORT` capstones):
  gated on R6 emission (constraint list + witness marking) and the
  (a1) commutation lemma. Build order: R6 emission → parametric
  replay of equisort (the hard validation: the recorded trees must
  replay over abstract `w`) → the commutation lemma → the
  apply-top-hints composition.

## Ratification questions for Mike

1. Approve option (a) (world-parametric constrained theorems) with
   sub-option (a1) (alias world + function-substitution commutation
   lemma, proved in EvalLemmas — no trusted-core growth)?
2. Approve the R7a/R7b split — R7a (plain `:use`) building
   immediately on the existing channels, R7b gated on R6?
3. The parametric replay of equisort requires the driver to accept an
   ABSTRACT world parameter for a whole book's replay (today
   `cfg.worldExpr` is always the concrete reflected world). This is a
   driver-surface change with L3 as its warrant — any constraints on
   how far it may reach?
4. `ConstraintsHold` shape: conjunction of `EvTrue` statements of the
   EMITTED constraint terms only (no signature/guard content beyond
   arity)? BSORT's weak variant shows IMPLIES-guarded constraints —
   confirm they ride as-is (the guard is part of the emitted term).
