# Decrease discharge via the emitted-obligation prover (#37 route) — plan

STATUS: DRAFT, awaiting MDD ratification. Branch `mdd/37-decrease-prover`.
Source: induction-generality audit finding 2 (TOP of the follow-up queue);
design I4 of `docs/plans/2026-06-10_generality-design.md`; the ratified
admission-decrease carve-out extension (CLAUDE.md, MDD 2026-06-11).

## The defect (two per-shape sites, one design violation)

1. `Waterfall/Induction.lean` ~242–287: the IH decrease is discharged by
   pattern-matching the IH substitution — J2 (cdr/car of a single measured
   var) and J4 (two-var sum swap) — and picking a Count lemma directly.
   It NEVER consults the scheme fn's emitted `:TERMINATION-CLAUSES`. This
   is the design's explicitly-REJECTED per-shape-tier approach, and it is
   a fidelity gap: the decrease ACL2 actually certified (the emitted
   clause, with its ruling literals) is not what we verify.
2. `Totality.lean` `totDischargeDecrease`: structurally CORRECT — (1) find
   the emitted clause for the call site, (2) verify every ruling literal
   against in-scope branch facts, (3) discharge the `<` — but step 3 is
   hardwired to cdr/car of a single measured formal, and the clause lookup
   assumes the measure is `(acl2-count m)` of one var.

## The real artifact (msort.proof-log, drives the design)

- EVENS (measured L): clause `((ENDP L) (O< (ACL2-COUNT (CDR (CDR L))) (ACL2-COUNT L)))`
  — ONE ruler; the Lean discharge must get `cddr < ·` from `¬endp L` alone
  (unconditional `cdr` ≤-step composed with one strict step).
- MSORT (measured X): `((ENDP X) (ENDP (CDR X)) (O< (ACL2-COUNT (EVENS X)) (ACL2-COUNT X)))`
  — a USER measure-arg; `Count.acl2Count_evens_lt`'s hypotheses are exactly
  these two rulers.
- MERGE2 (measure `(binary-+ (acl2-count x) (acl2-count y))`, measured
  (Y X)): the sum case (sum-right decrease).

Blocked frontier rows (golden lines 81–87): ACL2-COUNT-EVENS-{STRONG,WEAK},
ORDEREDP-MSORT, TRUE-LISTP-MSORT, HOW-MANY-MERGE2, HOW-MANY-EVENS-AND-ODDS,
HOW-MANY-MSORT.

## Design

**D1 — one shared prover.** Generalize `totDischargeDecrease` into
`dischargeDecrease` (stays in `Totality.lean`, upstream of both callers):
inputs = the `Justification` (emitted clauses), the measure term + measured
subset, the per-formal substitution (call args / IH alist), in-scope facts
`(SExpr × Bool × Expr)`. Steps (1) and (2) keep the existing logic but the
`O<` literal is built from the REAL measure term with the substitution
applied — not assumed `(acl2-count var)`. A clause with no match, or a
ruling literal with no covering fact, HARD-FAILS (never prove a decrease
ACL2 did not emit — carve-out scope unchanged).

**D2 — the Count walk (step 3), replacing both per-shape sites.**
Discharge `count(σ(μ)) < count(μ)` compositionally from the literal:
- destructor chains (`(cdr (cdr x))`, `(car x)`, …): unconditional ≤ steps
  (`acl2Count_cdr_le` / `acl2Count_car_le` — to ADD to Count.lean) chained
  with ONE strict step from a consp fact (in-scope directly, or via the
  existing endp/atom/or-form inversion, which moves from Induction.lean
  into the prover);
- user measure fns: an ADDITIVE registry `(head symbol) ↦ (Count lemma,
  required ruler facts)` — rows for EVENS (`acl2Count_evens_lt`) and ODDS
  (`acl2Count_odds_lt`) now; new fns = new registry rows + a proved Count
  lemma, no new match arms;
- sum measures (`(binary-+ (acl2-count x) (acl2-count y))`): componentwise
  ≤ with at least one strict component (existing `acl2Count_cdr_sum_lt_*`
  lemmas; the J4 swap lemma becomes derivable or a registry row).

**D3 — callers.** `replayInduction` lines ~242–287 replaced by a call to
`dischargeDecrease` (measure/measured-subset from the scheme fn's
justification, substitution from the IH alist, facts from the case's
branch facts); `totWalk`'s call site moves to the same prover. The old
J2/J4 fragment code is DELETED — no dual routes.

## Known hard part (flagged honestly)

For user-fn substitutions (`X := (EVENS X)`), the decrease obligation
relates `acl2Count` of the VALUE of `(EVENS X)` under the env, while
`acl2Count_evens_lt` speaks about the Lean model `Count.evens`. The bridge
`value-of (EVENS X) = Count.evens (value-of X)` (an evalOpt↔model
simulation fact) may or may not fall out of the existing pinned-value
machinery (`ctxValProof` / conv lemmas). This is the first thing to probe
against the real msort tree — if a simulation lemma per registered fn is
needed, it joins the registry row (lemma + sim fact), still additive.
Scope guard: if the bridge turns out to need NEW instrumentation (emitted
value facts), pause and re-scope with MDD rather than inferring in Lean.

## What changes in the golden (NOT zero-change — unlike WP2)

The 7 rows' frontier text changes; schemes that replay past the decrease
either REPLAY or surface the NEXT frontier behind it (honest outcome
either way). Gates: `just ci` green; golden diff REVIEWED (improvements /
frontier movement only — no regressions on the other 72 rows); diff-test
389/0 unchanged (no interpreter change).

## Stages (each gate-checked; commits at ratified milestones)

- S0: probe the msort tree for the EVENS bridge — DONE 2026-07-18:
  (a) EVENS/ODDS are WORLD DEFUNS in the corpus (`:DEFUN EVENS` in the
  msort log); `Logic.evens`/`odds` are UNWIRED models used only by the
  Count lemmas. The bridge therefore needs per-fn WORLD-PARAMETRIC
  simulation lemmas (`value-of (EVENS X) = Logic.evens (value-of X)`,
  proved by fuel induction from the defun body) — registry row = (head,
  Count lemma, sim lemma). NO new ACL2 instrumentation needed.
  (b) 4 of the 7 rows are destructor-only, bridge-free: the cddr rows
  (ACL2-COUNT-EVENS-{STRONG,WEAK}, HOW-MANY-EVENS-AND-ODDS) and MERGE2's
  sum-right — S2/S3(+S5) land them without sim lemmas; only the 3 msort
  rows ((EVENS X) substitutions) wait on S4.
  (c) The real induction node (ACL2-COUNT-EVENS-STRONG) confirms the
  clause-lookup design: justification formals (L) must be RENAMED to the
  induction's actual terms (X) before matching; the step-case ruling fact
  `(NOT (ENDP X))` is exactly the emitted clause's ruler; the IH's
  substituted measure is exactly the O< literal's lhs.
- S1 — DONE: `acl2Count_cdr_le`/`car_le` proved (no sorry).
- S2 — DONE (sum handling folded in so deleting J4 can't regress):
  `dischargeDecrease` + `chainLe`/`chainLt` in Totality.lean; BOTH former
  callers rerouted (`totWalk` and `proveTp`'s return-path self-call —
  a second call site the plan had missed). Sum measures: componentwise
  (one strict) + the swap pattern.
  DESIGN REFINEMENT (found by the sweep, HOW-MANY-ISORT): a MERGED
  induction case (two call sites, same substitution, complementary
  `(eql …)` polarities) establishes NEITHER polarity, so no single clause
  fully covers. Faithful rule implemented: accept when some matching
  clause's rulers are all covered, OR when exactly two clauses match with
  sole uncovered rulers `T` / `(NOT T)` — ACL2's own merged-case
  justification (either branch concludes the same `O<`).
- S3 — DONE: `replayInduction` rerouted through the prover (scheme
  fn/actuals from `ind.term`, justification from `cfg.justs`, σ = the IH
  alist, facts = the case's TestFacts, consp via the existing inversion);
  J2/J4 fragment code DELETED.
  Sweep outcome (golden updated, reviewed): EVENLEN-BOOLEANP is now
  REPLAYED UNCONDITIONALLY (24 unconditional, was 23 — the general walk
  discharges evenlen's cddr admission, the predicted flip); the 7 blocked
  rows all moved past the decrease — cddr rows to next frontiers
  (NUMERATOR convergence ×2, DEFAULT-CDR rule hyp), HOW-MANY-MERGE2 to an
  IH-solidify frontier (its sum-right decrease DISCHARGES), the 3
  `(EVENS X)` rows to the S4 registry frontier. No other row changed.
  Gates: ci green, diff-test 389/0, zero warnings.
- S4 — DONE (Route A, MDD-ratified in-session: prove the Lean models
  correct rather than grow the trusted core): `Replay/CountSim.lean` —
  `evens_body_conv` (strong induction on the argument's count, pure
  intro-direction over the conv kit; `conv_unique`/`conv_var`/`conv_quote`/
  `conv_if_false` added as kit completions), `evens_sim`/`odds_sim`
  (axioms: propext, Classical.choice, Quot.sound — no sorryAx).
  `DecreaseKit` structure (cfg/envE/facts/valOf/convOf/conspTrueOf/
  endpFalseOf) replaces the loose callbacks; registry branch in `chainLt`
  for EVENS/ODDS: world shape byte-checked against the proved constants,
  `defGetFact`+`proveNoShadow` kernel-decide the lemma's world hypotheses,
  sim equality casts the model-level `acl2Count_evens/odds_lt`.
  Sweep outcome (golden updated, reviewed — ONLY the 3 msort rows moved):
  all 3 `(EVENS X)` decreases now discharge (incl. the ODDS sim on the
  second IH); the rows surface NEW frontier classes past the induction
  (clause-level `definition:ODDS` step items ×2; preprocess `:PATH`
  ambiguity for a twice-occurring lhs). No theorem newly replays in msort
  — honest outcome: #37's decrease wall is fully gone, the next walls are
  precise recipe/instrumentation gaps.
- S5 — SUBSUMED INTO S2 (componentwise sum + swap landed there; MERGE2's
  decrease discharges — its remaining failure is an unrelated IH-solidify
  frontier).

## Follow-up frontier classes exposed (out of #37 scope, for the backlog)

MDD-ratified sequencing (2026-07-18) for the next arc, AFTER this branch
completes the merge protocol (pre-merge audit required): **4 → 5 → 3**
(clause-level definition step items, then preprocess `:PATH` emission,
then the IH-solidify instantiation — the path that flips msort rows to
REPLAYED). 1 (NUMERATOR, trusted-core growth via the H3 pin-first
process) and 2 (folds into the queued J6b positive type-set marker)
remain unsequenced backlog.
1. `proveConv`: unary NUMERATOR not in the builtin registry
   (ACL2-COUNT-EVENS-{STRONG,WEAK}).
2. `DEFAULT-CDR` marker-relieved hyp needs a falsity fact
   (HOW-MANY-EVENS-AND-ODDS).
3. IH-solidify: instantiated-vs-source equation mismatch on `(CAR Y)` vs
   `E` (HOW-MANY-MERGE2).
4. Clause-level `definition` step items in the spine
   ({ORDEREDP,TRUE-LISTP}-MSORT).
5. Preprocess `:PATH` emission for ambiguous lhs positions
   (HOW-MANY-MSORT).
