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

- S0: probe the msort tree for the EVENS bridge (read-only; answers the
  hard part before any code).
- S1: Count.lean additions (`cdr_le`/`car_le`, any sum compositions) —
  proved, no `sorry`.
- S2: `dischargeDecrease` in Totality.lean + `totWalk` call-site move
  (single-var destructor chains first — covers the cddr rows).
- S3: `replayInduction` rerouted; J2/J4 fragments deleted; cddr rows land.
- S4: registry (EVENS/ODDS) + bridge; msort rows land.
- S5: sum measures; MERGE2 row lands. Golden updated + reviewed at each
  landing.
