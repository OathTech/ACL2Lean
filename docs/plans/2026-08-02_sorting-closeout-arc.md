# Sorting TRUE close-out arc (DRAFT — uncommitted, for MDD review)

Drafted 2026-08-02 at the sorting-absolute merge point, incorporating
the pre-merge outside audit's corrections. The predecessor arc's
lesson, encoded here twice: (1) the design checkpoints go FIRST, not
last — deferring 2d stalled every capstone; (2) completion is defined
by CHECKABLE PREDICATES, not phase names, and any skipped bullet gets
a carried-debt entry at the moment of skipping (no silent scope-drop).

## Ground truth at draft time (golden of 3f28d6c)

Sweep 80/100. Sorting: 45/62 green; 17 red = 6 convert-perm
(TRUE-LISTP-RM, HOW-MANY-RM-GENERAL, PERM-COUNTER-EXAMPLE-…-TRUE-LISTS,
PERM-TLFIX, RM-TLFIX, CONVERT-PERM-TO-HOW-MANY) + 8 bsort
(3 BNEXT-SIZE-gated: ORDEREDP/TRUE-LISTP/HOW-MANY-BSORT; 5 per-row
walls) + 3 capstones (MSORT/QSORT/BSORT-IS-ISORT, R7). Off-sweep:
equisort (41 defthms, R6), how-many/orderedp (defun-only, no rows —
completion counts them as "in the family, nothing to replay").
Non-sorting reds (CLASSIFY-POS, CD2-BOUND, LEN2-APP-VIA-USE) are not
arc-gating, though LEN2-APP-VIA-USE falls with R7a.
Standing ratifications (MDD 2026-08-02): R7 (a)/(a1); carve-out with
the drift test; BUG-027 narrow-via-emission; BNEXT-SIZE
admission-waterfall route; count rows measure-absorbed.

## ARC EXIT AMENDED (MDD 2026-08-04, after the equisort-r6 NOT-READY)

The equisort-r6 audit established that every equisort row and all three
capstones REQUIRE the abstract-world driver surface (their statements
are false at the certified world — no concrete-world route to green
exists; the attempted concrete-world proxy was the audit's F2/F3 and
was reverted). MDD direction, verbatim: "if there are things we can do
that are orthogonal to this big push, and won't build redundant infra
we'll need to replace later, let's work on them in this arc. And then
we'll close the arc with one major missing piece."

- The ABSTRACT-WORLD BUILDOUT (parametric statements, ConstraintsHold
  over the extended world, the R7b capstone application) is DEFERRED to
  a follow-on arc, opened by a design note extending the R7 note's Q3,
  ratified before building.
- This arc's remaining scope: the orthogonal, non-redundant work — the
  fork emission batch (once reviewed), bsort's walls + BNEXT-SIZE
  replay wiring, the R-lane rung-2 threading (concrete-world consumers:
  PERM-TLFIX, bsort), the IF-TEST-TRUE consumer, Phase-7 mirrors/pins/
  catalog/machinery debt.
- The predicates below are READ UNDER the amendment: P2/P3/P4 exclude
  the equisort rows and the three capstones, which close the follow-on
  arc; the pre-merge audit DECLARES the missing piece with numbers.

## COMPLETION PREDICATES (the arc is done exactly when all hold)

- P1. All 9 row-bearing family books in the sweep (the 8 current +
  equisort); how-many/orderedp recorded as defun-only.
- P2. Sorting FAIL rows = 0 in the golden.
- P3. liftCatalog has zero `.pending` sorting entries (every green row
  `.native` or `.replayedOnly`-with-rationale, per the mirror
  criterion + the measure-absorbed doctrine).
- P4. Statement pins ≥ 1 per sweep sorting book (9 books).
- P5. The drift-test review (memory: carve-out-drift-test) run at arc
  close: no per-case discharge code accreted; result recorded.
- P6. `just ci` green (pipefail-honest), goldens byte-stable across a
  forced double elaboration (the determinism check), audit reports
  committed in docs/audits/.

## STANDING RULES (goal-referenced; survive context loss)

Amended 2026-08-03 at goal reinstatement — the goal text points HERE.

- STATE DISCOVERY on every (re)start: `git log` on the arc branch, the
  close-out sections of TODO.md, docs/audits/, and this plan. Never
  assume conversation memory.
- SUB-ARC DISCIPLINE: substantial increments run as sub-arcs; each
  passes a comprehensive adversarial audit whose findings + verdict
  are COMMITTED to docs/audits/ BEFORE fold-back (conversation-only
  audit records do not count). A NOT-READY verdict's fix round is
  re-verified by a FRESH verifier against the committed record.
- CLAIM GATE: no commit may claim completion or green status without
  a pipefail-honest full `just ci` exit recorded in it
  (`just claim-gate`).
- FORK BATCHING: emission changes batch into one rebuild + one
  `just recapture-all` + row-by-row golden review per round.
- STOP-EARLY CONDITIONS (stop and report plainly, no reframing):
  1. A ratified design fails against the artifact (design notes are
     amended by the user, not unilaterally).
  2. Any soundness concern, or the carve-out drift test failing
     (per-case custom proofs/checkers accreting — see the memory +
     TODO record).
  3. The equisort honest-split point: if its frontier tail runs long,
     stop at "equisort in + capstones green" with the numbers.
  4. Golden churn beyond row-by-row review.
  5. A structural instrumentation wall (ACL2-side needs something
     architecturally new, beyond more emission at existing joints).
  6. A sub-arc audit returns NOT-READY and the findings survive
     verification (happened once: docs/audits/
     2026-08-03_emission-cluster-audit.md), or a phase exceeds ~2×
     its expected scale without converging.

## Phase 0 — MDD CHECKPOINTS FIRST (the R6 design note)

The ONE remaining design item. Note covers: encapsulate emission
(:CONSTRAINT list; local witnesses marked — the BUG-019 surface,
already fail-closed at parse), the world-parametric constrained-
theorem statement shape (`∀ w, ConstraintsHold w → …` per the R7
ratification), how equisort's non-local theorems (re-proofs of perm/
ordered-perms content) ride the ordinary path, and the sweep-entry
plan. Present for ratification BEFORE building anything on it.
R7a needs no checkpoint (ratified); BNEXT-SIZE route ratified.

## Phase 1 — THE EMISSION CLUSTER (one fork round-trip, one recapture)

Corpus recapture is expensive and invalidates every include_str
consumer — batch ALL fork work into one round-trip:
- 1a. R6: :CONSTRAINT-list emission + local-witness marking.
- 1b. BNEXT-SIZE: log bsort's real admission waterfall (the
  termination field — the ratified route); the admission proof's
  helper rules are the already-green LEN rows.
- 1c. Type-alist derived-entry PROVENANCE (parent literals + FC rule):
  one emission serving THREE consumers — BUG-027's narrow-via-emission
  (equation-edge justifications), the LEXORDER-TRANSITIVE marker-
  relief class (bsort HOW-MANY-SMALLER-BNEXT + the parked ORDEREDP-
  APPEND/ORDEREDP-MEMB backlog), and the free-type-alist relief class.
- 1d. :RULE-CLASSES provenance (the equivrefl gate's shape-parse
  caveat; cheap alongside).
- 1e. Recapture corpus once; goldens re-pinned deliberately.

## Phase 2 — R7a (parallel-safe with Phase 1; no fork dependency)

Plain `:use` composition: route the useHint payload by content, not
branch shape (the BSORT-IS-ISORT finding — constraint chain walks
CONSTRAINT-CL, clausify walks the application side), instantiate used
theorems via the existing premise/substN machinery, peel the
application clause. Targets: LEN2-APP-VIA-USE green;
CONVERT-PERM-TO-HOW-MANY (its row cites the counter-example lemmas via
:use). Sub-arc audit gate as usual.

## Phase 3 — CONVERT-PERM'S SIX + THE THREE UNCLASSIFIED

- Classify frontier-or-bug FIRST (the pre-merge F12 debt):
  PERM-TLFIX (solidify literal heads NOT/PERM — likely the solidify
  source-matching class), PERM-COUNTER-EXAMPLE-…-TRUE-LISTS
  (replayRecognizer), ORDEREDP-WHEN-BNEXT-CONSTANT (pathSteps
  frames []). Each becomes a named class or a BUG entry.
- TRUE-LISTP-RM / RM-TLFIX share a trueListp-nil DP signature; likely
  one leaf-tactic/cell fix. HOW-MANY-RM-GENERAL is an ASSUMED:dp-fact
  premise gap (the 2c machinery's next instance). CONVERT-PERM-TO-
  HOW-MANY may fall to R7a (it is the book's capstone :use).
- While here: the frontier-classification MECHANISM (typed frontier
  tag, not per-message prose — the F12 sub-item).

## Phase 4 — EQUISORT IN (R6 build-out)

Parse/world support for the constraint emission; equisort into the
sweep. Its 41 defthms ride the ordinary waterfall machinery (they are
perm/ordered-perms-class proofs); expect a tail of ordinary frontiers
— budget the majority of row work here. The constrained-theorem
parametric statements validate here (R7b's prerequisite).

## Phase 5 — R7b: THE CAPSTONES

The alias-world commutation lemma (EvalLemmas, ordinary proved lemma);
apply the parametric constrained theorems at the concrete worlds;
MSORT/QSORT/BSORT-IS-ISORT + sorts-equivalent green. The family's
headline mirrors: `msortL/qsortL/bsortL = isortL` natively (the
generator's exec models already exist for msort/qsort; bsort's from
Phase 1b machinery).

## Phase 6 — BSORT'S REMAINING WALLS + DETAIL-CHAIN REPLAY

- The 3 BNEXT-SIZE rows via the Phase-1b admission replay.
- The remaining per-row walls (rewrite-equal CAR phase, spine
  literal-4, unemitted test resolution) — each a named class; fix at
  the class level.
- The clausify detail-chain replay (iff-in-boolean-position at the
  lift — pairs with the R-parameterized literal-chain class p4 pins);
  flips p8 to its ratified completion (green row + native mirror) and
  bsort's clausify-bearing rows.

## Phase 7 — MIRRORS, PINS, CLOSE

- The 3 pending convert-perm mirrors (List.count_eq_zero /
  List.erase_of_not_mem class) + mirrors for every row greened this
  arc, per criterion (capstones are the priority; equisort rows mostly
  `.replayedOnly` as re-proofs — rationale each).
- Pins to ≥1 per book (owed: convert-perm, bsort, ordered-perms,
  msort, perm, sorts-equivalent, equisort).
- Machinery debt swept in-arc (not deferred, per charter discipline):
  allBookRules direct walk; dp-premises F6 (premise-build failure
  must not silently downgrade a provable leaf); include-book
  provenance gate on cross offers; leaf-class gating plumb;
  generator-reads-the-log (retire the hand-transcribed bodies /
  measured indices; remaining 12 hand exec defs).
- Close: predicates P1–P6 checked mechanically; drift-test review;
  consolidated audit record committed; pre-merge audit.

## Risks

- R6 is the real unknown (encapsulate world semantics; the constrained
  replay must go through over abstract w — a tree step dereferencing a
  witness body hard-fails, which is correct but may reveal ACL2 used
  non-exported facts somewhere). Hedge: Phases 2-3 are R6-independent
  standalone value.
- The type-alist provenance emission (1c) reaches deep into
  rewrite.lisp; scope it to the three named consumers.
- Telescope growth: watch dischargeBudget under equisort-scale
  telescopes (the determinism class the cross-rules audit found);
  P6's double-elaboration check is the tripwire.
- Sequencing pressure: equisort's 41 rows are the bulk; if the tail of
  ordinary frontiers is long, the arc splits honestly at "equisort in
  + capstones green" vs "every last row" — IF that split happens it is
  declared with numbers, not framed away (the predecessor's lesson).
