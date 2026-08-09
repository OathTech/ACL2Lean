# Final-closeout fork batch — item-by-item review request

For: Mike (the standing rule: fork batches get item-by-item review
before the rebuild+recapture). Investigation state 2026-08-09; every
claim read off the current fork tree and the recaptured corpus, sites
quoted. The batch turned out SMALLER than the charter's estimate: the
old TODO items "rewrite-equal arm 18434 untagged" and "TA-RUNES
relief basis" are respectively ALREADY LANDED (both `equalityp`
case-split arms are tagged `emit/equal/case-split-lhs/rhs` and the
PCE tree consumes them) and ALREADY EMITTED (see C below).

## Item A (FORK — the one certain emission item): the rewrite-equal
## component-descent DECISION records

Site: `acl2/rewrite.lisp` ~18620-18700, the cons-cons arm ("we
(essentially) recursively rewrite the equality of their cars and then
of their cdrs"). The path-emission arc already logs the equal-cars /
equal-cdrs WINDOWS (`emit/if-window/begin` with both synthesized
component redexes) — but the arm's DECISION (the recursive
`rewrite-equal` outcome on the components: `equal-cars = *t*`,
`*nil*`, or unresolved, and likewise cdrs) is not emitted, so the
replay cannot know how ACL2 concluded the phase. Consumer message
(HOW-MANY-BAD-PAIRS-BNEXT): "rewrite-equal CAR phase — no recorded
decision and no in-scope refutation of (EQUAL (CAR X) (CAR (CDR X)))".

Proposed emission: one `:rewrite-step`-shaped record per resolved
phase (`:origin 'equal/cars-decision` / `'equal/cdrs-decision`,
`:lhs (EQUAL carL carR)`, `:rhs` the verdict `*t*`/`*nil*`, plus the
supporting ttree runes), pushed where `equal-cars`/`equal-cdrs`
resolve (the `cond` arms at ~18674 and the negative/unresolved arms),
tagged `emit/equal/cars-decision` etc. per the round-trip rule.
Unblocks: HOW-MANY-BAD-PAIRS-BNEXT → (via its :linear rule, snapshot
already emitted) termination:BSORT's assumed dp-fact → the three
bsort induction rows' interpCount μ route. The single highest-value
emission in the corpus.

## Item B (SPLIT, mostly TBD at build time): window-frame anchoring

Two consumers fail on anchoring, with DIFFERENT shapes:
- HOW-MANY-RM-GENERAL: an inline if-left window term admits 2
  distinct anchorings in the running term; the ENTRY path is recorded
  but the window-internal frames are not — the drift round explicitly
  KILLED the Lean-side "ambiguous-position preference" and restored
  the hard-fail, so the honest fix is emitting the window-internal
  :PATH for inline window steps (fork), not a tiebreak (banned).
- ORDEREDP-WHEN-BNEXT-CONSTANT: the equal-cars windows DO carry
  frames (`@ [arg 4 IMPLIES, arg 1 EQUAL]`) and BOTH component
  redexes; the generic-tail lift navigates to the equality position
  and then mismatches the component ("expected redex (CAR (CONS …))"
  vs the lhs-side component) — likely CONSUMER-side component
  selection over already-emitted data, possibly needing a small
  component-index emission if the record genuinely underdetermines
  the side. Classification finalized during the build; only the
  emission half (if any) joins the batch.

## Item C (CONSUMER — no fork change): FC-relief from the emitted
## fc-derivations record

HOW-MANY-SMALLER-BNEXT's wall: LEXORDER-TRANSITIVE's marker-relieved
hyp `(LEXORDER E (CAR (CDR X)))` has no falsity fact and its own
`:TA-RUNES` are `[]`. But the CLAUSE-level emission already carries
`fc-derivations: 1 record(s)` and the node cites
`forward-chaining:LEXORDER-TOTAL` — the relief basis (lexorder
totality from the in-clause `(NOT (LEXORDER (CAR (CDR X)) E))`
literal) IS in the log via the landed batch-3 fc/type-alist
provenance item. The build is a consumer route: the marker relief
consults the emitted fc-derivation record, with LEXORDER-TOTAL as a
D5-class prelude constant (boot FC rule — the two-class criterion's
class (i); statement recompute-checked against the emitted record).
NOT part of the fork batch; listed for completeness.

## Post-review update (2026-08-09, after the tpthm resurrection):
## PCE needs NO fork item

With the tpthm stack resurrected (fbb16f8) PCE fails only at the
chain-end reconciliation, and BOTH halves of the needed collapse are
provable from emitted data + existing machinery: (i) the
`(IF (TRUE-LISTP (CDR X)) 'T 'NIL) ⇒ 'T` half is anchored by the
emitted `:IF-TEST-TRUE` marker (IF-FINISH/IF-TEST, type-set
justification) with the test provable by the existing trueListp-CDR
closure from the clause context; (ii) the `(IF inner 'T 'NIL) ⇒ inner`
half is a VALUE-level identity — inner's branches are two-valued
primitives (`Logic.equal`/the emitted case-split shape), so the
collapse is provable with no emission. The consumer arm (a
`bridgeEqualNilNorm`-class reconciliation at CoreSpine's
reached≠recorded site) is Lean-side work.

## Second post-review update (2026-08-09, the resumed arc): items B(i)
## and C are FULLY LANDED consumer-side; the batch is A + B(ii) + D-if-ruled

- Item B's HOW-MANY-RM-GENERAL half: RESOLVED consumer-side with NO
  fork item and NO tiebreak — the drift round's stated completion
  condition ("pin all three, or prove uniqueness") was met by
  POSITION-CANONICAL UNIQUENESS (b95f14d) + synthesized branch
  anchors (0307f13); the subsequent hyp-relief wall fell by mirroring
  upstream `assoc-equiv`'s two-orientation lookup (212465e). The row
  is at its arc ceiling (ASSUMED ◌ on the *1/3.2 tau leaf).
- Item C's row (HOW-MANY-SMALLER-BNEXT) is GREEN: the fc-derivations
  relief (69a26c6) + the add-literal dedup arm (this increment —
  upstream `subst-equiv-and-maybe-delete-lit`/`add-literal` keep-last
  semantics mirrored at the spine's walk-mismatch site).
- Still open for the batch: item A (unchanged — the highest-value
  emission), item B's ORDEREDP-WHEN-BNEXT-CONSTANT half (unchanged),
  item D (R-lane-gated).

## Item D (GATED on the R-lane ruling): per-step relation at solidify

Joins the batch ONLY on a 1/2 ruling per the R-lane brief
(docs/notes/2026-08-09_r-lane-decision-brief.md). The with-lemma
`:GENEQV` half already emits (fork 24e6dbc); rung-3 is its designated
consumer.

## The ask

Approve/amend item A (and D if ruling 1/2) for the fork edit +
ONE rebuild+recapture round-trip; item B's emission half (if it
materializes) would ride the same round-trip — flagged here so the
batch review covers it in principle, exact site+shape presented
before the rebuild if it becomes a fork item. Recapture discipline
per the charter: goldens reviewed row-by-row, any drift outside the
bsort/convert reds is a mandatory stop.

## APPROVED (Mike, 2026-08-09): items A + B(ii); D joins via the
## R-lane ruling (option 2 — emission-only)

The batch = A (equal-cars/cdrs decision records) + D (the per-step
relation at the solidify site + the enclosing with-lemma record —
the F12 fidelity fix) + B(ii)'s emission half if the build-time
classification demands one. ONE rebuild+recapture round-trip. The
D item's consumer-compat caveat governs the re-pin: the emission
changes recorded fields existing consumers read, so the recaptured
corpus must sweep green (outside the expected bsort/convert
advances) before the golden re-pin.

ROUND RESULT (2026-08-09, post-recapture): item A landed and
round-tripped (rebuild + recapture-all; the log surface changed in
EXACTLY the three expected books + one build-timestamp line — byte-
identical elsewhere). Consumer side: (i) the decision-record
INGESTION keeps the whole corpus green (the duplicate consumption in
the decomposition protocol, the unresolved-probe block no-op in the
chain walker, the identity-literal predicate at the four walker
guards); (ii) HOW-MANY-BAD-PAIRS-BNEXT advanced TWO walls (the
resolved cars-decision consumed; the recorded ta-entry's disequality
closed by the new LEXORDER-ORDER rung — `logic_equal_nil_of_
lexorder_nil` anchored on the ground-zero order axioms) and now
stands at the NESTED equal-descent composition (an equal-self
decision on a nested component pair — the decomposition protocol
needs RECURSIVE phase decisions; a protocol restructure, named as
the continuation, not attempted in this round). (iii) item B(ii)
classification: CONSUMER-side — ORDEREDP-WHEN-BNEXT-CONSTANT's
generic-tail lift needs the component-pair treatment over the
already-emitted equal-cars window redexes; same nested-descent
family, NO further emission needed. The bsort μ-route rows stay
gated on HOW-MANY-BAD-PAIRS-BNEXT's completion (its :linear rule →
termination:BSORT).

BUILD-TIME FINDING (2026-08-09): item D is ALREADY FULLY EMITTED —
the solidify site records the true licensing relation
(`:equiv (ffn-symb eterm)`, rewrite.lisp ~5248) and the with-lemma
record carries the ambient `:GENEQV` relation symbols (~20731); both
landed as "fork-batch item 3, the R-lane prerequisite" (24e6dbc, an
ancestor of the fork HEAD). Under ruling 2 there is NO new fork work
for D; the deferred piece is exclusively the Lean-side rung-3
consumer. The executed fork edit is therefore ITEM A ALONE (three
decision-record pushes in rewrite-equal's cons-cons arm, tags
`emit/equal/cars-decision` / `emit/equal/cdrs-decision`,
check-acl2-tags green); B(ii) classification follows the recapture.
