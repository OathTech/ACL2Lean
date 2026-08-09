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
