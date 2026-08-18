# Close-out arc charter — the sorting shop window to 15/15 (2026-08-18)

Branch: from main AFTER the r4-collect merge (which itself awaits explicit
sign-off — this charter presumes nothing about it). Mike's direction
(2026-08-18, verbatim): "our next arc should be fixing bsort_is_isort (and
then we're done!)" — plus two same-day rulings folded in: (a) sorter_unique
is defensibly REMOVED from the mirror (an encapsulate-internal
instantiation device, not a book export); (b) permWitness_complete's block
is solved by the Option refinement route ("morally the same theorem" —
Mike), not rested. End state: a 15-Prop shop window with every Prop a
proven-via-replay theorem — no structural asterisks.

This arc CLOSES the sorting line. The survey's product-first targets
(Runs/compress, Fringe/samefringe, no-dups-qsort + the IFF-decode
broadening) are a separate future arc, deliberately out of scope here.

## Item 0 — sorter_unique reclassified out (spec change, ruled)

- **Pre-check (binding, before touching the spec):** verify from the
  75-row inventory (docs/notes/2026-08-18_sorting-spec-reshape.md) and the
  book source that (i) the uniqueness theorem's correspondent is
  encapsulate-internal — consumed only via :functional-instance to mint
  the concrete X-IS-ISORT exports — and (ii) permWitness_complete's
  correspondent IS a book-exported top-level defthm (the asymmetry that
  justifies keep-vs-remove). If the inventory contradicts either half,
  STOP and report before any edit.
- Remove sorter_unique from Mirrors/Sorting.lean (16 → 15 Props). No
  tombstone (shop-window rule); the reclassification is recorded as a
  dated part in the reshape doc (the same treatment the four phantom
  Props received). Catalog entry moves to the constraints tier; the
  concrete instance products (msort/qsort/bsort_is_isort) are and remain
  the book's external face.

## Item 1 — the bsort emission fix (fork round-trip)

- **The problem (J-2g-1, measured not inferred):** BSORT-IS-ISORT's
  replayed statement carries `ASSUMED:dp-fact` from a `Goal:preprocess/tau`
  leaf — the fork emits a verdict with no discharge record, and
  `driver_replayed%` correctly refuses to register it (the N1 guard).
  Wave 2g wrote the consuming decode, measured that it closes, and
  REVERTED it rather than ship it unwired (J-2g-2; preserved in the
  wave-2g charter record).
- **The fix is at emission, per the checker-does-no-inference rule:**
  instrument the tau/preprocess leaf to emit its precisely-stated
  obligation (the clause, lifted to the Logic primitives, with the
  emitted type facts) so the replay can discharge it under the RATIFIED
  DP-leaf carve-out — the same treatment every other verdict-class leaf
  already gets. TRACE-LOG tagging convention binds (emit/ namespace,
  round-trip rule); `just check-acl2-tags` after every instrumentation
  edit.
- **Fork protocol:** commit the fork BEFORE recapture; recapture the
  affected book logs; goldens diagnosed ROW-BY-ROW before any repin —
  the expected movement is confined to the BSORT-IS-ISORT row's discharge
  annotation, and ANY other row moving is a STOP, not a fix-forward.
- Then re-land the preserved decode → the bsort_is_isort product,
  receipts pinned. Scoreboard 14/15.

## Item 2 — the Option refinement row + permWitness_complete re-spell

- **Generic machinery (not a shim):** an Option row in the
  data-refinement calculus — Lean `Option α` refines ACL2's value-or-nil
  idiom (`none ↦ nil`, `some a ↦ enc a`). This is the rendering of
  ACL2's single most pervasive return shape (member/assoc/every search
  function), witnessed here first; it lands as a table row with the same
  fail-closed shape checks as every prior row. Acceptance: ALL existing
  transports byte-identical (regression net + receipts re-pass), golden
  untouched.
- **Spec change — draft returns for Mike's bless before landing (the
  established shop-window flow):** permWitness re-spelled with an
  `Option α` witness (the junk arm and its `[Inhabited α]` instance
  eliminated — the Option form is the TIGHTEST idiomatic correspondent
  of the book's element-or-nil witness); permWitness_complete restated
  in the Option form; the crossing re-derived; the Int product landed.
  Scoreboard 15/15.
- Note the prior record honestly: the J-2e-6 kernel refutation killed a
  DIFFERENT repair (the precondition quarantine) and stands; the Option
  route was named-not-taken in the reshape era and is now taken by
  Mike's direction.

## Order

0 → 1 → 2. Item 2 is independent of item 1's fork round-trip and MAY run
as a parallel lane while capture cycles block item 1; item 0 is a
half-day spec increment done first (it changes the denominator every
later receipt cites).

## Law

Four-line canon; golden protocol as above; never push; merge only with
explicit sign-off at the moment of merge; fast-gate intermediates labeled
as such, ONE full claim-gate TRUE_EXIT=0 at the arc exit; J/O-numbered
logging; the five ask-first classes; receipts pinned; sorries 0; spec
drafts return for the bless before landing.

## Escape hatch (per the goal-design rule)

Stop and report if:
- the tau leaf's obligation cannot be stated from what ACL2 itself
  possesses at emission time (i.e. the fix would require Lean-side
  inference — an instrumentation gap deeper than this arc);
- recapture moves ANY golden row beyond the BSORT-IS-ISORT row's
  expected discharge-annotation change;
- the Option row cannot keep the existing transports byte-identical;
- the item-0 pre-check contradicts the classification asymmetry;
- any remaining work gates on a user decision, a ratified design
  boundary, or a SECOND fork round-trip.

## Definition of done

Mirrors/Sorting.lean holds exactly 15 Props; 15 products with trio-clean
receipts ({propext, Classical.choice, Quot.sound}); the reshape doc
carries the item-0 record; full claim-gate TRUE_EXIT=0 recorded in the
exit commit; the merge candidate presented for explicit approval.
