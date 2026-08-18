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

> **THE PRE-CHECK FIRED (2026-08-18) — the asymmetry stated below is
> FALSE and the removal stands on a DIFFERENT argument.** Half (i) is
> refuted by the book, the captured artifact and the 75-row inventory
> alike; Mike re-ruled on the corrected facts ("still remove, this
> seems fine") on the EXPORTED-BUT-AN-INSTANTIATION-DEVICE argument.
> See ARC LOG J-0-1 and reshape note Part 8. The bullet about moving
> the catalog entry "to the constraints tier" is also void — the row is
> RESULT TIER and stays there, annotated represented-by-instances.

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

## Item 1 — bsort_is_isort (RETARGETED 2026-08-18: driver-side, NO fork round-trip)

**The original framing is withdrawn.** It said the fork emits a
verdict with no discharge record and the fix is at emission. The
binding ground-truth pass refuted all three of its load-bearing
claims (full diagnosis in the ARC LOG, J-1-1; the wave-2g entry it
came from carries a dated correction):

1. the fork HAS emitted `:TAU-BASIS` at `emit/preprocess/tau` since
   fork-batch item I (user-ruled 2026-08-10), and the BSORT leaf's
   slice names the `TRUE-LISTP-BSORT` signature rule;
2. the citation consumer is LIVE and the leaf DISCHARGES in the real
   replay by citing that already-replayed dependency theorem
   (instrumented measurement: gate passes, match succeeds,
   `proveDpFact` + `dischargeSpine` both OK — for all five tau-basis
   leaves in the sorting corpus, zero fallbacks);
3. the N1 guard never fired on this row: the golden's `REPLAYED ✓`
   with no trailing `cond[…]` means UNCONDITIONAL, and the `cond[…]`
   that was read as the row's belongs to the standalone informational
   DP probe, which has no `ReplayCtx` and so always reports `◌`.

**Mike's ruling (2026-08-18, verbatim): "we should ALWAYS replay ACL2
when we have the material at hand."** Dep-theorem CITATION is the
route; the DP-leaf carve-out is LAST RESORT, for genuinely
verdict-only leaves with no proof record. That principle is already
what the tau-basis path implements, which is why no fix was needed
there.

- **No fork change, no recapture, no golden repin** — the emission
  side is complete and the logs are untouched, so the golden must
  stay byte-identical. ANY golden movement in this item is a STOP.
- The real blocker is the `usefi` (functional-instance) bridge at the
  waypoint layer — the second, secondary observation in J-2g-1, which
  was the accurate one.
- Then re-land the preserved decode (J-2g-2) → the `bsort_is_isort`
  product, receipts pinned. Scoreboard 14/15.
- Records corrected as part of the item: the N1 guard's error text
  (it advised "fix the leaf's emission", which is what mis-aimed the
  wave), the wave-2g ARC LOG entry, and this charter.

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
- ~~the tau leaf's obligation cannot be stated from what ACL2 itself
  possesses at emission time~~ — RESOLVED 2026-08-18: it is stated,
  emitted, and cited. Replaced by: the `usefi` bridge's gap turns out
  to need a SECOND fork round-trip or a ratified-boundary change;
- ANY golden row moves at all in item 1 (there is no recapture, so
  the golden must be byte-identical);
- the Option row cannot keep the existing transports byte-identical;
- the item-0 pre-check contradicts the classification asymmetry;
- any remaining work gates on a user decision, a ratified design
  boundary, or a SECOND fork round-trip.

## Definition of done

Mirrors/Sorting.lean holds exactly 15 Props; 15 products with trio-clean
receipts ({propext, Classical.choice, Quot.sound}); the reshape doc
carries the item-0 record; full claim-gate TRUE_EXIT=0 recorded in the
exit commit; the merge candidate presented for explicit approval.

## ARC LOG

### Items 0 and 1 (2026-08-18, branch `mdd/close-out`)

* **J-0-1 — THE BINDING PRE-CHECK FIRED, AND THE CHARTER WAS THE THING
  THAT WAS WRONG.** Item 0's stated justification was an ASYMMETRY:
  `sorter_unique`'s correspondent "encapsulate-internal … not a book
  export" vs `permWitness_complete`'s "book-exported top-level defthm".
  Half (ii) held. Half (i) was refuted by all three sources the charter
  itself named — the book (`equisort.lisp`: the encapsulate closes at
  line 102, `strong-ssortfn1-is-ssortfn2` is at line 104, top level, not
  `local`), the captured artifact
  (`sorts-equivalent.proof-log:187` carries it `:SOURCE :INCLUDE-BOOK`
  and installs it as an active `:REWRITE` rule at `:189` — the identical
  export test `CONVERT-PERM-TO-HOW-MANY` passes), and the 75-row
  inventory (RESULT TIER, never in the ENCAPSULATE CONSTRAINTS tier the
  charter said to move it to). No edit was made. Mike re-ruled on the
  corrected facts — "still remove, this seems fine" — with the argument
  that actually holds (EXPORTED-BUT-AN-INSTANTIATION-DEVICE), and the
  removal landed on that basis. Record: reshape note Part 8.
* **J-1-1 — THE bsort "EMISSION GAP" DOES NOT EXIST; THE CITATION ROUTE
  WAS ALREADY LIVE.** Measured with temporary instrumentation at the
  eligibility gate (`Totality.lean:803`), then fully reverted. The fork
  has emitted `:TAU-BASIS` at `emit/preprocess/tau` since fork-batch
  item I (2026-08-10); the BSORT leaf's slice decodes to exactly the
  `TRUE-LISTP-BSORT` spec; that rule IS in `ctx.ruleHyps`; the gate
  passes; `oneWayMatch` succeeds; `proveDpFact` and `dischargeSpine`
  both succeed. ALL FIVE tau-basis leaves in the sorting corpus
  discharge by citation, with ZERO fallbacks. The leaf was already
  doing what Mike's principle asks ("we should ALWAYS replay ACL2 when
  we have the material at hand").
  **The `◌` that started the wave is a SCOREBOARD-READING error.** The
  `[DISCHARGE: … ◌ assumed cond[…]]` annotation is the STANDALONE
  informational DP probe's (`Runner.lean:855-878`), which by
  construction (`Totality.lean:479-483`) receives no `ReplayCtx` — no
  rules to cite — and so reports `◌` on every leaf whose discharge
  needs one, forever. The ROW's own verdict, `REPLAYED ✓` with no
  trailing `cond[…]`, means UNCONDITIONAL. All SIX `ASSUMED:dp-fact`
  rows in the golden are of this kind; none is blocked, none is
  `sorryAx`-class debt.
  Consequence: NO fork round-trip, NO recapture, NO golden repin — and
  the golden verified BYTE-IDENTICAL at the end.
* **J-1-2 — THE REAL BUG: A CACHED-CONDS SHORTCUT IN THE `usefi`
  PRE-PASS** (which is J-2g-1's second, accurate observation, correctly
  attributed at last). `Waypoints/Macro.lean` recorded `[]` as the
  condition list on both CACHE branches of its termination pre-pass.
  BSORT's is the corpus's one CONDITIONAL admission — its decrease is
  licensed by `HOW-MANY-BAD-PAIRS-BNEXT`, a `:LINEAR` rule ACL2 proves
  before it admits the defun — so `usefi_term_…_BSORT` carries a premise
  binder, and applying it with no condition arguments is a type error.
  It surfaced as `depReplayedProofAt: dependency ORDEREDP-BSORT's replay
  failed (frontier)` — an error naming a DIFFERENT THEOREM, which is why
  wave 2g read it as a dependency frontier. Latent because msort/qsort
  never need BSORT's totality; the first row that does is BSORT-IS-ISORT.
  Fixed with the device `crossBookRegistry` has always used for exactly
  this: a companion `_conds : List String` constant written alongside and
  read back, fail-closed (constant without companion hard-fails).
* **J-1-3 — WHAT THE MIS-AIM COST, and where it was corrected.** One
  wave recorded a fork round-trip as the remedy, one charter item was
  written around it, and three records repeated it (the N1 guard's own
  error text said "fix the leaf's emission instead", which is the most
  likely origin). All three are corrected in place with dated blocks
  rather than quietly re-aimed: the guard text, the wave-2g ARC LOG
  entry, and this charter's item 1. The catalogue's `.pending` text for
  the row is replaced by `.native` with the correction noted.
* **J-1-4 — DISCLOSED, not silenced: a toolchain PANIC in the sweep
  log.** `Lean.LibrarySuggestions.SymbolFrequency` hits a heartbeat
  timeout while writing the `BSsortsEquivalent` module. It is a
  Lean-internal symbol-indexing pass, non-fatal — the sweep completed
  116/116 with exit 0 and the golden byte-identical. Recorded because it
  is noise in the gate log that a later reader should not have to
  re-diagnose; not investigated further, and not ours.

### Residuals at this point

* Item 2 ran as a parallel lane on `mdd/close-out-item2`; the merge of
  the two lanes is the arc's collection step and is where the header
  scoreboard reaches FIFTEEN Props / FIFTEEN proven.
* The full claim-gate (`TRUE_EXIT=0`) is owed at the arc exit, after
  collection — the two commits here are FAST-GATE labelled.
