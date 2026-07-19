# msort-frontiers arc — close-out (2026-07-19)

Branch `mdd/msort-frontiers` (off main c5900c4). The MDD-ratified 4→5→3
sequencing from the decrease-prover plan's follow-up list, plus authorized
small/moderate knock-outs. This arc ran off commit messages + per-increment
golden reviews rather than a ratified plan doc — flagged by the pre-merge
audit (R3-C.2) as a process gap; this note is the post-hoc record.

## What landed (per-increment, each gate-green: ci + reviewed golden +
## diff-test 389/0 + zero warnings)

1. **Item 4a — chain-to-child preprocess route** (4e876e5): a multi-literal
   preprocess node whose step chain rewrote the clause under a NO-OP
   clausify continues into its single child by replaying the chain over the
   disjunction. Audit R1 verified the dispatch guard cannot capture a
   differently-processed node.
2. **Item 4b — generalize type-restriction literals + gz TP emission**
   (af22a38; fork d378b32da2): the restr/core split + TP-backed head-drop
   in replayGeneralize; the ground-zero snapshot now emits
   :TYPE-PRESCRIPTION events (EVENS/ODDS previously had NO emitted TP).
   Corpus-wide effect: a tau-contradiction DP leaf flipped assumed→
   discharged (✓18/◌18); conds gained tp:ACL2-COUNT entries.
3. **Item 5 — :PATH at preprocess sites** (4cbe6a5; fork 6762183d9d):
   `infra/abbrev-path` dynamic frame stack in expand-abbreviations-lst
   (registered in *initial-program-fns-with-raw-code* — the build's
   raw-code coverage check requires it); the replay chain navigates the
   emitted path with verify-the-redex instead of ambiguous subterm search.
4. **Item 3 — clause-scoped litFacts** (356273b + audit fix): the solidify
   "source equation" mismatches were STALE INDEX-KEYED litFacts leaking
   across clause boundaries; cleared at fresh-numbering child descents
   (clausify-split outputs, chain-to-child, composeSplit residuals, spine
   residual, eliminate-irrelevance), kept at the push-clause defer
   (identical clause). Term-keyed channels (segFacts/vals/varVals) flow
   through — the context-subst design.

## Scoreboard

28/79 REPLAYED (24 unconditional) throughout — no row regressed in any
committed golden (audit R3 re-derived all four evolutions independently).
All seven msort rows' ORIGINAL walls are gone; three rows (TRUE-LISTP-MSORT,
HOW-MANY-MERGE2, HOW-MANY-MSORT) now share ONE wall: the clausify
recompute's un-mirrored expand-and-or normalization ((ENDP x) vs
(NOT (CONSP x))) — the next-arc candidate. Remaining: marker-relieved/J6b
class (2 rows), NUMERATOR H3 (2 rows).

## Pre-merge audit (3 Opus reviewers, 2026-07-19) — disposition

ZERO soundness defects across all three dimensions; every attack scenario
verified fail-closed. Findings and actions:
- **R1-F1 (fixed — REMOVED)**: the segment-justified branch-substitution
  variant was added chasing a MISDIAGNOSIS (msort *1/3.2' has its equality
  literal IN-clause; the litFacts clearing was the sole real fix), had no
  corpus witness, and its anchoring comment cited the wrong example — the
  banned build-now-wire-later pattern. Deleted; the fail-closed error
  returns; reinstate against a real witness if one appears.
- **R1-F2 (fixed)**: eliminate-irrelevance child descent now clears
  litFacts (was non-exploitable — R1 proved litFacts empty at every
  replayClause entry today — but violated the stated invariant).
- **R1 traversal-order puzzle (resolved by orchestrator)**: the clausify
  route replays CHILDREN before bridgeClausify validates the recompute —
  so pre-item-3 the stale-litFact solidify failed inside a child before
  the bridge check; post-item-3 the children succeed and the pre-existing
  expand-and-or bridge wall surfaces. The advance is real.
- **R2-F1 (fixed, fork)**: the gz TP emitter selected `(car tps)` from the
  END-OF-BOOK world — a user :type-prescription defthm about a gz fn
  PREPENDS and would displace the definitional TP. Now selects by rune
  base-symbol (= fn name); the admission-time emitter was immune. Not
  triggered by the current corpus.
- **R2-F3 (fixed)**: abbrev-path comment now says "only ARGUMENT-positional
  recursion" (in-place arms need no frame).
- **R2-F2, R2-F4, R1 exact-match fragility (recorded, no action)**:
  leaf type-sets under final ens (structural for gz fns); expand-and-or-
  initiated expansions carry no/subterm-rooted paths (fail-closed
  fallbacks); mkNegEq orientation matching is syntactic (fail-closed).
- **R3-A.5 (recorded — HONEST STATUS)**: the generalize HEAD-DROP
  construction (TP instantiation + evtrue_tail peeling) has NO end-to-end
  kernel-checked consumer: both consuming theorems fail inside the child
  replay before the drop loop runs; only the restr/core SPLIT validation
  is exercised green. Same class as the #37 S4 registry: fail-closed
  infrastructure awaiting its consumer — it must not be described as
  validated until an msort row replays through it (the expand-and-or arc
  is the unlock).
- **R3-C.1/C.2 (fixed)**: TODO.md synced; this close-out note written.
