# Path-emission sub-arc (charter, MDD-approved 2026-07-31)

**Parent arc:** sorting-completion-2 (`mdd/sorting-completion-2`,
docs/plans/2026-07-30_sorting-completion-2-arc.md). **Branch:**
`mdd/path-emission`, off the parent arc branch — folds BACK into the
parent when its gate passes; it does NOT merge to main on its own. The
eventual pre-merge audit reviews the instrumentation change together
with the replay simplification it pays for (one unit of review).

## Why (the decision, recorded)

ORDEREDP-APPEND's wall is `relativizeAndStrip`'s documented composition
gap: node `:PATH`s are raw gstack coordinates, and when a chain collapses
an `if` mid-walk, deeper nodes' frames navigate structure the running
term no longer has. The replay currently patches around this with THREE
mechanisms (relativizeFrames' depth/boundary for definition bodies; the
`strip` lists for root if-collapses; if-finish's local `strip'`
arithmetic) whose composition is the documented not-handled case.

MDD decision (2026-07-31): fix at the SOURCE — the fork emits the
position information the replay needs, instead of the replay
reconstructing it ("where ACL2 already has the information we need,
avoid reconstructing it and just emit it"; the mapping plan's ratified
"prefer fork emission over Lean-side reconstruction"). The Lean side
becomes simple, shrinking our opportunity for error; the residual error
surface lives in well-tested ACL2. An ad-hoc third strip list is
explicitly OFF the table (the parent arc's no-epicycles criterion).

## The crux the spike must resolve

ACL2's rewriter has NO "running term": it recurses into the OLD term and
builds the result on the way out. So "term-relative" coordinates need a
defined anchor. Current best candidate — **more window structure, not
smarter flat paths**: emit explicit BEGIN/END windows per branch descent
carrying the window's INPUT term, so every step's `:PATH` is trivially
local to a window whose term the replay holds verbatim; cross-collapse
position arithmetic disappears entirely. (The existing BEGIN-LITERAL /
BEGIN-INNER-REWRITE windows are the precedent; this extends the idiom to
the rewrite-if descent.)

## Phases and gates

- **Phase 0 — the SPIKE (no corpus commitment).** Deliverables:
  1. A CENSUS of gstack frame classes vs. the divergence sources the
     replay patches around today: if-collapses (rewrite-if constant-test
     and or-collapse), definition-body coordinates (`(BODY . IF)`
     frames), the rewrite-equal SCRATCH redexes (bkptr 1/2 synthesized
     components), if-finish branch re-entries, lambda bodies, hyp/rhs
     inner windows. For each: what the gstack frame says, what the
     replay's running term has, which Lean mechanism currently bridges.
  2. A WRITTEN emission semantics (anchor + coordinate rule), reviewed
     against every census row.
  3. A PROTOTYPE emission for the rewrite-if family ONLY, validated
     against the ORDEREDP-APPEND chain (the failing *1/2'-family
     literal-5 window in qsort.proof-log).
  4. A consumer-migration cost estimate: which replay mechanisms retire
     (relativizeFrames depth/boundary, strip lists, if-finish strip',
     the swap-bridge path juggling), which node recipes need touching.
- **DECISION CHECKPOINT (MDD).** The semantics + prototype + cost
  estimate go to MDD before the corpus-wide switch — the one
  irreversible-ish step (every `.proof-log` regenerated; every path
  consumer touched).
- **Phase 1 — implement + recapture + parity.** Corpus-wide emission,
  full recapture, consumer migration WITH retirement of the three
  mechanisms (the parent arc's epicycle criterion — migration that
  keeps the old mechanisms alive does not pass the gate).

## Fold-back AUDIT (required; defined per the 2026-07-31 goal amendment)

Sub-arcs fold into the parent arc WITHOUT user sign-off but MUST pass a
comprehensive audit first. Definition for THIS sub-arc (the CLAUDE.md
audit pattern, adversarial, ground-truth first):

- **Ground truth:** the full sweep on the new emission, `#print axioms`
  on a replayed row, the retired-mechanism deletion diff, and a raw-log
  window sample diffed against the corresponding gstack trace.
- **Reviewer A (fork emission soundness, INSIDE):** does every emitted
  window `:TERM` equal, verbatim, the term ACL2's rewriter actually
  descends into (instantiation correctness — the lazy (term . alist)
  pairs are the risk: a mis-instantiated window term would make the
  replay silently prove steps against the wrong subterm)? Anchored to
  the rewrite-entry/rewrite-if/rewrite-equal sites, adversarial persona.
- **Reviewer B (replay fidelity, INSIDE):** did the consumer migration
  add any inference or shape-guessing, and are the three mechanisms
  DELETED (not bypassed)? Every navigation now record-directed?
- **Reviewer C (OUTSIDE):** is the window semantics faithful to the
  gstack as a black box — feed a chain and check window nesting equals
  gstack bracketing; hunt for a frame class the census missed.
- **Verification pass:** each falsifiable finding independently
  re-checked against the source, default-refute; survivors adjudicated
  and the highest-stakes ones spot-checked in the main session before
  the fold-back.
- Scale: one Opus reviewer per dimension (3) + one verifier — within
  the standing mid-point audit authorization; NOT a merge-to-main
  authorization.

**Gate to fold back into the parent branch:** full sweep at ≥69/79
parity on the new emission (byte-level row comparison for the
unaffected rows), ORDEREDP-APPEND past its path wall (green, or
advanced to a non-path frontier), `just ci` green, the retired
mechanisms deleted (not bypassed).

## Parent-arc work that continues AFTER the fold-back

HOW-MANY-QSORT (D), MSORT-IS-ISORT/QSORT-IS-ISORT (B), the type-set
walker consolidation (the second mandated epicycle elimination), then
the sorting mirror program — per the parent charter's amended criteria.

## CLOSED (2026-07-31): folded back into mdd/sorting-completion-2

Gate met in full: sweep 70/79 BYTE-IDENTICAL to the pre-emission golden
(better than the ≥69/79 parity bar), ORDEREDP-APPEND green (the
validating case), `just ci` green, the three mechanisms deleted (plus
the audit round's deletions: the collapseEval rung, the write-only
depth/chainPrefix-Nat). The fold-back audit ran per this charter
(3 adversarial Opus reviewers + default-refute verifier); every
confirmed finding was fixed and re-verified (BUG-024/025/026 fixed at
the fork with full recapture; BUG-027 open for the parent merge
review). The fix round's own consumer rework (branch-anchored windows,
begin-if adopter lookahead, chain-end normalizers — the census's
"regression round" section) is gate-validated (byte-identical sweep +
new pins) but postdates the reviewers — in scope for the parent arc's
pre-merge audit. Fold-back merge: fast-forward 371b7a6..4202c06,
sub-arc authorization per the standing goal (audit passed; no user
sign-off required for sub-arc folds).
