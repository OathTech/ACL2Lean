# Sorting-book FINAL close-out charter

Status: DRAFT — ratified when Mike sets the goal from it. Branch:
`mdd/sorting-final-closeout` (off `main` f13284c — the merged Phase 3
arc). Parents: the Phase 3 close-out
(`docs/plans/2026-08-08_phase3-closeout-charter.md`, its final report,
and its audit `docs/audits/2026-08-09_phase3-closeout-audit.md`).

## Goal

Take the sorting corpus from 67/78 to **78/78 rows REPLAYED ✓**, each
conditioned only on genuine theorem-rule/tp/totality residue — with
BSORT-IS-ISORT green — and leave the branch a fully-audited merge
candidate. One queue item (PERM-TLFIX) runs through a USER GATE and
the exit criterion explicitly tolerates its deferral.

## Exit bar (fixed up front — what "full" means here)

IN: the 11 red rows (bsort×7 incl. termination:BSORT; convert×3;
BSORT-IS-ISORT); the D3 chain→clausify→verdict composition; honest
conds only (no new ASSUMED classes on previously-green rows).

OUT (each its own future arc; listing here is the drift guard):
- The tau frontier: `◌ assumed` DISCHARGE PROBES stay informational;
  closing them is not this arc.
- Full `husethm_ORDERED-PERMS` closure on the AtCanonical witnesses
  (tau-dependent). If PCE-IS-COUNTEREXAMPLE greens, DO consume the
  free win: the `hrule_CONVERT-PERM-TO-HOW-MANY` premise and the
  CONVERT row's `use:` cond.
- The compositional-replay ratification (open with Mike separately).
- Any non-sorting corpus work beyond incidental strengthening.

## Standing queue

0. **Increment 0 — the recapture safety net (BEFORE any fork work).**
   (a) Capstone-row STATEMENT PINS: a sorts-equivalent section in
   `Tests/SortingPins.lean` pinning MSORT-IS-ISORT and QSORT-IS-ISORT
   statements against types hand-transcribed from
   `sorts-equivalent.lisp` (close-out audit follow-up, both
   reviewers). Rationale: recapture invalidates every log — exactly
   the window where statement-derivation drift (F5b) is live.
   (b) The AtCanonical KEPT-INVENTORY pin (audit n1): the two-premise
   list may only shrink.
   (c) The R-LANE DECISION BRIEF for Mike: the rung-3 equiv-lane
   design question stated with options and consequences, delivered
   early so the ruling is available before the convert cluster needs
   it. (d) Housekeeping: tighten the file-weight baseline for the
   shrunk Sorting.lean.
1. **Convert machinery (no fork dependency — start while any fork
   batch is in review).** HOW-MANY-RM-GENERAL's inline if-window
   frontier and PCE-IS-COUNTEREXAMPLE's recognizer frontier, from
   their TODO read-outs. PCE has triple leverage (its row, the
   CONVERT row's use: cond, the AtCanonical hrule_ premise) — take
   the knock-on discharges in the same increment.
2. **The bsort fork-emission batch.** The four diagnosed items
   (marker-relieved hyps; the rewrite-equal CAR phase; the
   generic-tail lift; μ-registry BNEXT-SIZE), authored under the
   TRACE-LOG tagging convention, `just check-acl2-tags` clean,
   through real ACL2 (`just build-acl2` + recapture), provenance
   gates green. Golden re-pins from recapture are reviewed
   ROW-BY-ROW with full claim-gates (the two-tier rule) — expect
   byte-identical outside bsort; any other drift is a stop-and-look.
3. **bsort driver machinery** riding the new emissions, row by row,
   until the book is 10/10 (termination:BSORT included).
4. **The D3 composition**: the FI arm learns to traverse
   chain → clausify checkpoint → verdict closure (the exact plan in
   the deferral log's D3 close-out entry). Lands BSORT-IS-ISORT — ◌
   first if the bsort book still lags, ✓ once it doesn't.
5. **PERM-TLFIX — USER GATE, then build.** Mike rules on the rung-3
   R-lane brief (item 0c). If approved: build the rung-3 lane and
   green the row. If deferred or unruled by the time the rest is
   done: PERM-TLFIX stays red with a deferral-log entry, and the arc
   still exits (the exit criterion below counts this as success —
   77/78 + the logged gate).
6. **Pre-merge audit** — PRE-APPROVED at ratification with the same
   shape as the close-out audit (two Opus reviewers, inside: fork
   emissions vs upstream diff + tag round-trips + recapture
   provenance + re-pins row-by-row + the new machinery vs emitted
   payloads; outside: are the new emissions faithful instrumentation
   of what ACL2 actually does, statement strength of the newly-green
   rows, carve-out drift check on any new discharge classes).
   Verification of findings by the coordinating agent; cost is two
   Opus agent runs, as before.
7. **Fix round** (gated TRUE_EXIT=0) and **final report + merge
   proposal** (sign-off at the moment of merge, as always).

## Binding constraints

All standing rules unchanged: the fidelity section (mirror the tree,
hard-fail at frontiers, no inference in the checker), the carve-out
drift test, replay-vs-infra, two-tier gating (full `just claim-gate`
TRUE_EXIT=0 at golden re-pins/claim points; labeled fast-gates
between), golden re-pins reviewed row-by-row, the module-size
ratchet, TODO and deferral-log currency, the ACL2 tagging convention
for every fork insertion. D5 discipline: NO new prelude constants for
rules whose owning book is capturable — if the bsort work surfaces
gz-class citations, they follow the two-class criterion in
`GzRules.lean` verbatim. New emissions are additive and reviewed as
the diff vs upstream master.

## Exit criterion

Reachable without user input EXCEPT the single R-lane gate, which the
exit tolerates: queue items 0-4 DONE (or honestly logged with the
blocking frontier named — an emission item that resists a bounded
batch round-trip is logged, not ground); item 5 either built (78/78)
or gate-logged (77/78 + the PERM-TLFIX deferral); the audit run,
verified, synthesized; the fix round applied and gated TRUE_EXIT=0;
the final report delivered with the merge proposal. Merge sign-off
itself is OUTSIDE the exit.

## Escape hatch

Finish early AT ANY TIME, FOR ANY REASON OR NONE — an honest state
report is a success outcome. Mandatory-exit triggers: any soundness
or correctness concern; a drift test firing; felt pressure to weaken
a statement, widen a carve-out, or shortcut a tree; per-case
accretion in the new machinery; recapture producing ANY unreviewed
golden drift outside the bsort book; an audit finding that questions
merged work (stop and surface, never patch forward).
