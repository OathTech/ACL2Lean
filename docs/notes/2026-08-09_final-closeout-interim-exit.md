# Sorting final close-out — EARLY EXIT (interim state report)

Charter: `docs/plans/2026-08-09_sorting-final-closeout-charter.md`.
Exit invoked under the charter's escape hatch ("finish early AT ANY
TIME, FOR ANY REASON OR NONE — an honest state report is a success
outcome"). Reason: user-directed pause for machine maintenance; all
work is committed and the head commit is fully gated. The arc is
INTERIM — re-chartering or re-setting the goal on this branch resumes
it exactly here.

## State at exit (branch mdd/sorting-final-closeout, HEAD 3b4a152)

Scoreboard: **105/116 corpus (45 unconditional + 60 conditional);
sorting 68/78; convert 11/13.** Head commit b95f14d fully gated
(claim-gate TRUE_EXIT=0 — completed against exactly that tree; see
3b4a152's record correction). Every increment landed under the
two-tier discipline; three full claim-gate points this arc (fbb16f8,
c0cb74b, b95f14d) plus the still-standing ones from the close-out.

## Queue disposition (per the charter)

0. **Increment 0 — DONE** (ba9f9bd): capstone statement pins (via the
   sweep's registered constants), AtCanonical KEPT-inventory pins,
   the R-lane decision brief, weight-baseline tighten.
1. **Convert machinery — SUBSTANTIALLY DONE.**
   PERM-COUNTER-EXAMPLE-IS-COUNTEREXAMPLE-FOR-TRUE-LISTS is **GREEN**
   (c0cb74b): the tpthm consumer stack resurrected over the module
   split, the new marker-anchored IF-collapse reconciliation bridge,
   five 910785a resurrections (each now with a live consumer), and
   the elim reorder's last-position case. The CONVERT row's
   use:PCE cond discharged in cascade. HOW-MANY-RM-GENERAL's
   anchoring wall fell (b95f14d — position-canonical uniqueness, the
   drift round's stated completion condition); the row now stands at
   the solidify equation-closure wall, whose emitted basis (the
   batch-3 ta-subst provenance) is the named next consumer piece.
2. **Fork batch — REVIEW REQUESTED, not executed** (the standing
   item-by-item rule): docs/notes/2026-08-09_fork-batch-review.md.
   The batch shrank to essentially ONE certain item (A: the
   equal-cars/cdrs decision records — unlocks
   HOW-MANY-BAD-PAIRS-BNEXT → termination:BSORT → the three bsort
   induction rows via the interpCount μ route); item B is half-moot
   (HOW-MANY-RM-GENERAL went consumer-side), item C landed
   consumer-side (69a26c6), item D gates on the R-lane ruling.
3. **bsort machinery — PARTIALLY DONE ahead of the batch:**
   HOW-MANY-SMALLER-BNEXT's FC-relief wall fell (69a26c6, the
   emitted fc-derivations channel); the row stands at the known
   add-literal dedup class. The rest of the cluster is downstream of
   batch item A.
4. **D3 (BSORT-IS-ISORT ◌) — NOT STARTED** beyond the recorded plan
   (deferral log D3): downstream of the same review cycle.
5. **PERM-TLFIX — GATE-LOGGED**: the R-lane brief
   (docs/notes/2026-08-09_r-lane-decision-brief.md) awaits Mike's
   1/2/3 ruling; the charter's exit explicitly tolerates this.

Audit/fix-round/final-report: NOT run — the arc exits interim before
its pre-approved audit point; the audit remains pre-approved in the
charter for the resumption.

## The two user gates open at exit

1. The R-lane ruling (brief on the branch; recommendation: option 2,
   emission-only riding the batch).
2. The fork-batch item review (item A + D-if-ruled; B's remaining
   half classified at build time).

## Resumption recipe

Re-set the goal from the same charter text (unchanged). The TODO
live-state block carries the machine-precise continuation: (a) consume
the emitted ta-subst provenance for HOW-MANY-RM-GENERAL's equation
closure (the R1-expiry retirement path); (b) on the batch ruling, the
fork edit + ONE recapture round-trip under the charter's recapture
discipline (capstone statement pins are in place as the safety net);
(c) the bsort consumer chain; (d) the D3 arm; (e) audit → fix round →
final report → merge proposal.
