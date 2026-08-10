# Sorting final close-out — FINAL REPORT + merge proposal

Charter: `docs/plans/2026-08-09_sorting-final-closeout-charter.md`.
Branch `mdd/sorting-final-closeout`; this report is the charter's exit
deliverable. The exit criterion is met: queue items 0–4 each DONE or
honestly logged, item 5 gate-logged with the user ruling recorded, the
audit run/verified/synthesized, the fix round applied and gated, and
this report with the merge proposal.

## Scoreboard

**106/116 corpus (45 unconditional + 61 conditional); sorting 69/78;
convert 11/13 + HOW-MANY-RM-GENERAL ASSUMED ◌.** Arc start (at
f13284c): 104/116. The number went 104 → 107 → 106: the final −1 is
the audit's own top finding applied — BSORT-IS-ISORT's conditionally
green row was VACUOUS (its kept usefi hypothesis IS the goal) and is
now honestly ASSUMED ◌ under the new `ASSUMED:fi-self` choke point.
An honest 106 beats a vacuous 107.

## Queue disposition

0. **Increment 0 — DONE** (ba9f9bd, pre-reboot): capstone statement
   pins, AtCanonical pins, the R-lane brief, baseline tightens.
1. **Convert machinery — DONE at its arc ceiling.**
   PERM-COUNTER-EXAMPLE-IS-COUNTEREXAMPLE-FOR-TRUE-LISTS GREEN
   (tpthm resurrection + the marker-anchored IF-collapse bridge +
   five 910785a resurrections + the elim last-position case); the
   CONVERT row's use:PCE cond discharged in cascade.
   HOW-MANY-RM-GENERAL: FOUR walls fell across the arc (anchoring
   position-canonical uniqueness; solidify equation closure via
   branch-fact decomposition; the hyp-relief wall via upstream
   `assoc-equiv`'s two-orientation lookup, mirrored verbatim) —
   ASSUMED ◌, residual = its *1/3.2 preprocess/tau leaf (the tau
   frontier, charter-scoped OUT; note the audit's caution that this
   leaf is lemma-level, not trivia).
2. **Fork batch — RULED and EXECUTED.** Mike approved A + B(ii);
   item A (the equal-cars/cdrs decision records) landed and
   round-tripped (rebuild + recapture-all, provenance-stamped at the
   fork HEAD e685362c9e; the log surface changed in exactly the three
   books with equal descents). Item D turned out ALREADY EMITTED
   (24e6dbc); item B(ii) classified CONSUMER-side (no emission).
3. **bsort machinery — two rows advanced, the rest honestly logged.**
   HOW-MANY-SMALLER-BNEXT GREEN (fc-derivations relief + the
   add-literal dedup arm — the arm now held under an emission expiry
   per the audit). HOW-MANY-BAD-PAIRS-BNEXT advanced two walls (the
   recorded decision consumed; the LEXORDER-ORDER rung) and stands at
   the NESTED equal-descent composition — a decomposition-protocol
   restructure (recursive phase decisions), logged as the named
   continuation with its artifact anchors. The three μ-route rows +
   termination:BSORT ride its completion.
4. **D3 — DONE.** `replayUseHintClausify`: constraint chain →
   recorded clausify checkpoint → tau verdict leaves → the
   tautology-dropped FI instance, every gate a verified read-off
   (both auditors credit this); the let-bound constraint proof
   surfaces its assumptions. The row it composes is ASSUMED ◌ until
   the usefi discharges (see the audit) — the D3 plan's original
   predicted ceiling, reached honestly.
5. **PERM-TLFIX — GATE-LOGGED + RULED.** Mike ruled option 2
   (emission-only); the emission halves were found already landed, so
   the deferred piece is exactly the Lean-side rung-3 lane (its own
   future charter). The row stays red; the charter's exit counts this
   as success.
6-7. **Audit + fix round — DONE.** Two Opus reviewers (inside +
   outside), synthesis at
   `docs/audits/2026-08-09_final-closeout-audit.md`. Every DEFECT
   dispositioned: the vacuity choke point (landed), the anchoring
   resolver tightened to its documented contract (landed), the dedup
   arm marked held-under-expiry with the `emit/dedup-drop` fork item
   QUEUED for the next batch review, the b95f14d gate-record deviation
   disclosed. Fix round swept (exactly the one intended row change),
   golden repinned after row-by-row review, full claim-gate
   TRUE_EXIT=0 recorded in the closing commit.

## Open user gates carried out of the arc

1. The `emit/dedup-drop` fork item (the audit's D1 remedy) — next
   batch review.
2. The R-lane rung-3 Lean lane — its own charter (ruling 2 recorded).

## Named continuations (no user gate, next arc's queue)

- The NESTED equal-descent composition (HOW-MANY-BAD-PAIRS-BNEXT →
  its :linear rule → termination:BSORT → ORDEREDP/TRUE-LISTP/
  HOW-MANY-BSORT via the interpCount μ route; B(ii)'s component-pair
  generic-tail lift is the same family).
- The tau-frontier family (HOW-MANY-RM-GENERAL's leaf; the D3 row's
  usefi discharge unlocks with the bsort cluster).
- Systemic notes from the audit: gate runs leave no in-repo artifact;
  `navigateFrames` does not validate frame fn symbols (pre-existing
  fail-open); the DP premise scan's breadth vs the carve-out wording.

## Process deviations (disclosed)

- b95f14d (pre-reboot) re-pinned the golden under a fast-gate; the
  completing gate run is attested only by 3b4a152's record.
- Two sequencing errors this session, both self-caught and both
  ultimately gated clean: a coverage sweep was started before a source
  edit landed (killed, re-run), and the corpus recapture overwrote
  logs while a claim-gate was running (gate killed, re-run; the
  recapture itself then re-done after the fork commit when the
  provenance gate rejected the dirty-tree stamps — the ratchet worked).

## Merge proposal

The branch is ready to propose: 24 commits over f13284c, every claim
point gated TRUE_EXIT=0 (this round's closing gate included), goldens
reviewed row-by-row at each re-pin, the audit synthesized and its fix
round landed, the fork submodule at e685362c9e (branch
acl2-lean-output) with tags round-trip-clean and 91 logs
provenance-stamped. Per the standing rule I am NOT merging: this is
the report-and-ask. If approved, the merge is a fast-forward of local
`main` to this branch's head after a fresh local `just ci` on the
merge commit's tree (the sandbox protocol); remote push remains
outside the sandbox with `just check-push-ready` (fork remote first).
