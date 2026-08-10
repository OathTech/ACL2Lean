# Equal-descent restructure arc — charter (restructure + leftovers)

Branch `mdd/equal-descent-restructure` off main @ db44b96 (the merged
final close-out). Scope ruled by Mike 2026-08-10: the restructure plus
the leftovers pass. Baseline: 106/116 corpus (45 + 61); sorting 69/78;
the golden is the drift net; capstone statement pins in place.

## The target

Seven sorting rows hang off ONE wall — the decomposition protocol
(NodeCore/Rewrites.lean) handles a single level of rewrite-equal's
cons-descent, and HOW-MANY-BAD-PAIRS-BNEXT's tree nests descents (a
phase decision that is itself a descent, closing by equal-self on a
nested component pair). Cascade on the wall falling:
HOW-MANY-BAD-PAIRS-BNEXT → its :linear rule → termination:BSORT →
ORDEREDP/TRUE-LISTP/HOW-MANY-BSORT (the interpCount μ route) +
ORDEREDP-WHEN-BNEXT-CONSTANT (same family) → BSORT-IS-ISORT's usefi
discharge (the ASSUMED:fi-self marker lifts when the bsort deps
green). Plausible landing: sorting 76–77/78; residuals PERM-TLFIX
(the ruled R-lane deferral) and HOW-MANY-RM-GENERAL's tau leaf.

## Queue

1. **Extract, behavior-preserving.** Factor the one-level protocol
   into `replayEqualDescent` (running equality + node stream →
   verdict + consumed nodes) with NO semantic change. Bar: full sweep,
   golden BYTE-IDENTICAL. This is the regression fence for the green
   consumers (ordered-perms, 02-rev, the bsort probe blocks).
2. **Extend: recursive phase decisions.** A phase decision may be a
   recorded verdict node, an item-A decision record, or a NESTED
   descent (recurse). Anchoring: every level's verdict must be a
   recorded node/record — the item-A records bracket every phase, so
   no level is ever inferred. Drive off the real *1/6-family trees.
   Lands HOW-MANY-BAD-PAIRS-BNEXT.
3. **The cascade, row by row**: the μ-route trio + termination:BSORT;
   ORDEREDP-WHEN-BNEXT-CONSTANT's component-pair generic-tail lift;
   then verify BSORT-IS-ISORT's usefi discharge composes and the
   fi-self marker lifts (its statement pin + catalog entry land here).
4. **The leftovers fork batch — USER GATE (item-by-item review before
   rebuild, standing rule).** Candidates assembled for review:
   (a) `emit/dedup-drop` at add-literal's member-term branch (audit
   D1 remedy — retires dedupSkipClose's held-under-expiry inference);
   (b) type-alist entry-derivation provenance for the lexorder-class
   entries (retires the LEXORDER-ORDER rung's expiry);
   (c) split the negative-side `equal/cdrs-decision` origin IF item 2
   makes that side reachable (audit C3). ONE rebuild+recapture
   round-trip, sequenced fork-commit → build → recapture (the
   provenance discipline); goldens row-by-row.
5. **Small leftovers**, each its own increment, none blocking:
   navigateFrames frame-symbol validation (the pre-existing fail-open
   both auditors flagged); an in-repo gate-run artifact (the
   TRUE_EXIT-by-commit-message gap — smallest honest fix: claim-gate
   tees its tail + exit into a stamped file the commit can cite);
   the DP-premise-scan scope note logged as a ratification question
   in TODO (user decision, not built).
6. **Exit audit** — proposed for pre-approval at ratification, same
   shape as the close-out's (two Opus reviewers, inside: the
   restructure vs the recorded trees + re-pins row-by-row; outside:
   statement strength of the newly-green bsort cluster + drift test
   on the recursion) — then the fix round (TRUE_EXIT=0) and the exit
   report with the merge proposal.

## Discipline

Two-tier gating as ratified (full claim-gate at re-pins/claim points;
fast-gate labeled intermediates). Inert files only while gates/sweeps
run; fork sequencing commit → build → recapture. Item 1's
byte-identical bar is a hard intermediate claim point (full gate).

## Exit criterion + escape hatch

Done = items 1–3 landed or honestly logged at a named wall, item 4
executed or review-logged (a pending user ruling at exit is success),
item 5 done or logged, the audit run/verified/synthesized, the fix
round gated TRUE_EXIT=0, and the exit report with the merge proposal.
ESCAPE HATCH (binding): the agent may declare an early exit at any
time, for any reason or none — an honest interim state report is a
success outcome; fidelity rules and the drift tests override
completion pressure. MANDATORY-EXIT triggers: any green-row flip
without a diagnosis in hand; the extract step unable to reach
byte-identical; a fix that would require weakening a statement or
inferring an unrecorded step.
