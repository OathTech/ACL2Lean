# Final close-out audit — 2 Opus reviewers (inside + outside), synthesis

Charter-pre-approved audit of the sorting-final-closeout arc
(f13284c..4969f50). Both reviewers ran adversarially against primary
sources; findings verified/adjudicated by the main line; the fix round
follows each disposition. Severity tags are the reviewers'.

## Convergent top finding — BSORT-IS-ISORT's row was VACUOUS

Outside DEFECT 1 + inside CONCERN 4, independently: the row's kept
`usefi:WEAK-SORTFN1-IS-SORTFN2` hypothesis (`∀ env', EvTrue w env' Φ`)
has Φ == the row's own goal (the tautology-dropped FI shape:
`:HYPS == :INPUTCLAUSE` in the emitted payload). The registered
statement was `… → (∀ env', ⟦Φ⟧) → EvTrue w env ⟦Φ⟧` — verified by the
outside reviewer with an `rfl` probe (the row's proof is literally
hypothesis projection; a control probe on a different hypothesis
fails). The seven other conditions decorate the LET-BOUND constraint
proof (a discarded side proof), so the cond list suggested substance
the type does not have. MSORT/QSORT are unaffected (their usefi is
discharged by the 2c alias-world composition; probes confirm
non-vacuity). PCE and HOW-MANY-SMALLER-BNEXT probed non-vacuous.

**FIX (landed this round): the FI self-vacuity choke point.** A kept
`usefi:` hypothesis whose formula IS the row's goal appends the
reserved `ASSUMED:fi-self` marker (Harness), and the runner's ASSUMED
choke point renders the row ASSUMED ◌ and refuses registration — the
`assumedDpFactCond` doctrine's second instance; both `driver_replayed%`
and `parametric_replayed%` guards extended. BSORT-IS-ISORT returns to
ASSUMED ◌ (the D3 plan's original predicted ceiling); the corpus count
drops 107 → 106. The D3 composition itself (chain → clausify → tau
discharge, every gate a verified read-off — inside C4 credits this)
stays; the row turns ✓ when the usefi discharges (bsort cluster
greens). The missing statement pin (outside CONCERN 5) is deferred to
that point — unregistered rows cannot be pinned.

## Inside DEFECT 1 — dedupSkipClose is un-ruled inference at an
## emission-precedent site

The add-literal duplicate-drop arm infers from clause shape at the
member-term branch of the SAME upstream `cond` whose
member-complement-term branch was user-ruled (2026-08-06) to need an
emission. Semantics verified correct (keep-last matches the upstream
right fold); soundness not in question (byCases). **FIX: the arm is
now HELD UNDER EXPIRY** (docstring marker mirroring the
complement-close precedent); the `emit/dedup-drop` fork record is
QUEUED for the next batch's item-by-item review. Flagged to Mike in
the final report.

## Inside DEFECT 2 + outside CONCERN 4 — the anchoring resolver was
## weaker than its docstring

`posSame` compared frames only; the single-anchored and all-unanchored
exits skipped the metadata agreement the docstring claimed; the batch
doc's "NO tiebreak" overclaimed (the anchored-over-unanchored
selection IS a ratified preference). Verified mitigations: no wrong
proof possible (identical conclusions); the preSwap-mismatch path was
unreachable. **FIX: all survivors must now canonicalize and agree on
the canonical preSwap; full-metadata agreement among anchored
survivors; only anchored-over-unanchored may differ. Docstring and
batch doc corrected.** Convert book re-verified unchanged post-fix.

## Inside DEFECT 3 — b95f14d's golden re-pin under a fast-gate

Historical (pre-reboot): the re-pin commit's gate was interrupted by
the machine reboot; 3b4a152 later recorded that the gate had completed
TRUE_EXIT=0, but by assertion — no artifact. Immutable commits; the
honest treatment is this disclosure. Mitigation: every subsequent full
gate (c0cb74b, 212465e, 4969f50, and this round's) covered supersets
of that tree's content. SYSTEMIC NOTE for a future increment: gate
runs leave no in-repo artifact, so TRUE_EXIT claims rest on commit
messages (both reviewers' could-not-verify lists name this).

## Inside CONCERNS C1/C2/C3, outside CONCERNS 3/6 — reconstruction-
## class drift, each now marked

- C1 (LEXORDER-ORDER rung): supplies a kernel-checked justification
  (ground-zero order axioms) for a type-alist entry whose recorded
  rune basis is empty. **Marked HELD UNDER EXPIRY** (rung-B class) —
  expires when entry-derivation provenance is emitted.
- C2 (installBranchTrueFacts): the "assume-true-false decomposition"
  provenance claim was unsupported (upstream `normalize` distributes
  composite tests instead). **Docstring corrected** to the honest
  claim: value-level entailments of the recorded branch assumption.
- C3 (shared `equal/cdrs-decision` origin, negative side discards *t*):
  verified unreachable today; **guard comment added** — split the
  origins in the fork before that side ever becomes consumable.
- Outside 3 (DP premise scan over all stored rules cites rules ACL2
  did not cite — e.g. rule:TRUE-LISTP-BSORT): PRE-EXISTING mechanism
  (fold-back-audit-F2 era), not this arc's change; conditions stay
  honest (visible in the type). Logged as a scope note; no change
  this round.
- Outside 6 (dedup byCases takes a route the tree doesn't record):
  subsumed by inside D1's expiry disposition.

## Outside NOTE 7 — HOW-MANY-RM-GENERAL's assumed leaf is lemma-level

The *1/3.2 tau leaf's content is NOT-MEMB-IMPLIES-HOW-MANY-IS-0-class
reasoning, not arithmetic trivia — the ASSUMED ◌ label is honest and
the row is correctly excluded from the count, but the leaf is a
substantive hole; recorded here so the tau-frontier work is sized
accordingly.

## What both reviewers verified as solid

The fork emission (item A: zero behavior change, tag round-trips,
`check-acl2-tags` green); provenance stamps (91 logs at fork HEAD);
golden integrity across the whole arc (no green→red, tally arithmetic
reproduces); the commuted-EQUAL arm as a genuine `assoc-equiv`
read-off; the unresolved-probe block verified against the real bsort
artifact (all escape paths hard-fail); axiom cleanliness (classical
trio only, no sorry/admit/native_decide in the arc's diff); real
replay re-runs reproducing the golden byte-for-byte.

## Reviewer could-not-verify items (carried honestly)

Gate runs unverifiable post-hoc (no artifacts — see D3); the exact
reason the 2c usefi discharge declines for WEAK-SORTFN1-IS-SORTFN2
(swallowed into logInfo); pre-recapture log bytes (gitignored);
`navigateFrames`' non-validation of frame fn symbols (a PRE-EXISTING
fail-open worth its own look); `proveDpFact` internals.
