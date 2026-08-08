# Phase 3 close-out charter — finish, audit, merge-candidate

Status: RATIFIED at goal-set (Mike, 2026-08-08). Branch:
`mdd/phase3-r7b` (continuing — the branch carries the whole R7b arc
and remains the single merge candidate). Parents: the Phase 3 charter
(`docs/plans/2026-08-08_phase3-r7b-charter.md`, exited early then
D2-resolved on Mike's direction) and its deferral log
(`docs/notes/2026-08-08_phase3-deferral-log.md`, which this push keeps
using). Long-term frame:
`docs/notes/2026-08-08_compositional-replay-design.md`.

## Goal

Finish Phase 3's tractable remainder, run the close-out audit over the
WHOLE branch, apply the fix round, and leave `mdd/phase3-r7b` as a
fully-audited merge candidate with a final report. The merge itself is
NOT part of this push (sign-off at the moment of merge, as always).

## Standing queue

1. **D1's in-scope half** — the witness-TP `dis_*` hand lemmas
   (`tp:SORTFN1-INSERT` class; `proveTp`'s return-path-CONS frontier)
   and, using the landed D2 bridging where it fits, closing the
   AtCanonical constants' remaining constraint-rule premises. The
   PERM-TLFIX R-lane leg stays DEFERRED regardless (a pre-ratified
   user checkpoint) — D1 ends as done-except-R-lane or with an
   updated log entry.
2. **D4** — the gz agreement-lemma ci check (`gz_def_implies` +
   companions; every builtin-named ground-zero snapshot either has an
   agreement lemma or is flagged) and, if cheap, the scope-in-force
   refinement.
3. **D3 (bounded)** — the BSORT useHint+clausify composition. Honest
   ceiling stated up front: FAIL → ASSUMED ◌ at best (never ✓ until
   the bsort book's emission-adjacent frontiers land), and the WEAK
   prepare keeps the FI hypothesis (ORDEREDP-BSORT is genuinely red).
   BOUNDED: if the composition resists more than a focused attempt,
   log it and move on — the ◌ move is not worth a grind.
4. **The close-out audit** — pre-approved by this charter's
   ratification (the audit-protocol sign-off): TWO Opus reviewers,
   the proven inside/outside pattern, over the WHOLE branch since
   `main` (a1f0e07):
   - *Inside* (fidelity to sources/process): the 2a FI arm vs the
     emitted `:LMI-LST`/`:CONSTRAINT-CL` payloads; the discharger and
     pre-pass (cache-key discipline — hunt relatives of the caught
     msort/qsort collision; the keyed application's type discipline;
     the prepare-time closure's channel choices); both golden re-pins
     row-by-row; the FnAlias lemma statements vs what the meta-code
     assumes of them; the tstack/budget changes' honesty.
   - *Outside* (right-thing-at-all): do the discharged capstone rows'
     statements + conditions faithfully render ACL2's
     functional-instantiation step; is the alias-world composition
     (B′/B″/A + withAliases) the a1 route as ratified; vacuity and
     over-condition checks on the new row conditions.
   Ground truth first, findings anchored file:line, independent
   verification of each falsifiable finding, honest synthesis.
5. **The fix round** — apply verified audit findings (MAJORs fixed or
   honestly logged; the golden re-reviewed if any row changes).
6. **The final report** — scoreboard, queue disposition, audit
   synthesis, deferral-log state, and the merge proposal.

## Scope boundary — what this does NOT reach

This close-out does NOT complete full sorting-book replay. After it,
the sorting corpus stands at 66-of-77 rows (+ BSORT-IS-ISORT possibly
◌). The remaining reds and their classes:

- **bsort (6 rows)** — the emission-adjacent Phase-1 frontier family
  (marker-relieved hyps, the rewrite-equal CAR phase, the generic-tail
  lift, μ-registry BNEXT-SIZE): mostly FORK-EMISSION work (a batch
  round-trip) plus bounded machinery; owns BSORT-IS-ISORT's ✓ ceiling.
- **convert-perm-to-how-many (3 rows)** — HOW-MANY-RM-GENERAL (inline
  if-window frontier), PCE-IS-COUNTEREXAMPLE (recognizer frontier),
  PERM-TLFIX (the rung-3 R-lane — Mike's checkpoint).
- **sorts-equivalent (1 row)** — BSORT-IS-ISORT, downstream of bsort.

Full sorting replay is therefore its own follow-on arc (fork batch +
the two convert machinery frontiers + the R-lane checkpoint), natural
to charter after this merge, before or alongside Phase 4's demo work.

## Binding constraints

All standing rules unchanged: the fidelity section, replay-vs-infra,
the carve-out drift test, two-tier gating (full `just claim-gate`
TRUE_EXIT=0 at golden re-pins and at exit; labeled fast-gates between),
golden re-pins reviewed row-by-row, the size ratchet, TODO and
deferral-log currency. New `dis_*` lemmas follow the established
hand-mirror pattern (world-parametric, decide-pinned hypotheses) —
never per-case provers in the driver. The compositional-replay note's
ratification is NOT consumed by this push (its questions stay open for
Mike); only the already-landed tactical machinery is in scope.

## Exit criterion

Queue items 1–3 each DONE or logged (D3's bounded-attempt log entry
counts); the audit run, verified, and synthesized; the fix round
applied and gated TRUE_EXIT=0; the final report delivered with the
merge proposal. Reachable without user input — the R-lane checkpoint
and the merge sign-off are explicitly OUTSIDE the exit.

## Escape hatch

Finish early AT ANY TIME, FOR ANY REASON OR NONE — an honest state
report is a success outcome. Mandatory-exit triggers: any soundness or
correctness concern; a drift test firing; felt pressure to weaken a
statement, widen a carve-out, or shortcut a tree; churn or per-case
accretion; an audit finding that questions already-merged work (stop
and surface it rather than patching forward).
