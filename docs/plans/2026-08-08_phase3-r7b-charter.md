# Phase 3 charter — R7b functional instantiation (long-cycle, low-oversight)

Status: RATIFIED at goal-set (Mike, 2026-08-08). Branch:
`mdd/phase3-r7b` (off main 3a120d9). Parent plan:
`docs/plans/2026-08-06_capstone-demo-arc.md` (Phase 3). Design inputs:
`docs/notes/2026-08-01_r7-use-functional-instantiation-design.md`
(draft — its remaining open decisions are settled by THIS charter's
ratification, scoped in "Pre-ratified decisions" below);
`docs/notes/2026-08-02_r6-encapsulate-design.md` (ratified 2026-08-02);
the Phase 2 pre-merge audit record (TODO "AUDIT 2026-08-08 DEFERRED
ITEMS").

## Goal

Build the R7b functional-instantiation composition from EMITTED content
and close out the standing queue below — each item DONE or explicitly
DEFERRED. The centerpiece: the three `sorts-equivalent` capstone rows,
whose emitted `:USE-HINT` payloads carry the full composition
(`:LMI-LST ((:FUNCTIONAL-INSTANCE STRONG-SSORTFN1-IS-SSORTFN2
(SSORTFN1 (LAMBDA (X) (MSORT X))) …))` + `:CONSTRAINT-CL` + the
constraint-discharge rewrite chain over the already-green concrete
rules).

## Pre-ratified decisions (so the push cannot block on them)

1. **Route (a)/(a1)** from the R7 note: the parametric statement is
   applied at an ALIAS WORLD (the concrete world extended with the
   constrained names bound to the instances' semantics), bridged by
   function-substitution commutation lemma(s) PROVED in the lemma
   library — **no trusted-core growth**. If trusted-core growth ever
   appears necessary, that is a mandatory-exit trigger, not a decision
   to make in-flight.
2. **The functional substitution is consumed VERBATIM from the emitted
   `:LMI-LST`** (the `(name (LAMBDA …))` pairs); the obligation source
   is the emitted `:CONSTRAINT-CL`, walked as recorded — never the
   goal, never a reconstructed substitution. Missing or mismatched
   emission → hard-fail → deferral class (b).
3. **Premise discharge at instantiation uses EXISTING machinery classes
   only** (concrete rule replay / the mirror registry, the totality/TP
   provers, kernel decide for structural facts). A premise outside
   those classes stays a kept condition or becomes a deferral entry —
   never a new bespoke per-case prover (the carve-out drift test
   governs).
4. The Phase 2 audit's stored-rule premise shape stands as landed (the
   parametric constants' premises are ACL2's stored-rule forms); the
   instantiation discharges exactly those shapes (the concrete rule
   replay produces them — verified in the audit record).

## The deferral log (the binding mechanism of this phase)

`docs/notes/2026-08-08_phase3-deferral-log.md` — append-only, kept
current in the same commit as the deferral. ANY item whose honest
resolution needs: a user decision or ratification; a fork-emission
change (batch it); a TCB or statement-derivation-path change; a
ratified-boundary amendment; or a merge/push — gets a dated entry
(what, why deferred, what it would unblock) and is thereby COVERED.

**A deferral entry is a SUCCESS outcome, equal in standing to a green
row.** Never trade fidelity, statement strength, or tree mirroring for
completion; honestly-red-with-a-named-frontier plus a log entry is a
valid terminal state for every row. This phase's design exists so that
finishing honestly is always easier than cheating.

## Standing queue (initial; grown explicitly, never silently)

1. Non-vacuity instantiation of `weakSortfn1IsSortfn2Parametric` and
   `strongSsortfn1IsSsortfn2Parametric` at the equisort canonical
   world — kernel-checked telescope discharge (closes audit O6).
2. The FI `:USE-HINT` arm: the emitted `:LMI-LST`/`:CONSTRAINT-CL`
   composition through the apply-top-hints processor.
3. `MSORT-IS-ISORT` row.  4. `QSORT-IS-ISORT` row.
5. `BSORT-IS-ISORT` row (rides the bsort book's 6 red frontiers —
   partial/classified is an expected honest outcome).
6. Phase 2 audit deferrals IF the work touches them (gz
   agreement-lemma ci check; scope-in-force refinement) — cover or
   defer with an entry.

Items the work surfaces are ADDED to this queue (in TODO's live-state
pin) or logged as deferrals — nothing silently dropped.

## Gates & discipline

All standing rules bind unchanged: the fidelity section, the
replay-vs-infra test, the carve-out drift test, two-tier gating
(fast-gate labeled intermediates; FULL `just claim-gate` TRUE_EXIT=0
at golden re-pins and at exit), golden re-pins reviewed row-by-row,
the size ratchet, TODO currency. The branch stays local: the exit
deliverable is a MERGE CANDIDATE plus the exit report plus the
deferral log — merge and push always require sign-off and are never
part of this push.

## Exit criterion

Every standing-queue item is DONE (green, gated) or DEFERRED (a log
entry naming the blocking decision). Then: the exit report —
scoreboard delta, the deferral log's contents, audit recommendation,
and the merge proposal.

## Escape hatch

Finish early AT ANY TIME, FOR ANY REASON OR NONE — an early exit with
an honest state report is a success outcome, not a failure. Mandatory
exit triggers (stop and report, don't work around): a soundness or
correctness concern of any kind; a drift test firing; any felt
pressure to weaken a statement, widen a carve-out, or shortcut a tree
to reach green; trusted-core growth appearing necessary; churn or
per-case accretion.
