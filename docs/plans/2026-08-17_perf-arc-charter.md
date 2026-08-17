# Perf arc charter — profile-first (2026-08-17)

Branch: from main post-merge, parallel lane to R4 wave 2 (endorsed
2026-08-16, synthesis RULINGS RECORD R-6). Mike's scope additions:
(a) fold in any other CLEVER SMALLER OPTIMIZATIONS that are
TRUST-NEUTRAL; (b) DO ACTUAL PROFILING — "we have the hooks, and
that's what helped last time": the methodology of
docs/notes/2026-06-11_perf-profile.md binds (NUMBERS FIRST; the order
of attack is decided BY the profile, not by the plan).

## Phase 1 — the profile (before ANY optimization)

The hooks: Runner.lean's `timings` flag (`[t]` per-stage lines), the
per-book `coverage … ms` lines in every gate log, Lake's per-module
timings. Measure:
1. Per-book sweep walls at HEAD (compare the 7b69166 gate log and
   A5's decomposition — the a5 profile is the baseline).
2. The within-book split on the top-2 books (qsort,
   sorts-equivalent): cross-book pre-pass vs own rows vs usefi
   prepare vs buildTotalEnv vs Meta.check.
3. THE JUNE LESSON RE-TEST: is failed/assumed work still a cost
   center? The 9 ◌-assumed DP probes may burn full heartbeat budgets
   per sweep (the 2026-06-11 finding: failure was 99% of the cost
   then; make-failure-cheap was the win). Measure their cost NOW.
4. The edit-cascade check (a substantive one-line lemma edit → which
   targets re-elaborate, how long).

## Phase 2 — the attack, ordered by the profile

The PLANNED centerpiece, validated against phase 1: the D7 transport
(evalOpt_world_mono — proven, zero consumers) + module-DAG sharing so
each dep theorem/admission replays ONCE corpus-wide (A5: ~20-30 min
off every sweep; the corpus-scaling fix). FIRST TASK: reconcile
P3c's rejection (the hnew side condition via callBuiltin equation
lemmas — impossible at the fixed whnf budget) with A5's reading of
the D7 design (hnew dischargeable from the proveNoShadow facts the
drivers already build) — settle AT BUILD TIME; fall back to today's
re-replay route wherever transport doesn't apply (conditional
entries stay on the old route by construction — hypotheses are
contravariant).

Opportunistic (trust-neutral, each with its measurement): the
`just replay-book <name>` dev-loop recipe with the automatic covDeps
closure (~30 lines); the usefi-prepare scout (are the parametric
equisort constants re-derived per sweep?); the assumed-work budget
tuning IF phase 1 shows the June mechanism still paying rent;
anything else the profile surfaces.

## Law (all DISQUALIFIERS per A5, restated as binding)

Golden BYTE-IDENTICAL is the universal acceptance test — any diff is
a refusal, not a fix-forward. No persistent proof cache outside
Lake's tracking (two stale-cache incidents live in this branch's
history). No demand-seed narrowing (re-introduces the stranded
hypotheses P6 closed). No invalidation skips at claim points. No
fail-closed property weakened. Trust-neutral means: a reviewer can
verify the optimization changed WHEN things are computed, never WHAT
is proved.

## Escape hatch

Stop and report if the transport reconciliation fails both ways, if
any optimization cannot be made golden-byte-identical, or if the
profile contradicts the plan badly enough that the centerpiece
changes (that re-scope is Mike's to see).

## ARC LOG

### Phase 1 (2026-08-17) — THE PROFILE (the measurement brief is the
lane report; raw logs .tmp/perf1/; absolutes from the 36f01f2 gate log
per the noise disclosure). Headlines: redundant re-derivation = ~59%
of book elaboration (SE pre-pass 1086s incl. 3 admission re-replays;
usefi layer ~700-760s; other pre-passes ~193s); the QSORT admission
proved 3x/sweep; JUNE RE-TEST: the make-failure-cheap fix HELD, the
regime inverted (assumed work 31s ≈ 1% — budget tuning DROPPED, no
prize); quiescence/memo healthy (2 rounds typical, zero wasted
re-attempts); NEW COST TIER: the edit cascade (Waypoints lib chain
~1050s/edit, SortingPins 799s SERIAL after BSsortsEquivalent,
PatternPins 652s) — post-edit gate critical path ~80 min explained.
Dev-loop recipe LANDED (just replay-book, covDeps parsed from the
Harness at runtime — no drift table; parity gaps documented in the
recipe). Instrumentation: timings-gated [t] lines in crossBookRegistry
+ the quiescence census on the TP_DIAG sink — behavior-zero, sweep
passes timings=false, golden verified untouched.

### O-4 (orchestrator, 2026-08-17) — phase 2's order of attack,
decided BY the profile per the binding methodology:
1. THE TRANSPORT (D7 via the proven evalOpt_world_mono + module-DAG
   sharing), EXTENDED TO ADMISSIONS (the profile's 3x-QSORT finding
   makes admission sharing explicitly in scope). Prize ~24 min
   CPU/sweep, confidence HIGH. First task: the hnew reconciliation
   (P3c's equation-lemma failure vs A5's proveNoShadow route) settled
   at build time; fallback = today's re-replay; golden byte-identity
   the acceptance test.
2. THE USEFI CONSUMPTION: prepareUseFi consumes the EquisortParametric
   library constants; the admission constants share one namespace with
   (or ride) the transport. Prize ~11-13 min/sweep.
3. THE CASCADE TIER (new, flagged by the profile): investigate
   breaking SortingPins' import of BSsortsEquivalent — CAUTION: the
   capstone pins reference the sweep-registered constants, so the
   decoupling must keep the pins binding the same constants or it is
   refused; take only if honestly decoupled, fail-closed. Plus a look
   at Waypoints/Qsort.lean's 564s elaboration.
4. Budget tuning: DROPPED (the profile's verdict).
