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
