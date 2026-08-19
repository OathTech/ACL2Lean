import ACL2Lean.Imported.Waypoints.Macro
import ACL2Lean.Imported.Waypoints.PermBook
import ACL2Lean.Imported.Waypoints.ConvertPerm
import ACL2Lean.Imported.Waypoints.Isort
import ACL2Lean.Imported.Waypoints.Msort
import ACL2Lean.Imported.Waypoints.Qsort
import ACL2Lean.Imported.Waypoints.OrderedPerms
import ACL2Lean.Imported.Waypoints.BsortCap
import ACL2Lean.Imported.Waypoints.EquisortParametric
import ACL2Lean.Imported.SortsEquivalent
import ACL2Lean.DevLoad

namespace ACL2.Imported.Waypoints

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! ## The sorts-equivalent book — THE CAPSTONES (R4 wave 2g)

The corpus's largest book, and the last one with no waypoint presence at
all. Its three theorems are the top-level claim that the four sorts
agree, and each is proved in ACL2 by ONE node: a `:USE
(:FUNCTIONAL-INSTANCE …)` of the equisort scope's constrained-sorter
capstone at the concrete pair.

**What had to arrive, and it was not a native.** Waves 2e/2f recorded
this book as "NO waypoint module at all — no `derive_world`, no
`driver_replayed%` row". The reason it had none is sharper than that:
`driver_replayed%` had no route to a FUNCTIONAL-INSTANCE proof. The
discharge existed only as a `runBook` parameter the coverage sweep
supplies, so these three rows were replayable by the SWEEP and by
nothing else. The `usefi` clause (`Waypoints/Macro.lean`) is the same
pre-pass at this layer: the dep books' recorded ADMISSIONS carried to
this world, the library PARAMETRIC constants consumed by name, and the
prepare run in a shallow context.

Both landed rows are UNCONDITIONAL — which is what the golden's
`sorting/sorts-equivalent` section already said of the sweep, and now
holds of a waypoint row too.

THE ONE COST, disclosed: the `usefi` composition spends a native frame
per telescope binder, so `lakefile.toml` now carries the Tests lib's
`--tstack=524288` for the `ACL2Lean` lib as well. Without it the
elaboration aborts with "deep recursion was detected at 'interpreter'".

THE EXPECTED REFUSAL, recorded rather than silenced: the cross-book
transfer prints `[cross-book equisortDev: world NOT included in
sortsEqWorldD — transfer refused]`. That is correct — the equisort
scope's WITNESS defuns do not appear in the consumer's world — and the
`usefi` route is exactly the mechanism that does not need them. -/

-- The SE world carries 215 defuns, so the `by decide` world facts of the
-- native entries below evaluate deeper than the default limit (512).
-- RECURSION-DEPTH sweep 2026-08-19: the three per-capstone
-- `set_option maxRecDepth 1000000 in` raises that used to sit on the
-- `replayed_theorem`s below were DELETED — the module elaborates clean
-- under this file-level 100000 alone (probed 2026-08-19), so they were
-- pure over-provision. The 100000 itself is still an UNPROFILED bound:
-- named residue in the TODO heartbeat/recursion sweep item.
set_option maxRecDepth 100000

private def sortsEqLog : String :=
  include_str "../../../acl2_samples/sorting/sorts-equivalent.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def sortsEqDev : Development :=
  load_development% sortsEqLog

derive_world sortsEqWorldD from sortsEqDev

-- hb guard: measured 14.32M user units vs bound UNLIMITED (0) (2026-08-19 sweep).
-- Needed — over Lean's 200k default. TRIAGE SITE for the next perf/design
-- round: see the TODO heartbeat/recursion sweep item.
set_option maxHeartbeats 0 in
/-- The driver's CONDITIONAL replayed statement for MSORT-IS-ISORT (the
    telescope is EMPTY — the row is unconditional). -/
replayed_theorem msortIsIsortReplayedCond := driver_replayed% sortsEqDev sortsEqWorldD
  "msort-is-isort" with_termination usefi
  deps [permDev, convertPermDev, isortDev, bsortDev, orderedPermsDev,
        equisortDev, msortDev, qsortDev]

/-- The unconditional form. -/
theorem msortIsIsortReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f sortsEqWorldD env
      Worlds.Sorting.msort_is_isortFormula = some v ∧ v ≠ SExpr.nil :=
  msortIsIsortReplayedCond env

/-- ENTRY, PROVED — MSORT-IS-ISORT natively: merge sort and insertion
    sort compute the same list. -/
theorem msort_is_isort_native_driver (xs : List SExpr) :
    Worlds.Sorting.msortL xs = Worlds.Sorting.isortL xs :=
  Worlds.Sorting.msort_is_isort_native_of_replayed sortsEqWorldD
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    msortIsIsortReplayed_uncond xs

#print axioms msort_is_isort_native_driver

-- hb guard: measured 1.9M user units vs bound UNLIMITED (0) (2026-08-19 sweep).
-- Needed — over Lean's 200k default. TRIAGE SITE for the next perf/design
-- round: see the TODO heartbeat/recursion sweep item.
set_option maxHeartbeats 0 in
/-- The driver's CONDITIONAL replayed statement for QSORT-IS-ISORT. -/
replayed_theorem qsortIsIsortReplayedCond := driver_replayed% sortsEqDev sortsEqWorldD
  "qsort-is-isort" with_termination usefi
  deps [permDev, convertPermDev, isortDev, bsortDev, orderedPermsDev,
        equisortDev, msortDev, qsortDev]

/-- The unconditional form. -/
theorem qsortIsIsortReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f sortsEqWorldD env
      Worlds.Sorting.qsort_is_isortFormula = some v ∧ v ≠ SExpr.nil :=
  qsortIsIsortReplayedCond env

/-- ENTRY, PROVED — QSORT-IS-ISORT natively (at the depth-1 reading). -/
theorem qsort_is_isort_native_driver (xs : List SExpr) :
    Worlds.Sorting.qsortOwnL xs = Worlds.Sorting.isortL xs :=
  Worlds.Sorting.qsort_is_isort_native_of_replayed sortsEqWorldD
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    qsortIsIsortReplayed_uncond xs

#print axioms qsort_is_isort_native_driver

/-! ## BSORT-IS-ISORT

The corpus's one CONDITIONAL capstone — the book states it under
`TRUE-LISTP`, and `sorts-equivalent` instantiates the WEAK twin
(`WEAK-SORTFN1-IS-SORTFN2`) for it, not the strong one the other two
use. The decode absorbs the hypothesis in the standing way (every `enc`
image is a true list) via the generic IMPLIES peel.

**Correction to this file's previous record (close-out arc,
2026-08-18).** What stood here said the row was blocked by an ASSUMED
dp-fact and that "the remedy is at the LEAF's emission". Both were
wrong, and the measurement that refutes them is in the close-out
charter's ARC LOG (J-1-1): the `Goal:preprocess/tau` leaf DISCHARGES in
the real replay, by CITING the already-replayed `TRUE-LISTP-BSORT`
through the `:TAU-BASIS` slice the fork has emitted since 2026-08-10.
The `◌ assumed cond[…]` in the golden line quoted here belongs to the
STANDALONE informational DP probe (which has no `ReplayCtx`, hence no
rules to cite, and so can only ever report `◌`); the ROW's own verdict
is `REPLAYED ✓` with no trailing `cond[…]`, i.e. UNCONDITIONAL. The
accurate half of the old record was the SECOND observation — the
`usefi` bridge — which is what this row actually had to cross. -/

-- hb guard: measured 1.72M user units vs bound UNLIMITED (0) (2026-08-19 sweep).
-- Needed — over Lean's 200k default. TRIAGE SITE for the next perf/design
-- round: see the TODO heartbeat/recursion sweep item.
set_option maxHeartbeats 0 in
/-- The driver's CONDITIONAL replayed statement for BSORT-IS-ISORT. -/
replayed_theorem bsortIsIsortReplayedCond := driver_replayed% sortsEqDev sortsEqWorldD
  "bsort-is-isort" with_termination usefi
  deps [permDev, convertPermDev, isortDev, bsortDev, orderedPermsDev,
        equisortDev, msortDev, qsortDev]

/-- The unconditional form. -/
theorem bsortIsIsortReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f sortsEqWorldD env
      Worlds.Sorting.bsort_is_isortFormula = some v ∧ v ≠ SExpr.nil :=
  bsortIsIsortReplayedCond env

/-- ENTRY, PROVED — BSORT-IS-ISORT natively: bubble sort and insertion
    sort compute the same list. -/
theorem bsort_is_isort_native_driver (xs : List SExpr) :
    Worlds.Sorting.bsortL xs = Worlds.Sorting.isortL xs :=
  Worlds.Sorting.bsort_is_isort_native_of_replayed sortsEqWorldD
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    bsortIsIsortReplayed_uncond xs

#print axioms bsort_is_isort_native_driver

end ACL2.Imported.Waypoints
