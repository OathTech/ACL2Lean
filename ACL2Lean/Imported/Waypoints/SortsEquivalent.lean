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
-- native entries below evaluate deeper than the default limit.
set_option maxRecDepth 100000

private def sortsEqLog : String :=
  include_str "../../../acl2_samples/sorting/sorts-equivalent.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def sortsEqDev : Development :=
  load_development% sortsEqLog

derive_world sortsEqWorldD from sortsEqDev

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- The driver's CONDITIONAL replayed statement for MSORT-IS-ISORT (the
    telescope is EMPTY — the row is unconditional). -/
def msortIsIsortReplayedCond := driver_replayed% sortsEqDev sortsEqWorldD
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

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- The driver's CONDITIONAL replayed statement for QSORT-IS-ISORT. -/
def qsortIsIsortReplayedCond := driver_replayed% sortsEqDev sortsEqWorldD
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

/-! ## BSORT-IS-ISORT — NOT BUILT, and the cause is not machinery

Measured this wave, not inferred. The golden's own row says it:

```
BSORT-IS-ISORT → REPLAYED ✓  [DISCHARGE: Goal:preprocess/tau ◌ assumed
  cond[total:(BSORT X), ASSUMED:dp-fact]]
```

The `◌ assumed` marker is an ASSUMED dp-fact — visible `sorryAx`-class
debt the sweep carries and reports. `driver_replayed%` REFUSES to
register a replayed statement carrying `ASSUMED:dp-fact` (the N1
remediation guard, `Waypoints/Macro.lean`: "an ASSUMED:dp-fact condition
states an obligation over independently-quantified opaques that can be
FALSE"). So this row cannot become a waypoint native while its leaf is
assumed, and the remedy is at the LEAF's emission — not here.

The row was additionally observed to fail EARLIER than that guard, on
its own dependency: `usefi bridge: consumer discharge of ORDEREDP-BSORT
failed: depReplayedProofAt: dependency ORDEREDP-BSORT's replay failed
(frontier)`. Both observations are recorded; neither is worked around.

Its DECODE was written and measured to close against a hypothetical
replayed statement, then REVERTED rather than left in the tree as
machinery with no consumer (the J-2d-6 precedent). -/

end ACL2.Imported.Waypoints
