import ACL2Lean.Imported.SortingBsortKit

namespace ACL2.Imported.Waypoints

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! ## The bsort book — the CAPSTONE rows (R4 wave 2g)

ORDEREDP-BSORT and HOW-MANY-BSORT: what the bsort book proves about its
own top-level function. They live here rather than in `Waypoints/Bsort.
lean` because their decodes need the BSORT exec kit, and that kit's
termination proof is a theorem `Waypoints/Bsort.lean` replays — see
`Imported/SortingBsortKit.lean`'s header for why this one book inverts
the usual layering.

Both rows replay UNCONDITIONALLY (the golden's `sorting/bsort` section
carries them with no `cond[…]`); `with_termination` supplies BSORT's own
admission, which takes the RECORDED route because its measure is a world
function (the measure table's `userFn` row). -/

-- hb guard (2026-08-19 sweep): measured 133k units, bound 3.2M — 24x margin
set_option maxHeartbeats 3200000 in
/-- The driver's CONDITIONAL replayed statement for ORDEREDP-BSORT. -/
replayed_theorem orderedpBsortReplayedCond := driver_replayed% bsortDev
  bsortWaypointsWorld "orderedp-bsort" with_termination

/-- The unconditional form. -/
theorem orderedpBsortReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f bsortWaypointsWorld env
      Worlds.Sorting.orderedp_bsortFormula = some v ∧ v ≠ SExpr.nil :=
  orderedpBsortReplayedCond env

/-- ENTRY, PROVED — ORDEREDP-BSORT natively: BUBBLE SORT SORTS (over the
    native fixed-point recursion `bsortL` and the chain2 reading
    `orderedpRec`). -/
theorem orderedp_bsort_native_driver (xs : List SExpr) :
    Worlds.Sorting.orderedpRec (Worlds.Sorting.bsortL xs) = true :=
  Worlds.Sorting.orderedp_bsort_native_of_replayed bsortWaypointsWorld
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) orderedpBsortReplayed_uncond xs

#print axioms orderedp_bsort_native_driver

-- hb guard (2026-08-19 sweep): measured 11k units, bound 3.2M — 290x margin
set_option maxHeartbeats 3200000 in
/-- The driver's CONDITIONAL replayed statement for HOW-MANY-BSORT. -/
replayed_theorem howManyBsortReplayedCond := driver_replayed% bsortDev
  bsortWaypointsWorld "how-many-bsort" with_termination

/-- The unconditional form. -/
theorem howManyBsortReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f bsortWaypointsWorld env
      Worlds.Sorting.how_many_bsortFormula = some v ∧ v ≠ SExpr.nil :=
  howManyBsortReplayedCond env

/-- ENTRY, PROVED — HOW-MANY-BSORT natively: BUBBLE SORT PRESERVES
    MULTIPLICITY. -/
theorem how_many_bsort_native_driver (ev : SExpr) (xs : List SExpr) :
    Worlds.Sorting.howManyL ev (Worlds.Sorting.bsortL xs)
      = Worlds.Sorting.howManyL ev xs :=
  Worlds.Sorting.how_many_bsort_native_of_replayed bsortWaypointsWorld
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    howManyBsortReplayed_uncond ev xs

#print axioms how_many_bsort_native_driver

end ACL2.Imported.Waypoints
