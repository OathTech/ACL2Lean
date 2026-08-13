import ACL2Lean.Imported.Waypoints.Macro
import ACL2Lean.Imported.Waypoints.ConvertPerm
import ACL2Lean.DevLoad

namespace ACL2.Imported.Waypoints

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! ## The isort book — ORDEREDP-ISORT: insertion sort always sorts.
The row's ONE condition (`tp:INSERT`, insert's emitted `(CONSP (INSERT E
X))` corollary) is discharged BY THE DRIVER's own TP prover from that
emitted corollary + ACL2's `:LEAVES` (every emitted return-path leaf is
a `CONS`, verdicted `3072` = `*ts-cons*` — TP-replay arc increment 2,
2026-08-13; the hand-side `dis_insert_tp` it used to consume is
retired), so the replayed statement is UNCONDITIONAL as the driver
emits it; the `insert`/`isort` exec kit decodes it natively. -/

private def isortLog : String :=
  include_str "../../../acl2_samples/sorting/isort.proof-log"


def isortDev : Development :=
  load_development% isortLog

derive_world isortWorldD from isortDev

/-- The driver's replayed statement, now UNCONDITIONAL (its sole
    `tp:INSERT` hypothesis is supplied by the driver's TP prover). -/
def orderedpIsortReplayedCond := driver_replayed% isortDev isortWorldD
  "orderedp-isort"

/-- The unconditional form — nothing left to discharge hand-side. -/
theorem orderedpIsortReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f isortWorldD env
      Worlds.Sorting.orderedp_isortFormula = some v ∧ v ≠ SExpr.nil :=
  orderedpIsortReplayedCond env

/-- ENTRY, PROVED — ORDEREDP-ISORT natively: INSERTION SORT ALWAYS SORTS —
    `isortL` (insertion sort by `lexorderB`) yields an adjacent-pair
    lexorder-sorted list for EVERY input list. -/
theorem orderedp_isort_native_driver (xs : List SExpr) :
    Worlds.Sorting.orderedpRec (Worlds.Sorting.isortL xs) = true :=
  Worlds.Sorting.orderedp_isort_native_of_replayed isortWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) orderedpIsortReplayed_uncond xs

#print axioms orderedp_isort_native_driver

set_option maxHeartbeats 1600000 in
/-- The driver's CONDITIONAL replayed statement for HOW-MANY-ISORT
    (hypotheses: `tp:HOW-MANY`, `rule:FOLD-CONSTS-IN-+`;
    `rule:NOT-MEMB-IMPLIES-HOW-MANY-IS-0` discharged CROSS-BOOK from the
    dependency's replayed tree — 2a). -/
def howManyIsortReplayedCond := driver_replayed% isortDev isortWorldD
  "how-many-isort" deps [convertPermDev]

/-- The unconditional form — both remaining hypotheses discharged
    world-parametrically (the how-many exec kit + the arithmetic rule
    dischargers). -/
theorem howManyIsortReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f isortWorldD env
      Worlds.Sorting.how_many_isortFormula = some v ∧ v ≠ SExpr.nil :=
  howManyIsortReplayedCond env


/-- ENTRY, PROVED — HOW-MANY-ISORT natively: INSERTION SORT PRESERVES
    MULTIPLICITY — `List.count` of every element is unchanged by
    `isortL`. -/
theorem how_many_isort_native_driver (ev : SExpr) (xs : List SExpr) :
    (Worlds.Sorting.isortL xs).count ev = xs.count ev :=
  Worlds.Sorting.how_many_isort_native_of_replayed isortWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) howManyIsortReplayed_uncond ev xs

#print axioms how_many_isort_native_driver

end ACL2.Imported.Waypoints
