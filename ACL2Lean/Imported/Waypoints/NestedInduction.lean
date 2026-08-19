import ACL2Lean.Imported.Waypoints.Macro
import ACL2Lean.Imported.NestedInduction
import ACL2Lean.DevLoad

namespace ACL2.Imported.Waypoints

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! ## The 15-nested-induction book — NESTED-INDUCTION

The first CONJUNCTIVE waypoint. The row has been green and unconditional
for a long time; what blocked it was that every ender in the decode
family took an `(EQUAL …)`-headed replayed statement, and this theorem's
is the macroexpanded `AND` — `(IF (EQUAL …) (EQUAL …) 'NIL)`. The split
happens once, at the seam, in
`Lifting.native_of_replayed_and`. -/

private def nestedLog : String :=
  include_str "../../../acl2_samples/recon-tests/15-nested-induction.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def nestedDev : Development :=
  load_development% nestedLog

derive_world nestedWorldD from nestedDev

/-- The driver's replayed statement for NESTED-INDUCTION (the proof
    OBJECT) — the row whose tree carries TWO inductions under a
    synthesized `*1.k` pool root. -/
replayed_theorem nestedInductionReplayedCond := driver_replayed% nestedDev nestedWorldD
  "nested-induction"

/-- The driver replayed statement — UNCONDITIONAL, STATEMENT-PINNED to
    the hand `nested_inductionFormula` (the log's root Goal clause). -/
theorem nestedInductionReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f nestedWorldD env
      Worlds.Nested.nested_inductionFormula = some v ∧ v ≠ SExpr.nil :=
  nestedInductionReplayedCond env

/-- ENTRY, PROVED — BOTH conjuncts natively through the DRIVER's replayed
    statement: append adds lengths, and `dupL` (the aligned reading of
    `DUP`) doubles them. -/
theorem nested_induction_native_driver (xs ys zs : List SExpr) :
    (((xs ++ ys).length : Int) = (xs.length : Int) + (ys.length : Int)) ∧
    (((Worlds.Nested.dupL zs).length : Int)
      = (zs.length : Int) + (zs.length : Int)) :=
  Worlds.Nested.nested_induction_native_of_replayed nestedWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) nestedInductionReplayed_uncond xs ys zs

#print axioms nested_induction_native_driver

end ACL2.Imported.Waypoints
