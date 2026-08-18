import ACL2Lean.Imported.Waypoints.Macro
import ACL2Lean.Imported.Linear
import ACL2Lean.DevLoad

namespace ACL2.Imported.Waypoints

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! ## The 03-linear book — LEN2-NONNEG and LEN2-CDR-SMALLER

The first COMPARISON-concluded waypoints: every prior entry ends at
`Lifting.native_of_replayed_equal`, and these two end at the new `≤` / `<`
enders (`Imported/LiftingRel.lean`). No simulation work was needed —
`LEN2`'s emitted body IS `Lifting.lenBody "LEN2"`, so the name-generic
length correspondence instantiates here by `decide`.

The catalog's long-standing `.pending "len2 dischargers"` reason is
retired as STALE (the 02-rev pattern, R0 item 7): both rows' `cond[…]`
labels sit inside `[DISCHARGE: …]` on the informational DP probe, and the
driver emits both replayed statements UNCONDITIONAL — the `_uncond`
theorems below are the proof of that, since a surviving hypothesis would
not typecheck. -/

private def linearLog : String :=
  include_str "../../../acl2_samples/recon-tests/03-linear.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def linearDev : Development :=
  load_development% linearLog

derive_world linearWorldD from linearDev

/-- The driver's replayed statement for LEN2-NONNEG (the proof OBJECT). -/
def len2NonnegReplayedCond := driver_replayed% linearDev linearWorldD
  "len2-nonneg"

/-- The driver replayed statement — UNCONDITIONAL, STATEMENT-PINNED to
    the hand `len2_nonnegFormula` (the log's root Goal clause:
    `(NOT (< (LEN2 X) '0))` — ACL2's macroexpansion of `(<= 0 (LEN2 X))`). -/
theorem len2NonnegReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f linearWorldD env
      Worlds.Linear.len2_nonnegFormula = some v ∧ v ≠ SExpr.nil :=
  len2NonnegReplayedCond env

/-- ENTRY, PROVED — a length is never negative, through the DRIVER's
    replayed statement, decoded by the `≤` ender. -/
theorem len2_nonneg_native_driver (xs : List SExpr) :
    (0 : Int) ≤ (xs.length : Int) :=
  Worlds.Linear.len2_nonneg_native_of_replayed linearWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    len2NonnegReplayed_uncond xs

#print axioms len2_nonneg_native_driver

/-- The driver's replayed statement for LEN2-CDR-SMALLER (the proof
    OBJECT). -/
def len2CdrSmallerReplayedCond := driver_replayed% linearDev linearWorldD
  "len2-cdr-smaller"

/-- The driver replayed statement — UNCONDITIONAL, STATEMENT-PINNED to
    the hand `len2_cdr_smallerFormula` (the log's root Goal clause:
    `(IMPLIES (CONSP X) (< (LEN2 (CDR X)) (LEN2 X)))`). -/
theorem len2CdrSmallerReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f linearWorldD env
      Worlds.Linear.len2_cdr_smallerFormula = some v ∧ v ≠ SExpr.nil :=
  len2CdrSmallerReplayedCond env

/-- ENTRY, PROVED — a proper tail is strictly shorter, through the
    DRIVER's replayed statement, decoded by the conditional `<` ender with
    the `(CONSP X)` antecedent discharged at the encoded instance. -/
theorem len2_cdr_smaller_native_driver (a : SExpr) (t : List SExpr) :
    (t.length : Int) < ((a :: t).length : Int) :=
  Worlds.Linear.len2_cdr_smaller_native_of_replayed linearWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    len2CdrSmallerReplayed_uncond a t

#print axioms len2_cdr_smaller_native_driver

end ACL2.Imported.Waypoints
