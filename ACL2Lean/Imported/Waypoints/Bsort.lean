import ACL2Lean.Imported.Waypoints.Macro
import ACL2Lean.Imported.Waypoints.ConvertPerm
import ACL2Lean.Imported.SortingBsort
import ACL2Lean.DevLoad

namespace ACL2.Imported.Waypoints

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! ## The bsort book — first tranche: HOW-MANY-BNEXT (the P3 close-gap
build: the bubble pass preserves counts). -/

private def bsortLog : String :=
  include_str "../../../acl2_samples/sorting/bsort.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def bsortDev : Development :=
  load_development% bsortLog

derive_world bsortWaypointsWorld from bsortDev

set_option maxHeartbeats 3200000 in
/-- The driver's CONDITIONAL replayed statement for HOW-MANY-BNEXT
    (hypotheses: `total:BNEXT`, `tp:HOW-MANY`; the cross-book
    `rule:NOT-MEMB-IMPLIES-HOW-MANY-IS-0` condition discharges from the
    convert-perm dependency trees — the 2a channel, matching the sweep). -/
def howManyBnextReplayedCond := driver_replayed% bsortDev
  bsortWaypointsWorld "how-many-bnext" deps [convertPermDev]

/-- The unconditional form — bnext's totality now arrives BY REPLAY of
    its emitted `(LEN X)` admission (the R3 measure table, 2026-08-14:
    `dis_bnext_total` is GONE), how-many's TP by the standard
    discharger. -/
theorem howManyBnextReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f bsortWaypointsWorld env
      Worlds.Sorting.how_many_bnextFormula = some v ∧ v ≠ SExpr.nil :=
  howManyBnextReplayedCond env

/-- ENTRY, PROVED — HOW-MANY-BNEXT natively: the bubble pass preserves
    `howManyL` (over the self-contained native pass `bnextL`). -/
theorem how_many_bnext_native_driver (ev : SExpr) (xs : List SExpr) :
    Worlds.Sorting.howManyL ev (Worlds.Sorting.bnextL xs)
      = Worlds.Sorting.howManyL ev xs :=
  Worlds.Sorting.how_many_bnext_native_of_replayed bsortWaypointsWorld
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) howManyBnextReplayed_uncond ev xs

#print axioms how_many_bnext_native_driver

set_option maxHeartbeats 3200000 in
/-- The driver's CONDITIONAL replayed statement for
    ORDEREDP-WHEN-BNEXT-CONSTANT (hypothesis: `total:BNEXT`). -/
def orderedpWhenBnextConstantReplayedCond := driver_replayed% bsortDev
  bsortWaypointsWorld "orderedp-when-bnext-constant"

/-- The unconditional form — bnext's totality by replay (the R3 measure
    table's LEN row; the former debt entry is GONE). -/
theorem orderedpWhenBnextConstantReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f bsortWaypointsWorld env
      Worlds.Sorting.orderedp_when_bnext_constantFormula = some v
        ∧ v ≠ SExpr.nil :=
  orderedpWhenBnextConstantReplayedCond env

/-- ENTRY, PROVED — ORDEREDP-WHEN-BNEXT-CONSTANT natively: a list the
    bubble pass leaves unchanged is sorted (over the native pass `bnextL`
    and the chain2 reading `orderedpRec`). -/
theorem orderedp_when_bnext_constant_native_driver (xs : List SExpr)
    (h : Worlds.Sorting.bnextL xs = xs) :
    Worlds.Sorting.orderedpRec xs = true :=
  Worlds.Sorting.orderedp_when_bnext_constant_native_of_replayed
    bsortWaypointsWorld (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    orderedpWhenBnextConstantReplayed_uncond xs h

#print axioms orderedp_when_bnext_constant_native_driver

set_option maxHeartbeats 3200000 in
/-- The driver's CONDITIONAL replayed statement for HOW-MANY-SMALLER-BNEXT
    (hypotheses: `total:BNEXT`, `tp:HOW-MANY-SMALLER`). -/
def howManySmallerBnextReplayedCond := driver_replayed% bsortDev
  bsortWaypointsWorld "how-many-smaller-bnext"

/-- The unconditional form — bnext's totality and how-many-smaller's TP
    both arrive by replay (the R3 measure table's LEN row; the former debt
    entries are GONE). -/
theorem howManySmallerBnextReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f bsortWaypointsWorld env
      Worlds.Sorting.how_many_smaller_bnextFormula = some v ∧ v ≠ SExpr.nil :=
  howManySmallerBnextReplayedCond env

/-- ENTRY, PROVED — HOW-MANY-SMALLER-BNEXT natively: one bubble pass
    preserves every counts-below (over the native pass `bnextL` and the
    native count `howManySmallerL`). -/
theorem how_many_smaller_bnext_native_driver (ev : SExpr) (xs : List SExpr) :
    Worlds.Sorting.howManySmallerL ev (Worlds.Sorting.bnextL xs)
      = Worlds.Sorting.howManySmallerL ev xs :=
  Worlds.Sorting.how_many_smaller_bnext_native_of_replayed bsortWaypointsWorld
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    howManySmallerBnextReplayed_uncond ev xs

#print axioms how_many_smaller_bnext_native_driver

set_option maxHeartbeats 3200000 in
/-- The driver's CONDITIONAL replayed statement for
    HOW-MANY-BAD-PAIRS-BNEXT (hypothesis: `total:BNEXT`). `tp:BNEXT-SIZE`
    left this telescope with TP-replay arc increment 3 (2026-08-13): the
    CALLEE-TP return path — BNEXT-SIZE's emitted leaf
    `(BINARY-+ (HOW-MANY-SMALLER (CAR X) (CDR X)) (BNEXT-SIZE (CDR X)))`
    now closes with the `BINARY-+` summand's P-fact supplied by
    HOW-MANY-SMALLER's OWN emitted non-negative-integer corollary. -/
def howManyBadPairsBnextReplayedCond := driver_replayed% bsortDev
  bsortWaypointsWorld "how-many-bad-pairs-bnext"

/-- The unconditional form — bnext's totality and the count TPs all
    arrive by replay (the R3 measure table's LEN row). -/
theorem howManyBadPairsBnextReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f bsortWaypointsWorld env
      Worlds.Sorting.how_many_bad_pairs_bnextFormula = some v
        ∧ v ≠ SExpr.nil :=
  howManyBadPairsBnextReplayedCond env

/-- ENTRY, PROVED — HOW-MANY-BAD-PAIRS-BNEXT natively: a bubble pass that
    CHANGES the list strictly decreases the bubble measure (bubble sort's
    well-foundedness, over the native pass and measure). -/
theorem how_many_bad_pairs_bnext_native_driver (xs : List SExpr)
    (h : xs ≠ Worlds.Sorting.bnextL xs) :
    Worlds.Sorting.bnextSizeL (Worlds.Sorting.bnextL xs)
      < Worlds.Sorting.bnextSizeL xs :=
  Worlds.Sorting.how_many_bad_pairs_bnext_native_of_replayed
    bsortWaypointsWorld (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    howManyBadPairsBnextReplayed_uncond xs h

#print axioms how_many_bad_pairs_bnext_native_driver

end ACL2.Imported.Waypoints
