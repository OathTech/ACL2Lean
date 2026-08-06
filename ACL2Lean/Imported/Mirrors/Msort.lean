import ACL2Lean.Imported.Mirrors.Macro
import ACL2Lean.Imported.Mirrors.ConvertPerm
import ACL2Lean.DevLoad

namespace ACL2.Imported.Mirrors

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! ## The msort book — merge sort, all four content rows. -/

private def msortLog : String :=
  include_str "../../../acl2_samples/sorting/msort.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def msortDev : Development :=
  load_development% msortLog

derive_world msortWorldD from msortDev

set_option maxHeartbeats 1600000 in
/-- HOW-MANY-MERGE2's conditional replayed statement. -/
def howManyMerge2ReplayedCond := driver_replayed% msortDev msortWorldD
  "how-many-merge2" deps [convertPermDev]

theorem howManyMerge2Replayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f msortWorldD env
      Worlds.Sorting.how_many_merge2Formula = some v ∧ v ≠ SExpr.nil :=
  howManyMerge2ReplayedCond env
    (Worlds.Sorting.dis_merge2_total msortWorldD (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide))
    (Worlds.Sorting.dis_how_many_tp msortWorldD (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide))
    (Worlds.Sorting.dis_fold_consts msortWorldD (by decide) _ _)


/-- ENTRY, PROVED — HOW-MANY-MERGE2 natively: merging adds
    multiplicities. -/
theorem how_many_merge2_native_driver (ev : SExpr) (xs ys : List SExpr) :
    (Worlds.Sorting.merge2L xs ys).count ev = xs.count ev + ys.count ev :=
  Worlds.Sorting.how_many_merge2_native_of_replayed msortWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) howManyMerge2Replayed_uncond ev xs ys

#print axioms how_many_merge2_native_driver

set_option maxHeartbeats 1600000 in
/-- HOW-MANY-EVENS-AND-ODDS's conditional replayed statement. -/
def howManyEvensOddsReplayedCond := driver_replayed% msortDev msortWorldD
  "how-many-evens-and-odds" deps [convertPermDev]

theorem howManyEvensOddsReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f msortWorldD env
      Worlds.Sorting.how_many_evens_and_oddsFormula = some v ∧
      v ≠ SExpr.nil :=
  howManyEvensOddsReplayedCond env
    (Worlds.Sorting.dis_how_many_tp msortWorldD (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide))
    (Worlds.Sorting.dis_default_car msortWorldD (by decide) (by decide)
      (by decide))
    (Worlds.Sorting.dis_default_cdr msortWorldD (by decide) (by decide)
      (by decide))
    (Worlds.Sorting.dis_fold_consts msortWorldD (by decide) _ _)


/-- ENTRY, PROVED — HOW-MANY-EVENS-AND-ODDS natively: the evens/odds
    split partitions every element's multiplicity. -/
theorem how_many_evens_and_odds_native_driver (ev a : SExpr)
    (t : List SExpr) :
    (Worlds.Sorting.evensL (a :: t)).count ev
      + (Worlds.Sorting.evensL t).count ev = (a :: t).count ev :=
  Worlds.Sorting.how_many_evens_and_odds_native_of_replayed msortWorldD
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) howManyEvensOddsReplayed_uncond
    ev a t

#print axioms how_many_evens_and_odds_native_driver

set_option maxHeartbeats 1600000 in
/-- ORDEREDP-MSORT's conditional replayed statement. -/
def orderedpMsortReplayedCond := driver_replayed% msortDev msortWorldD
  "orderedp-msort"

theorem orderedpMsortReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f msortWorldD env
      Worlds.Sorting.orderedp_msortFormula = some v ∧ v ≠ SExpr.nil :=
  orderedpMsortReplayedCond env
    (Worlds.Sorting.dis_merge2_total msortWorldD (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide))
    (Worlds.Sorting.dis_msort_total msortWorldD (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
    (Worlds.Sorting.dis_evens_tp msortWorldD (by decide) (by decide)
      (by decide) (by decide) (by decide))

/-- ENTRY, PROVED — ORDEREDP-MSORT natively: MERGE SORT ALWAYS SORTS —
    `msortL` yields an adjacent-pair lexorder-sorted list for EVERY
    input. -/
theorem orderedp_msort_native_driver (xs : List SExpr) :
    Worlds.Sorting.orderedpRec (Worlds.Sorting.msortL xs) = true :=
  Worlds.Sorting.orderedp_msort_native_of_replayed msortWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) orderedpMsortReplayed_uncond xs

#print axioms orderedp_msort_native_driver

set_option maxHeartbeats 1600000 in
/-- HOW-MANY-MSORT's conditional replayed statement. -/
def howManyMsortReplayedCond := driver_replayed% msortDev msortWorldD
  "how-many-msort" deps [convertPermDev]

theorem howManyMsortReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f msortWorldD env
      Worlds.Sorting.how_many_msortFormula = some v ∧ v ≠ SExpr.nil :=
  howManyMsortReplayedCond env
    (Worlds.Sorting.dis_merge2_total msortWorldD (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide))
    (Worlds.Sorting.dis_msort_total msortWorldD (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
    (Worlds.Sorting.dis_how_many_tp msortWorldD (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide))
    (Worlds.Sorting.dis_default_car msortWorldD (by decide) (by decide)
      (by decide))
    (Worlds.Sorting.dis_default_cdr msortWorldD (by decide) (by decide)
      (by decide))
    (Worlds.Sorting.dis_fold_consts msortWorldD (by decide) _ _)


/-- ENTRY, PROVED — HOW-MANY-MSORT natively: MERGE SORT PRESERVES
    MULTIPLICITY. -/
theorem how_many_msort_native_driver (ev : SExpr) (xs : List SExpr) :
    (Worlds.Sorting.msortL xs).count ev = xs.count ev :=
  Worlds.Sorting.how_many_msort_native_of_replayed msortWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    howManyMsortReplayed_uncond ev xs

#print axioms how_many_msort_native_driver

/-- ORDEREDP-MSORT, Mathlib form. -/
theorem orderedp_msort_isChain_driver (xs : List SExpr) :
    (Worlds.Sorting.msortL xs).IsChain
      (fun a b => Worlds.Sorting.lexorderB a b = true) :=
  (Worlds.Sorting.chain2Rec_iff_isChain _ _).mp
    (orderedp_msort_native_driver xs)

end ACL2.Imported.Mirrors
