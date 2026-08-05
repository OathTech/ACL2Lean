import ACL2Lean.Imported.Mirrors.Macro
import ACL2Lean.Imported.Mirrors.ConvertPerm

namespace ACL2.Imported.Mirrors

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! ## The bsort book — first tranche: HOW-MANY-BNEXT (the P3 close-gap
build: the bubble pass preserves counts). -/

private def bsortLog : String :=
  include_str "../../../acl2_samples/sorting/bsort.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def bsortDev : Development :=
  (((ProofLog.parse bsortLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world bsortMirrorsWorld from bsortDev

set_option maxHeartbeats 3200000 in
/-- The driver's CONDITIONAL replayed statement for HOW-MANY-BNEXT
    (hypotheses: `total:BNEXT`, `tp:HOW-MANY`; the cross-book
    `rule:NOT-MEMB-IMPLIES-HOW-MANY-IS-0` condition discharges from the
    convert-perm dependency trees — the 2a channel, matching the sweep). -/
def howManyBnextReplayedCond := driver_replayed% bsortDev
  bsortMirrorsWorld "how-many-bnext" deps [convertPermDev]

/-- The unconditional form — bnext's totality from its own corr
    (`dis_bnext_total`), how-many's TP by the standard discharger. -/
theorem howManyBnextReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f bsortMirrorsWorld env
      Worlds.Sorting.how_many_bnextFormula = some v ∧ v ≠ SExpr.nil :=
  howManyBnextReplayedCond env
    (Worlds.Sorting.dis_bnext_total bsortMirrorsWorld (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide))
    (Worlds.Sorting.dis_how_many_tp bsortMirrorsWorld (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide))

/-- ENTRY, PROVED — HOW-MANY-BNEXT natively: the bubble pass preserves
    `List.count` (over the self-contained native pass `bnextL`). -/
theorem how_many_bnext_native_driver (ev : SExpr) (xs : List SExpr) :
    (Worlds.Sorting.bnextL xs).count ev = xs.count ev :=
  Worlds.Sorting.how_many_bnext_native_of_replayed bsortMirrorsWorld
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) howManyBnextReplayed_uncond ev xs

#print axioms how_many_bnext_native_driver

end ACL2.Imported.Mirrors
