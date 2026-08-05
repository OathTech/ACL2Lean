import ACL2Lean.Imported.Mirrors.Macro

namespace ACL2.Imported.Mirrors

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-- The parsed development — the ONLY input is the log. -/
private def convertPermLog : String :=
  include_str "../../../acl2_samples/sorting/convert-perm-to-how-many.proof-log"

/-- The convert-perm-to-how-many DEPENDENCY development (2a): its theorem
    trees are offered via `deps [convertPermDev]` so consumer rows'
    included `rule:` hypotheses (NOT-MEMB-IMPLIES-HOW-MANY-IS-0 today)
    discharge by replaying the dependency's tree at the CONSUMER's world —
    no `derive_world`: the dev is a tree source only. -/
def convertPermDev : Development :=
  (((ProofLog.parse convertPermLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

/-! ## The convert-perm book's own mirrors (Phase 7 of the close-out arc) -/

derive_world convertPermWorldD from convertPermDev

set_option maxHeartbeats 1600000 in
/-- The driver's CONDITIONAL replayed statement for
    NOT-MEMB-IMPLIES-HOW-MANY-IS-0 (hypothesis: `tp:HOW-MANY`). -/
def notMembHowMany0ReplayedCond := driver_replayed% convertPermDev
  convertPermWorldD "not-memb-implies-how-many-is-0"

/-- The unconditional form (the `tp:HOW-MANY` hypothesis discharged by the
    standard nonneg-int TP discharger at this world). -/
theorem notMembHowMany0Replayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f convertPermWorldD env
      Worlds.Sorting.not_memb_how_many_0Formula = some v ∧ v ≠ SExpr.nil :=
  notMembHowMany0ReplayedCond env
    (Worlds.Sorting.dis_how_many_tp convertPermWorldD (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide))

/-- ENTRY, PROVED — NOT-MEMB-IMPLIES-HOW-MANY-IS-0 natively: an absent
    element has `List.count` zero (the `List.count_eq_zero` class). -/
theorem not_memb_how_many_0_native_driver (av : SExpr) (xs : List SExpr)
    (h : xs.contains av = false) :
    xs.count av = 0 :=
  Worlds.Sorting.not_memb_how_many_0_native_of_replayed convertPermWorldD
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) notMembHowMany0Replayed_uncond
    av xs h

#print axioms not_memb_how_many_0_native_driver

set_option maxHeartbeats 1600000 in
/-- The driver's CONDITIONAL replayed statement for
    NOT-MEMB-IMPLIES-RM-IS-NO-OP (hypothesis: `rule:CONS-CAR-CDR`). -/
def notMembRmNoopReplayedCond := driver_replayed% convertPermDev
  convertPermWorldD "not-memb-implies-rm-is-no-op"

/-- The unconditional form (the ground-zero rule discharged
    world-parametrically). -/
theorem notMembRmNoopReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f convertPermWorldD env
      Worlds.Sorting.not_memb_rm_noopFormula = some v ∧ v ≠ SExpr.nil :=
  notMembRmNoopReplayedCond env
    (Worlds.Sorting.dis_cons_car_cdr convertPermWorldD (by decide)
      (by decide) (by decide) (by decide))

/-- ENTRY, PROVED — NOT-MEMB-IMPLIES-RM-IS-NO-OP natively: erasing an
    absent element is the identity (the `List.erase_of_not_mem` class). -/
theorem not_memb_rm_noop_native_driver (av : SExpr) (xs : List SExpr)
    (h : xs.contains av = false) :
    xs.erase av = xs :=
  Worlds.Sorting.not_memb_rm_noop_native_of_replayed convertPermWorldD
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    notMembRmNoopReplayed_uncond av xs h

#print axioms not_memb_rm_noop_native_driver

end ACL2.Imported.Mirrors
