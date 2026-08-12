import ACL2Lean.Imported.Waypoints.Macro
import ACL2Lean.DevLoad

namespace ACL2.Imported.Waypoints

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! ## Entry 9 — `perm-cons` (the sorting corpus, R1):
`a ∈ xs → (xs ~ a :: ys ↔ xs.erase a ~ ys)`

The FULL chain on the perm book's first replayed theorem: the REAL
`sorting/perm.proof-log` → parse → reconstruct → the log-DERIVED world → the
driver's replayed statement (the branch-split composer, destructor elimination, the
whole R1 node family) — UNCONDITIONAL: all totality auto-discharged from
admission data and all TP corollaries by the TP prover (`proveTp`), both
landed in the 2026-07-06 lifter sprint — → the `contains`/`erase`/`isPerm`
simulations → the native statement over `List.Perm`. The hand dischargers
in `Imported/Perm.lean` remain as the provers' validated models. -/

private def permLog9 : String := include_str "../../../acl2_samples/sorting/perm.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def permDev : Development :=
  load_development% permLog9

derive_world permWorldD from permDev

/-- The driver's replayed-statement proof OBJECT — UNCONDITIONAL as produced (totality
    by the admission prover, TP corollaries by the TP prover): no
    hypotheses left to discharge. -/
def permConsReplayedCond := driver_replayed% permDev permWorldD "perm-cons"

theorem permConsReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f permWorldD env
      Worlds.Perm.perm_consFormula = some v ∧ v ≠ SExpr.nil :=
  permConsReplayedCond env

/-- ENTRY 9, PROVED — the Boolean form through the DRIVER's replayed statement. -/
theorem perm_cons_native_driver (a : SExpr) (xs ys : List SExpr)
    (h : xs.contains a = true) :
    xs.isPerm (a :: ys) = (xs.erase a).isPerm ys :=
  Worlds.Perm.perm_cons_native_of_replayed permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) permConsReplayed_uncond a xs ys h

/-- ENTRY 9, PROVED — the idiomatic `List.Perm` form: a member moves across
    the permutation relation. -/
theorem perm_cons_native_perm_driver (a : SExpr) (xs ys : List SExpr)
    (h : a ∈ xs) :
    xs.Perm (a :: ys) ↔ (xs.erase a).Perm ys :=
  Worlds.Perm.perm_cons_native_perm_of_replayed permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) permConsReplayed_uncond a xs ys h

#print axioms perm_cons_native_perm_driver

/-! ## Entries 10–16 — the REST of the perm book (lifter sprint 2026-07-06)

Every remaining theorem's UNCONDITIONAL driver replayed statement, decoded natively
through the same `corr_*` layer with the Lifting decode kit. The whole ACL2
book is now imported: 8 replayed statements, 8 native facts, zero hypotheses. -/

def permSymmetricReplayed := driver_replayed% permDev permWorldD "perm-symmetric"
def membRmReplayed := driver_replayed% permDev permWorldD "memb-rm"
def permMembReplayed := driver_replayed% permDev permWorldD "perm-memb"
def commRmReplayed := driver_replayed% permDev permWorldD "comm-rm"
def permRmReplayed := driver_replayed% permDev permWorldD "perm-rm"
def permTransitiveReplayed := driver_replayed% permDev permWorldD "perm-transitive"
def permEquivReplayed := driver_replayed% permDev permWorldD "perm-is-an-equivalence"

/-- ENTRY 10, PROVED — perm-symmetric: `isPerm` is symmetric. -/
theorem perm_symmetric_native_driver (xs ys : List SExpr)
    (h : xs.isPerm ys = true) : ys.isPerm xs = true :=
  Worlds.Perm.perm_symmetric_native_of_replayed permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) permSymmetricReplayed xs ys h

/-- ENTRY 11, PROVED — memb-rm: membership survives erasing another element. -/
theorem memb_rm_native_driver (av bv : SExpr) (xs : List SExpr)
    (h : (xs.erase bv).contains av = true) : xs.contains av = true :=
  Worlds.Perm.memb_rm_native_of_replayed permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    membRmReplayed av bv xs h

/-- ENTRY 12, PROVED — comm-rm: erasures commute (the Mathlib
    `List.erase_comm` fact, imported from ACL2). -/
theorem comm_rm_native_driver (av bv : SExpr) (xs : List SExpr) :
    (xs.erase bv).erase av = (xs.erase av).erase bv :=
  Worlds.Perm.comm_rm_native_of_replayed permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) commRmReplayed av bv xs

/-- ENTRY 13, PROVED — perm-memb: membership transports across `isPerm`. -/
theorem perm_memb_native_driver (av : SExpr) (xs ys : List SExpr)
    (hp : xs.isPerm ys = true) (hm : xs.contains av = true) :
    ys.contains av = true :=
  Worlds.Perm.perm_memb_native_of_replayed permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) permMembReplayed av xs ys hp hm

/-- ENTRY 14, PROVED — perm-rm: `isPerm` is preserved by erasing the same
    element from both sides. -/
theorem perm_rm_native_driver (av : SExpr) (xs ys : List SExpr)
    (hp : xs.isPerm ys = true) :
    (xs.erase av).isPerm (ys.erase av) = true :=
  Worlds.Perm.perm_rm_native_of_replayed permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) permRmReplayed av xs ys hp

/-- ENTRY 15, PROVED — perm-transitive: `isPerm` is transitive. -/
theorem perm_transitive_native_driver (xs ys zs : List SExpr)
    (hxy : xs.isPerm ys = true) (hyz : ys.isPerm zs = true) :
    xs.isPerm zs = true :=
  Worlds.Perm.perm_transitive_native_of_replayed permWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) permTransitiveReplayed xs ys zs hxy hyz

/-- ENTRY 16, PROVED — perm-is-an-equivalence: reflexivity (the conjunct
    with no standalone theorem), decoded by peeling the defequiv tower. -/
theorem perm_refl_native_driver (xs : List SExpr) : xs.isPerm xs = true :=
  Worlds.Perm.perm_refl_native_of_replayed permWorldD (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) permEquivReplayed xs

/-- The BUNDLE — ACL2's defequiv, in Lean's own terms: `isPerm` is an
    equivalence relation, assembled from entries 10/15/16. -/
theorem isPerm_equivalence_driver :
    Equivalence (fun xs ys : List SExpr => xs.isPerm ys = true) where
  refl := perm_refl_native_driver
  symm := fun h => perm_symmetric_native_driver _ _ h
  trans := fun h1 h2 => perm_transitive_native_driver _ _ _ h1 h2

/-- The idiomatic `List.Perm` corollaries. -/
theorem perm_symm_perm_driver {xs ys : List SExpr} (h : xs.Perm ys) :
    ys.Perm xs :=
  List.isPerm_iff.mp
    (perm_symmetric_native_driver xs ys (List.isPerm_iff.mpr h))

theorem perm_trans_perm_driver {xs ys zs : List SExpr}
    (h1 : xs.Perm ys) (h2 : ys.Perm zs) : xs.Perm zs :=
  List.isPerm_iff.mp (perm_transitive_native_driver xs ys zs
    (List.isPerm_iff.mpr h1) (List.isPerm_iff.mpr h2))

theorem perm_erase_perm_driver (av : SExpr) {xs ys : List SExpr}
    (h : xs.Perm ys) : (xs.erase av).Perm (ys.erase av) :=
  List.isPerm_iff.mp
    (perm_rm_native_driver av xs ys (List.isPerm_iff.mpr h))

theorem mem_transport_perm_driver {av : SExpr} {xs ys : List SExpr}
    (h : xs.Perm ys) (hm : av ∈ xs) : av ∈ ys := by
  have := perm_memb_native_driver av xs ys (List.isPerm_iff.mpr h)
    (by simpa [List.contains_iff_mem] using hm)
  simpa [List.contains_iff_mem] using this

#print axioms isPerm_equivalence_driver
#print axioms comm_rm_native_driver
#print axioms perm_erase_perm_driver

end ACL2.Imported.Waypoints
