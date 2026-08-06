import ACL2Lean.Imported.Mirrors.Macro
import ACL2Lean.DevLoad

namespace ACL2.Imported.Mirrors

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! ## Entry 17 — true-listp-flatten (J8, induction-generality arc exit)

From the REAL `recon-tests/10-tree-induction.proof-log`: the arc's first
WF-induction theorem, replayed UNCONDITIONALLY by the driver (its
`rule:TRUE-LISTP-APP` dependency discharged through the D1 registry from the
dependency's own replayed statement). The native decode: **the imported FLATTEN
program, run on ANY input, converges to the encoding of a genuine Lean
`List`** — `true-listp`-ness decoded through the `enc` isomorphism
(`exists_enc_of_trueListp`). For a recognizer theorem the subject IS the
imported program, so `evalOpt` remains in the statement: a fully native
restatement would need a simulation that subsumes — and so bypasses — the
replayed theorem. The OUTER recognizer needs no simulation at all:
`TRUE-LISTP` is absent from the derived world (gz snapshots live in
`gzDefs`, not `w.defs`), so it dispatches to the trusted-core builtin
(`Logic.trueListp`) directly; FLATTEN itself is untouched — its list-ness
comes entirely from ACL2's replayed induction. -/

private def treeLog : String :=
  include_str "../../../acl2_samples/recon-tests/10-tree-induction.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def treeDev : Development :=
  load_development% treeLog

derive_world treeWorldD from treeDev

/-- The UNCONDITIONAL driver replayed statement (zero hypotheses — see the coverage row
    `TRUE-LISTP-FLATTEN → REPLAYED ✓`). -/
def trueListpFlattenReplayed := driver_replayed% treeDev treeWorldD "true-listp-flatten"

private def flattenXT : SExpr := Lifting.app1 "FLATTEN" (.atom (.symbol { name := "X" }))

/-- ENTRY 17, PROVED — FLATTEN's value is always an encoded Lean list. -/
theorem true_listp_flatten_native_driver (env : Env) :
    ∃ (N : Nat) (l : List SExpr), ∀ f ≥ N,
      evalOpt f treeWorldD env flattenXT = some (enc l) := by
  -- the replayed statement: (TRUE-LISTP (FLATTEN X)) is eventually truthy
  obtain ⟨N₀, hN₀⟩ := trueListpFlattenReplayed env
  -- fix the composite's value across fuels
  obtain ⟨N₁, vTL, hTL⟩ := ACL2.Replay.conv_fix
    ⟨N₀, fun f hf => ⟨(hN₀ f hf).choose, (hN₀ f hf).choose_spec.1⟩⟩
  have hvTLne : vTL ≠ SExpr.nil := by
    obtain ⟨v, hv, hne⟩ := hN₀ (max N₀ N₁) (le_max_left _ _)
    rw [hTL (max N₀ N₁) (le_max_right _ _)] at hv
    exact (Option.some.inj hv) ▸ hne
  -- invert: the argument (FLATTEN X) converges, to a fixed value
  obtain ⟨N₂, vF, hF⟩ := ACL2.Replay.conv_fix
    (ACL2.Replay.conv_arg1_of_conv_app treeWorldD env
      { name := "TRUE-LISTP" } flattenXT vTL (by decide) ⟨N₁, hTL⟩)
  -- builtin dispatch: TRUE-LISTP is not in the world, so the composite
  -- computes the trusted-core Logic.trueListp on FLATTEN's value
  obtain ⟨N₃, hC⟩ := ACL2.Replay.conv_builtin1 treeWorldD env
    { name := "TRUE-LISTP" } flattenXT vF (Logic.trueListp vF)
    (by decide) (by decide) ⟨N₂, hF⟩ (ACL2.Replay.callBuiltin_true_listp _)
  -- determinism: the composite's value IS Logic.trueListp vF
  have hEq : vTL = Logic.trueListp vF := by
    have h1 := hTL (max N₁ N₃) (le_max_left _ _)
    have h2 := hC (max N₁ N₃) (le_max_right _ _)
    exact Option.some.inj (h1.symm.trans h2)
  -- decode through the enc isomorphism
  have hT : Logic.trueListp vF = SExpr.t :=
    ACL2.Replay.logic_trueListp_ne_nil_t vF (hEq ▸ hvTLne)
  obtain ⟨l, hl⟩ := Lifting.exists_enc_of_trueListp hT
  exact ⟨N₂, l, fun f hf => by rw [hF f hf, hl]⟩

#print axioms true_listp_flatten_native_driver

end ACL2.Imported.Mirrors
