/-
  SPIKE (2026-06-09): can a Lean-core decision procedure (omega) discharge the
  NATIVE LIFT of a tau-system black-box leaf, kernel-clean?

  Target leaf: 07-mutual-recursion's termination tip, Subgoal 1':
      {(zp n) ∨ (< (binary-+ '-1 n) n)}
  closed by ACL2's tau (executable-counterpart:tau-system) via zp's
  compound-recognizer + interval arithmetic — no internal step record exists.

  The lift: the clause (a disjunction over ALL SExpr values of n, with ACL2's
  defaulting semantics in the Logic primitives) is true. Stated as: if the first
  literal is false (zp n = nil), the second evaluates to t.

  This spike is evidence for the "emit top-level tau node + discharge by a
  kernel-checked decision procedure" design (Option 2 in
  docs/plans/2026-06-09_direct-proof-emission.md). It is NOT yet wired to the
  driver; the driver integration (mechanized lift from the emitted clause +
  emitted type facts) is the follow-up if the design is adopted.
-/
import ACL2Lean.Logic

namespace ACL2.Tests.SpikeTauOmega

open ACL2 Logic

private def negOne : SExpr := .atom (.number (.int (-1)))

/-- The lifted tau-leaf obligation: `(zp n) = nil → (< (+ -1 n) n) = t`,
    over ALL SExpr `n` (ACL2 defaulting semantics included). -/
theorem tau_leaf_07_subgoal_1'
    (n : SExpr) (h : zp n = SExpr.nil) :
    lt (plus negOne n) n = SExpr.t := by
  -- zp n = nil forces n to be an integer atom with value > 0
  -- (toInt defaults every non-integer to 0, which zp sends to t).
  match n with
  | .atom (.number (.int k)) =>
    simp only [zp, toInt] at h
    split at h
    · exact absurd h (by simp [SExpr.t])
    · rename_i hk
      -- k > 0; now (+ -1 k) = k-1 as an int atom, and k-1 < k by omega.
      simp [plus, toRat, negOne, mkNumber, lt]
      omega
  | .atom (.number (.rational a b)) => simp [zp, toInt] at h
  | .atom (.number (.decimal m e)) => simp [zp, toInt] at h
  | .atom (.symbol s) => simp [zp, toInt] at h
  | .atom (.keyword k) => simp [zp, toInt] at h
  | .atom (.string s) => simp [zp, toInt] at h
  | .nil => simp [zp, toInt] at h
  | .cons a b => simp [zp, toInt] at h

/-- info: 'ACL2.Tests.SpikeTauOmega.tau_leaf_07_subgoal_1'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tau_leaf_07_subgoal_1'

end ACL2.Tests.SpikeTauOmega
