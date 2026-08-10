/-
  Replay/ClausifyBridgeCons — the CONS-CONS clausify-expansion registry
  identity (equal-descent restructure arc; module-size norm split from
  ClausifyBridge).
-/
import ACL2Lean.Replay.ClausifyBridge

namespace ACL2.Replay

open ACL2

/-- The CONS-CONS specialization of the decomposition (the ground-zero
    CONS-EQUAL rewrite's shape): both sides are conses, so the CONSP guard
    and the CAR/CDR projections evaluate away. -/
private theorem equal_cons_cons_decomp (x1 y1 x2 y2 : SExpr) :
    Logic.equal (SExpr.cons x1 y1) (SExpr.cons x2 y2)
      = cond (Logic.toBool (Logic.equal x1 x2)) (Logic.equal y1 y2)
          SExpr.nil := by
  by_cases hx : x1 = x2
  · subst hx
    by_cases hy : y1 = y2
    · subst hy; simp [Logic.equal]
    · have hc : SExpr.cons x1 y1 ≠ SExpr.cons x1 y2 := by
        intro h; injection h with _ h2; exact hy h2
      simp [Logic.equal, beq_eq_false_iff_ne.mpr hy,
            beq_eq_false_iff_ne.mpr hc]
  · have hc : SExpr.cons x1 y1 ≠ SExpr.cons x2 y2 := by
      intro h; injection h with h1 _; exact hx h1
    simp [Logic.equal, beq_eq_false_iff_ne.mpr hx,
          beq_eq_false_iff_ne.mpr hc]

/-- `(EQUAL (CONS x1 y1) (CONS x2 y2)) ⇒
    (IF (EQUAL x1 x2) (EQUAL y1 y2) 'NIL)`: the CONS-CONS expansion
    preserves the lift — the ground-zero `(:REWRITE CONS-EQUAL)` fired as
    a clausify expansion (equal-descent restructure arc,
    ORDEREDP-WHEN-BNEXT-CONSTANT Subgoal *1/4.2'; the driver validates
    the target shape verbatim and the record cites the rune). -/
theorem dpLiftF_equal_cons_cons_expand {vars : List (Symbol × SExpr)}
    {opq : List (SExpr × SExpr)} (hwf : dpOpqWF opq = true)
    (x1 y1 x2 y2 : SExpr) :
    dpLiftF vars opq (equalAppCB (consAppCB x1 y1) (consAppCB x2 y2))
      = dpLiftF vars opq
          (ifT (equalAppCB x1 x2) (equalAppCB y1 y2) quoteNil) := by
  have hqn : dpLiftF vars opq quoteNil = some SExpr.nil := dpLiftF_quote hwf _
  have hEo := dpLiftF_prim2 (vars := vars) hwf "EQUAL" (consAppCB x1 y1)
    (consAppCB x2 y2) (by decide) (by decide) (by decide) (by decide)
  have hC1 := dpLiftF_prim2 (vars := vars) hwf "CONS" x1 y1
    (by decide) (by decide) (by decide) (by decide)
  have hC2 := dpLiftF_prim2 (vars := vars) hwf "CONS" x2 y2
    (by decide) (by decide) (by decide) (by decide)
  have hEx := dpLiftF_prim2 (vars := vars) hwf "EQUAL" x1 x2
    (by decide) (by decide) (by decide) (by decide)
  have hEy := dpLiftF_prim2 (vars := vars) hwf "EQUAL" y1 y2
    (by decide) (by decide) (by decide) (by decide)
  have hIf := dpLiftF_ifT (vars := vars) (opq := opq) hwf
    (equalAppCB x1 x2) (equalAppCB y1 y2) quoteNil
  have hCB1 : ∀ a b : SExpr, callBuiltin "CONS" [a, b]
      = some (SExpr.cons a b) := fun _ _ => rfl
  have hCB5 : ∀ a b : SExpr, callBuiltin "EQUAL" [a, b]
      = some (Logic.equal a b) := fun _ _ => rfl
  simp only [hIf, hEo, hC1, hC2, hEx, hEy, hqn, hCB1, hCB5]
  cases hx1 : dpLiftF vars opq x1 <;> cases hy1 : dpLiftF vars opq y1 <;>
    cases hx2 : dpLiftF vars opq x2 <;> cases hy2 : dpLiftF vars opq y2 <;>
      simp only [Option.bind, equal_cons_cons_decomp]

end ACL2.Replay
