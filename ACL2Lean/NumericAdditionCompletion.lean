import ACL2Lean.NumericEquality

namespace ACL2.Logic

/-- The primitive COMPLETION-OF-+ axiom, used by the captured default-rule
proofs. The defaults themselves still require their recorded replay. -/
theorem plus_completion (x y : SExpr) : plus x y =
    (bif toBool (acl2Numberp x) then
      (bif toBool (acl2Numberp y) then plus x y else x)
      else (bif toBool (acl2Numberp y) then y else .atom (.number (.int 0)))) := by
  by_cases hx : acl2Numberp x = .nil <;> by_cases hy : acl2Numberp y = .nil
  · rw [(toBool_eq_false _).mpr hx, (toBool_eq_false _).mpr hy]
    change plus x y = .atom (.number (.int 0))
    rw [plus_parts, numberParts_nonnumber hx, numberParts_nonnumber hy]
    change mkParts (0 + 0) (0 + 0) = .atom (.number (.int 0))
    simpa only [Rat.zero_add] using
      (show mkParts (0 : Rat) 0 = .atom (.number (.int 0)) from rfl)
  · rw [(toBool_eq_false _).mpr hx, (toBool_eq_true _).mpr hy]
    change plus x y = y
    rw [plus_parts, numberParts_nonnumber hx]
    simp only [Rat.zero_add, mkParts_numberParts, fix_of_number y hy]
  · rw [(toBool_eq_true _).mpr hx, (toBool_eq_false _).mpr hy]
    change plus x y = x
    rw [plus_parts, numberParts_nonnumber hy]
    simp only [Rat.add_zero, mkParts_numberParts, fix_of_number x hx]
  · rw [(toBool_eq_true _).mpr hx, (toBool_eq_true _).mpr hy]
    rfl

end ACL2.Logic
