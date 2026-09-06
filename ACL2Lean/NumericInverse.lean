import ACL2Lean.NumericEquality
import ACL2Lean.NumericMultiplication
import ACL2Lean.NumericReciprocal
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ACL2.Logic

/-- Primitive reciprocal and inverse equations on the full canonical numeric
domain. Used at actual INVERSE-OF-* nodes in the reciprocal dependency chain. -/
theorem reciprocal_parts (v : SExpr) :
    reciprocal v = mkParts
      ((numberParts v).1 / ((numberParts v).1 * (numberParts v).1 +
        (numberParts v).2 * (numberParts v).2))
      (- (numberParts v).2 / ((numberParts v).1 * (numberParts v).1 +
        (numberParts v).2 * (numberParts v).2)) := by
  by_cases hc : isComplex v = true
  · simp only [reciprocal, div, hc, Bool.or_true, ↓reduceIte]
    change mkParts ((1 * (numberParts v).1 + 0 * (numberParts v).2) / _)
      ((0 * (numberParts v).1 - 1 * (numberParts v).2) / _) = _
    simp only [Rat.one_mul, Rat.zero_mul, Rat.add_zero, Rat.sub_eq_add_neg, Rat.zero_add]
  · have hcf : isComplex v = false := Bool.eq_false_iff.mpr hc
    rw [reciprocal_rational_view v hcf, numberParts_of_not_complex v hcf]
    simp only [Rat.zero_mul, Rat.add_zero, Rat.neg_zero, zero_div, mkParts_zero]
    congr 2
    by_cases hq : rationalValue v = 0
    · simp [hq]
    · field_simp

theorem times_reciprocal (v : SExpr) (hn : acl2Numberp v ≠ .nil)
    (hz : v ≠ .atom (.number (.int 0))) :
    times v (reciprocal v) = .atom (.number (.int 1)) := by
  have hparts : numberParts v ≠ (0, 0) := by
    intro h
    apply hz
    have hm := mkParts_numberParts v
    rw [h, fix_of_number v hn] at hm
    exact hm.symm
  have hnorm : (numberParts v).1 * (numberParts v).1 +
      (numberParts v).2 * (numberParts v).2 ≠ 0 := by
    intro h
    apply hparts
    ext <;> nlinarith [sq_nonneg (numberParts v).1, sq_nonneg (numberParts v).2]
  rw [reciprocal_parts, times_parts, numberParts_mkParts]
  change mkParts _ _ = mkParts 1 0
  congr 1
  · calc
      _ = ((numberParts v).1 * (numberParts v).1 +
          (numberParts v).2 * (numberParts v).2) *
          ((numberParts v).1 * (numberParts v).1 +
          (numberParts v).2 * (numberParts v).2)⁻¹ := by
        simp only [Rat.div_def]
        ring
      _ = 1 := Rat.mul_inv_cancel _ hnorm
  · simp only [Rat.div_def]
    ring


end ACL2.Logic
