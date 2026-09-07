import ACL2Lean.NumericMultiplication
import ACL2Lean.NumericEquality
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Rat.Cast.Order

namespace ACL2.Logic

/-- An injective field view of canonical ACL2 numbers. Nonnumbers retain
ACL2's zero completion. This is representation transport for recorded DP
leaves; it carries no theorem about an ACL2 book function. -/
def complexValue (v : SExpr) : Complex :=
  ⟨((numberParts v).1 : Real), ((numberParts v).2 : Real)⟩

theorem complexValue_eq_iff (a b : SExpr) :
    complexValue a = complexValue b ↔ numberParts a = numberParts b := by
  simp only [complexValue, Complex.ext_iff, Prod.ext_iff, Rat.cast_inj]

theorem number_eq_iff_complex (a b : SExpr) (ha : acl2Numberp a ≠ .nil)
    (hb : acl2Numberp b ≠ .nil) : a = b ↔ complexValue a = complexValue b := by
  rw [number_eq_iff a b ha hb, complexValue_eq_iff]

theorem complexValue_times (a b : SExpr) :
    complexValue (times a b) = complexValue a * complexValue b := by
  simp only [complexValue, times_parts, numberParts_mkParts]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem complexValue_zero :
    complexValue (.atom (.number (.int (Int.ofNat 0)))) = 0 := by
  apply Complex.ext <;> simp [complexValue, numberParts, rationalValue]

theorem complexValue_nonnumber (v : SExpr) (h : acl2Numberp v = .nil) :
    complexValue v = 0 := by
  apply Complex.ext <;> simp [complexValue, numberParts_nonnumber h]

/-- Multiplication completes a nonnumeric argument to zero. -/
theorem times_nonnumber_right (a b : SExpr) (hb : acl2Numberp b = .nil) :
    times a b = .atom (.number (.int (Int.ofNat 0))) := by
  apply (number_eq_iff_complex _ _ (by rw [acl2Numberp_times]; decide) (by decide)).mpr
  rw [complexValue_times, complexValue_nonnumber b hb, complexValue_zero, mul_zero]

end ACL2.Logic
