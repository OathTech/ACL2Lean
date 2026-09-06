import ACL2Lean.NumericReciprocal
import ACL2Lean.NumericMultiplication
import ACL2Lean.NumericCompletion

namespace ACL2.Logic

/-- The RATIONAL-IMPLIES2 primitive axiom. Its actual USE in the denominator
dependency needs the canonical numerator/denominator reconstruction law. -/
theorem rational_reconstruct (v : SExpr) (h : rationalp v ≠ .nil) :
    times (reciprocal (denominator v)) (numerator v) = v := by
  cases v with
  | nil | cons _ _ => simp [rationalp] at h
  | atom a =>
    cases a with
    | number n =>
      cases n with
      | int k =>
        simp only [denominator, numerator, reciprocal_int_view]
        rw [times_parts, numberParts_fromRat]
        rw [show (Rat.ofInt 1)⁻¹ = 1 from Rat.inv_eq_of_mul_eq_one (Rat.one_mul 1)]
        change mkParts (1 * Rat.ofInt k - 0 * 0) (1 * 0 + 0 * Rat.ofInt k) = _
        simp only [Rat.one_mul, Rat.zero_mul, Rat.mul_zero,
          Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero]
        exact mkParts_numberParts (.atom (.number (.int k)))
      | rational n d hc =>
        let v := SExpr.atom (.number (.rational n d hc))
        have hr : (Rat.ofInt (d : Int))⁻¹ * Rat.ofInt n = rationalValue v := by
          rw [Rat.mul_comm, ← Rat.div_def]
          exact (Rat.divInt_eq_div n (d : Int)).symm.trans (Rat.num_divInt_den (rationalValue v))
        simp only [denominator, numerator, reciprocal_int_view]
        rw [times_parts, numberParts_fromRat]
        change mkParts ((Rat.ofInt (d : Int))⁻¹ * Rat.ofInt n - 0 * 0)
          ((Rat.ofInt (d : Int))⁻¹ * 0 + 0 * Rat.ofInt n) = _
        simp only [Rat.zero_mul, Rat.mul_zero, Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero, hr]
        exact mkParts_numberParts v
      | complex _ _ _ => simp [rationalp] at h
    | _ => simp [rationalp] at h

/-- The completion axiom paired with RATIONAL-IMPLIES2 in the recorded USE.
Its nonrational branch is retained on the complete ACL2 value universe. -/
theorem denominator_completion (v : SExpr) :
    denominator v = (bif toBool (rationalp v) then denominator v else .atom (.number (.int 1))) := by
  cases v with
  | nil | cons _ _ => rfl
  | atom a => cases a with
    | number n => cases n <;> simp [denominator, rationalp, toBool]
    | _ => rfl

end ACL2.Logic
