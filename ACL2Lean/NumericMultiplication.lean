import ACL2Lean.NumericLemmas
import ACL2Lean.NumericCompletion

namespace ACL2.Logic

/-- ACL2's primitive multiplication commutativity axiom, including complex
values and nonnumber completion. Consumed at the recorded COMMUTATIVITY-OF-*
node in arithmetic-3's basic book. -/
theorem times_comm (a b : SExpr) : times a b = times b a := by
  simp [times, Bool.or_comm, Rat.mul_comm, Rat.add_comm, Int.mul_comm, Nat.mul_comm]



/-- Multiplication through the canonical complex component representation. -/
theorem times_parts (a b : SExpr) :
    times a b = mkParts
      ((numberParts a).1 * (numberParts b).1 - (numberParts a).2 * (numberParts b).2)
      ((numberParts a).1 * (numberParts b).2 + (numberParts a).2 * (numberParts b).1) := by
  by_cases h : (isComplex a || isComplex b) = true
  · simp only [times, h, ↓reduceIte]
  · have ha : isComplex a = false := by simpa using (Bool.or_eq_false_iff.mp
      (Bool.eq_false_iff.mpr h)).1
    have hb : isComplex b = false := by simpa using (Bool.or_eq_false_iff.mp
      (Bool.eq_false_iff.mpr h)).2
    rw [numberParts_of_not_complex a ha, numberParts_of_not_complex b hb]
    simp only [Rat.zero_mul, Rat.mul_zero, Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero,
      mkParts_zero, times, ha, hb, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    rw [mkNumber_eq_fromRat, Rat.mul_def']
    rcases rationalValue_num_den a with ⟨han, had⟩
    rcases rationalValue_num_den b with ⟨hbn, hbd⟩
    rw [han, had, hbn, hbd]

/-- ACL2's multiplication always returns a number, including completed inputs. -/
theorem acl2Numberp_times (a b : SExpr) : acl2Numberp (times a b) = .t := by
  rw [times_parts]
  rfl

/-- The primitive DISTRIBUTIVITY axiom, on arbitrary ACL2 values.
Required by the recorded rewrite in INTEGERP-MOD. -/
theorem times_add (a b c : SExpr) :
    times a (plus b c) = plus (times a b) (times a c) := by
  simp only [times_parts, plus_parts, numberParts_mkParts,
    Rat.sub_eq_add_neg, Rat.mul_add, Rat.neg_add]
  congr 1 <;> ac_rfl

/-- Multiplication by zero, including ACL2's nonnumber completion.
Normalizes a primitive subterm of the recorded USE-implication tau leaf.
The explicit integer constructor matches reflected literals in simp's index. -/
theorem times_zero_right (a : SExpr) :
    times a (.atom (.number (.int (Int.ofNat 0)))) = .atom (.number (.int (Int.ofNat 0))) := by
  rw [times_parts]
  change mkParts ((numberParts a).1 * 0 - (numberParts a).2 * 0)
    ((numberParts a).1 * 0 + (numberParts a).2 * 0) = _
  simp only [Rat.mul_zero, Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero]
  rfl

/-- The UNICITY-OF-1 primitive equation, including nonnumber completion. -/
theorem times_one_fix (v : SExpr) : times (.atom (.number (.int 1))) v = fix v := by
  rw [times_parts]
  change mkParts (1 * (numberParts v).1 - 0 * (numberParts v).2)
    (1 * (numberParts v).2 + 0 * (numberParts v).1) = _
  simp only [Rat.one_mul, Rat.zero_mul, Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero,
    mkParts_numberParts]

end ACL2.Logic
