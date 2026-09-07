import ACL2Lean.NumericComponents
import ACL2Lean.NumericPositive
import ACL2Lean.NumericRecognizers

namespace ACL2.Logic

/-- Component completion in the primitive COMPLETION-OF-COMPLEX axiom,
required by the actual DEFAULT-COMPLEX-1/2 USE nodes. -/
theorem rationalValue_completed (x : SExpr) :
    rationalValue (bif toBool (rationalp x) then x else .atom (.number (.int 0))) =
      rationalValue x := by
  cases x with
  | nil | cons _ _ => rfl
  | atom a =>
    cases a with
    | number n => cases n <;> rfl
    | symbol _ | keyword _ | string _ | char _ => rfl

theorem complex_completion (x y : SExpr) :
    complex x y = complex
      (bif toBool (rationalp x) then x else .atom (.number (.int 0)))
      (bif toBool (rationalp y) then y else .atom (.number (.int 0))) := by
  simp only [complex, rationalValue_completed]


/-- The primitive COMPLEX-DEFINITION axiom, required by the recorded USE
in COMPLEX-OPENER. Its rational premises are retained. -/
theorem complex_definition (x y : SExpr)
    (hx : rationalp x ≠ .nil) (hy : rationalp y ≠ .nil) :
    complex x y = plus x (times (.atom (.number (.complex 0 1 (by decide)))) y) := by
  have hpx := numberParts_of_not_complex x (isComplex_false_of_rationalp x hx)
  have hpy := numberParts_of_not_complex y (isComplex_false_of_rationalp y hy)
  rw [complex, plus_parts, times_parts, numberParts_mkParts, hpx, hpy]
  change mkParts _ _ = mkParts (_ + (0 * _ - 1 * 0)) (0 + (0 * 0 + 1 * _))
  simp only [Rat.zero_mul, Rat.one_mul, Rat.sub_eq_add_neg, Rat.neg_zero,
    Rat.add_zero, Rat.zero_add]

theorem numberParts_fix (x : SExpr) : numberParts (fix x) = numberParts x := by
  cases x with
  | nil | cons _ _ => rfl
  | atom a => cases a <;> rfl

private theorem realpart_equal_parts (x y : SExpr) :
    equal (realpart x) (realpart y) =
      if (numberParts x).1 = (numberParts y).1 then .t else .nil := by
  have num (z : SExpr) : acl2Numberp (realpart z) ≠ .nil := by
    intro hn
    have hr := ((acl2Numberp_nil_iff _).mp hn).1
    rw [rationalp_realpart] at hr
    cases hr
  have he := number_eq_iff (realpart x) (realpart y) (num x) (num y)
  rw [numberParts_realpart, numberParts_realpart] at he
  simp only [Prod.mk.injEq, and_true] at he
  unfold equal
  simp only [beq_iff_eq, he]

/-- Component expression in ACL2's primitive COMPLETION-OF-< axiom.
This includes nonnumber completion and genuine complex arguments. -/
theorem lt_components (x y : SExpr) : lt x y =
    (bif toBool (lt (realpart x) (realpart y)) then
      lt (realpart x) (realpart y) else
      (bif toBool (equal (realpart x) (realpart y)) then
        lt (imagpart x) (imagpart y) else .nil)) := by
  rw [realpart_equal_parts]
  simp only [lt_parts, numberParts_realpart, numberParts_imagpart,
    Rat.lt_irrefl, and_false, or_false]
  by_cases hl : (numberParts x).1 < (numberParts y).1 <;>
    by_cases he : (numberParts x).1 = (numberParts y).1 <;>
    by_cases hi : (numberParts x).2 < (numberParts y).2 <;>
    simp_all [toBool, SExpr.t]

theorem lt_completion (x y : SExpr) : lt x y =
    (bif toBool (bif toBool (rationalp x) then rationalp y else .nil) then lt x y else
      (bif toBool (lt (realpart (fix x)) (realpart (fix y))) then
        lt (realpart (fix x)) (realpart (fix y)) else
        (bif toBool (equal (realpart (fix x)) (realpart (fix y))) then
          lt (imagpart (fix x)) (imagpart (fix y)) else .nil))) := by
  cases toBool (bif toBool (rationalp x) then rationalp y else .nil) with
  | true => rfl
  | false =>
    simp only [cond_false]
    rw [← lt_components]
    simp only [lt_parts, numberParts_fix]

end ACL2.Logic
