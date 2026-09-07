import ACL2Lean.NumericOrder
import ACL2Lean.NumericMultiplication
import Mathlib.Tactic.Linarith

namespace ACL2.Logic

private theorem ltParts (a b : SExpr) : lt a b ≠ .nil ↔
    (numberParts a).1 < (numberParts b).1 ∨
      ((numberParts a).1 = (numberParts b).1 ∧ (numberParts a).2 < (numberParts b).2) := by
  rw [lt_parts]
  split <;> simp_all [SExpr.t]

theorem isComplex_false_of_rationalp (v : SExpr) (h : rationalp v ≠ .nil) : isComplex v = false := by
  cases v with
  | nil | cons _ _ => rfl
  | atom a => cases a with
    | number n => cases n <;> simp_all [rationalp, isComplex]
    | _ => rfl

/-- Addition conjunct of ACL2's primitive POSITIVE axiom, including its
lexicographic complex order. Used by the two recorded POSITIVE instances in
the floor-bound dependency's multiplication cancellation proof. -/
theorem positiveAdd (a b : SExpr)
    (ha : lt (.atom (.number (.int 0))) a ≠ .nil)
    (hb : lt (.atom (.number (.int 0))) b ≠ .nil) :
    lt (.atom (.number (.int 0))) (plus a b) ≠ .nil := by
  rw [ltParts] at ha hb ⊢
  rw [plus_parts, numberParts_mkParts]
  change 0 < (numberParts a).1 + (numberParts b).1 ∨
    (0 = (numberParts a).1 + (numberParts b).1 ∧
      0 < (numberParts a).2 + (numberParts b).2)
  change 0 < (numberParts a).1 ∨ (0 = (numberParts a).1 ∧ 0 < (numberParts a).2) at ha
  change 0 < (numberParts b).1 ∨ (0 = (numberParts b).1 ∧ 0 < (numberParts b).2) at hb
  rcases ha with ha | ⟨har, hai⟩ <;> rcases hb with hb | ⟨hbr, hbi⟩
  · left; nlinarith
  · left; nlinarith
  · left; nlinarith
  · right; constructor <;> nlinarith

/-- The multiplication conjunct requires rational operands, as ACL2 does. -/
theorem positiveTimes (a b : SExpr)
    (hra : rationalp a ≠ .nil) (hrb : rationalp b ≠ .nil)
    (ha : lt (.atom (.number (.int 0))) a ≠ .nil)
    (hb : lt (.atom (.number (.int 0))) b ≠ .nil) :
    lt (.atom (.number (.int 0))) (times a b) ≠ .nil := by
  have hpa := numberParts_of_not_complex a (isComplex_false_of_rationalp a hra)
  have hpb := numberParts_of_not_complex b (isComplex_false_of_rationalp b hrb)
  rw [ltParts] at ha hb ⊢
  rw [times_parts, numberParts_mkParts, hpa, hpb]
  rw [hpa] at ha
  rw [hpb] at hb
  change 0 < rationalValue a ∨ (0 = rationalValue a ∧ 0 < (0 : Rat)) at ha
  change 0 < rationalValue b ∨ (0 = rationalValue b ∧ 0 < (0 : Rat)) at hb
  simp only [Rat.lt_irrefl, and_false, or_false] at ha hb
  apply Or.inl
  change 0 < rationalValue a * rationalValue b - 0 * 0
  nlinarith


end ACL2.Logic
