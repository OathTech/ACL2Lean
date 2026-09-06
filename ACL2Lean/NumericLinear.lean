import ACL2Lean.NumericOrder
import ACL2Lean.NumericNegation
import ACL2Lean.NumericEquality

namespace ACL2.Logic

/-- The weak zero bound carried by an ACL2 polynomial, including the
lexicographic imaginary component. This is a certificate judgment. -/
def LinearNonnegative (p : Rat × Rat) : Prop :=
  0 ≤ p.1 ∧ (p.1 = 0 → 0 ≤ p.2)

def linearDifference (a b : SExpr) : Rat × Rat :=
  ((numberParts a).1 - (numberParts b).1,
   (numberParts a).2 - (numberParts b).2)

theorem linear_int_parts (n : Int) :
    numberParts (.atom (.number (.int n))) = ((n : Rat), 0) := rfl

/-- LINEARIZE1's false-comparison branch constructs lhs minus rhs with
relation <=. No number premise is needed for ACL2's completed comparison. -/
theorem linear_difference_nonnegative (a b : SExpr) (h : lt a b = .nil) :
    LinearNonnegative (linearDifference a b) := by
  rw [lt_parts] at h
  have hn : ¬ ((numberParts a).1 < (numberParts b).1 ∨
      ((numberParts a).1 = (numberParts b).1 ∧
        (numberParts a).2 < (numberParts b).2)) := by
    intro hp
    rw [if_pos hp] at h
    cases h
  unfold LinearNonnegative linearDifference
  grind

/-- Complementary unit rows isolate the equation exactly as
FIND-EQUATIONAL-POLY-RHS does. Numeric premises prevent completion from
identifying distinct nonnumbers. -/
theorem linear_unit_pair (a b : SExpr)
    (ha : acl2Numberp a ≠ .nil) (hb : acl2Numberp b ≠ .nil)
    (hp : LinearNonnegative (linearDifference a b))
    (hn : LinearNonnegative (linearDifference b a)) : a = b := by
  apply (number_eq_iff a b ha hb).mpr
  unfold LinearNonnegative linearDifference at hp hn
  apply Prod.ext <;> grind

/-- Consume a recorded rationality premise as the required number premise. -/
theorem linear_number_of_rational (a : SExpr) (h : rationalp a ≠ .nil) :
    acl2Numberp a ≠ .nil := by
  cases a with
  | nil | cons _ _ => simp [rationalp] at h
  | atom v => cases v with
    | number _ => simp [acl2Numberp, SExpr.t]
    | _ => simp [rationalp] at h

end ACL2.Logic
