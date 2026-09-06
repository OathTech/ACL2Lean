import ACL2Lean.NumericCompletion

namespace ACL2.Logic

/-- Primitive negation through the same canonical component representation
used by addition. The recorded tau leaves in pass1/basic-arithmetic require
normalization of nested negations, including nonnumber completion. -/
theorem neg_parts (v : SExpr) :
    neg v = mkParts (-(numberParts v).1) (-(numberParts v).2) := by
  cases v with
  | nil | cons _ _ => rfl
  | atom a =>
    cases a with
    | number n =>
      cases n with
      | int k =>
        simp [neg, numberParts, rationalValue, mkParts, Number.fromParts,
          Number.fromRat, toRat, mkNumber]
      | rational n d hc =>
        have facts : 2 ≤ d ∧ n.natAbs.gcd d = 1 := by
          simpa only [canonRat, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using hc
        simp [neg, numberParts, rationalValue, mkParts, Number.fromParts,
          Number.fromRat, toRat, mkNumber, Int.natAbs_neg, facts.2,
          show d ≠ 0 by omega, show d ≠ 1 by omega]
      | complex _ _ _ => rfl
    | _ => rfl

/-- ACL2 axioms.lisp's INVERSE-OF-+ primitive equation. -/
theorem plus_neg_right (v : SExpr) :
    plus v (neg v) = .atom (.number (.int 0)) := by
  rw [plus_parts, neg_parts, numberParts_mkParts]
  simp only [Rat.add_neg_cancel]
  rfl

/-- The ground-zero primitive negation/addition equation (axioms.lisp),
used at its recorded rewrite in INTEGERP-MOD. -/
theorem neg_plus (a b : SExpr) : neg (plus a b) = plus (neg a) (neg b) := by
  simp only [neg_parts, plus_parts, numberParts_mkParts, Rat.neg_add]

/-- Scalar normalization used by the recorded additive-inverse tau leaf. -/
theorem rat_neg_eq_iff (a b : Rat) : -a = b ↔ a + b = 0 := by
  constructor
  · rintro rfl; exact Rat.add_neg_cancel a
  · intro h
    exact Rat.add_left_cancel a (by rw [Rat.add_neg_cancel, h])

end ACL2.Logic
