import ACL2Lean.NumericOrder

namespace ACL2.Logic

private theorem numberpMkNumber (n : Int) (d : Nat) : acl2Numberp (mkNumber n d) = .t := by
  unfold mkNumber
  split
  · rfl
  · dsimp only
    split <;> rfl

/-- Reciprocal's completed result is numeric, including at zero and on
nonnumbers. Used by recorded reciprocal recognizer and literal verdicts. -/
theorem acl2Numberp_reciprocal (v : SExpr) : acl2Numberp (reciprocal v) = .t := by
  unfold reciprocal div
  split
  · rfl
  · dsimp only
    split
    · rfl
    · exact numberpMkNumber _ _

/-- The nonnumeric arm of ACL2's reciprocal completion axiom. -/
theorem reciprocal_nonnumber (v : SExpr) (h : acl2Numberp v = .nil) :
    reciprocal v = .atom (.number (.int 0)) := by
  cases v with
  | nil | cons _ _ => rfl
  | atom a => cases a with
    | number n => cases n <;> simp [acl2Numberp, SExpr.t] at h
    | symbol _ | keyword _ | string _ | char _ => rfl

/-- Primitive reciprocal on the real component. The actual reciprocal-sign
tau clauses in arithmetic-3/pass1/inequalities require this representation
normalization; the recorded IFF rewrite and clause splits remain replayed. -/
theorem reciprocal_rational_view (v : SExpr) (hv : isComplex v = false) :
    reciprocal v = .atom (.number (Number.fromRat (rationalValue v)⁻¹)) := by
  have ⟨hn, hd⟩ := rationalValue_num_den v
  unfold reciprocal div
  rw [show isComplex (.atom (.number (.int 1))) = false from rfl, hv]
  simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  simp only [show toRat (.atom (.number (.int 1))) = (1, 1) from rfl,
    Int.one_mul, Nat.one_mul]
  change (if (toRat v).1 == 0 then .atom (.number (.int 0)) else
    mkNumber (if (toRat v).1 < 0 then -((toRat v).2 : Int) else (toRat v).2)
      (toRat v).1.natAbs) = _
  rw [Rat.inv_def, hn, hd]
  cases h : (toRat v).1 with
  | ofNat n =>
    cases n with
    | zero => simp [Rat.divInt, Number.fromRat]
    | succ n => simp [mkNumber_eq_fromRat, Rat.divInt,
        show (n : Int) + 1 ≠ 0 by omega,
        show ¬ ((n : Int) + 1 < 0) by omega,
        show ((n : Int) + 1).natAbs = n + 1 by omega]
  | negSucc n => simp [mkNumber_eq_fromRat, Rat.divInt, Rat.normalize_eq_mkRat]

/-- Constructor instances keep reciprocal normalization ahead of component
expansion in the DP leaf simplifier. -/
theorem reciprocal_int_view (n : Int) : reciprocal (.atom (.number (.int n))) =
    .atom (.number (Number.fromRat (Rat.ofInt n)⁻¹)) :=
  reciprocal_rational_view _ rfl

theorem reciprocal_rat_view (n : Int) (d : Nat) (hc : canonRat n d = true) :
    reciprocal (.atom (.number (.rational n d hc))) =
      .atom (.number (Number.fromRat (rationalValue (.atom (.number (.rational n d hc))))⁻¹)) :=
  reciprocal_rational_view _ rfl

/-- Rational order normalization for the negative reciprocal tau leaves. -/
theorem rat_inv_lt_zero (q : Rat) : q⁻¹ < 0 ↔ q < 0 := by
  rw [Rat.lt_iff, Rat.lt_iff, Rat.num_inv]
  simp only [show (0 : Rat).num = 0 from rfl, show (0 : Rat).den = 1 from rfl,
    Int.zero_mul]
  have hd := q.den_pos
  cases hn : q.num with
  | ofNat n =>
    cases n with
    | zero => simp [Int.sign]
    | succ n => simp [Int.sign]; omega
  | negSucc n => simp [Int.sign]; omega

end ACL2.Logic
