import ACL2Lean.Logic

/-! Primitive exponent arithmetic for recorded DP leaves. The actual
BVCHOP upper-bound tau leaf requires positivity; this family is independent
of every book function and proves the evaluator operation for arbitrary
positive integer bases and every ACL2 exponent value. -/

open ACL2
namespace ACL2.Logic

theorem integerp_int (n : Int) : integerp (.atom (.number (.int n))) = .t := rfl

private theorem zero_lt_mkNumber (n : Int) (d : Nat) (hn : 0 < n) (hd : 0 < d)
    (hc : Nat.gcd n.natAbs d = 1) :
    lt (.atom (.number (.int 0))) (mkNumber n d) = .t := by
  simp only [mkNumber, (show d ≠ 0 by omega), ↓reduceDIte, hc,
    Nat.div_one]
  split <;> simp_all [lt, toRat]

theorem zero_lt_expt_pos_int (base : Int) (power : SExpr) (hb : 0 < base) :
    lt (.atom (.number (.int 0))) (expt (.atom (.number (.int base))) power) = .t := by
  cases power with
  | nil | cons _ _ => simp [expt, lt, toRat]
  | atom a =>
    cases a with
    | number n =>
      cases n with
      | rational _ _ _ | complex _ _ _ => simp [expt, lt, toRat]
      | int i =>
        simp only [expt, isComplex, Bool.false_eq_true, ↓reduceIte, toRat,
          beq_iff_eq, (show base ≠ 0 by omega)]
        by_cases hi : i = 0
        · simp [hi, lt, toRat]
        · simp only [hi, ↓reduceIte]
          split
          · apply zero_lt_mkNumber
            · exact Int.pow_pos hb
            · simp
            · simp
          · have hp : 0 < base ^ (-i).toNat := Int.pow_pos hb
            simp only [hp, ↓reduceIte, Int.one_mul]
            apply zero_lt_mkNumber
            · simp
            · exact Nat.pow_pos (by omega)
            · simp
    | _ => simp [expt, lt, toRat]

/-- ACL2's ZIP branch: a noninteger exponent completes to one. -/
theorem expt_of_not_integer (base power : SExpr)
    (h : integerp power = .nil) : expt base power = .atom (.number (.int 1)) := by
  cases power with
  | nil | cons _ _ => rfl
  | atom a =>
    cases a with
    | number n =>
      cases n with
      | int _ => simp [integerp] at h
      | rational _ _ _ | complex _ _ _ => rfl
    | _ => rfl

/-- Integer powers at nonnegative integer exponents stay integers.
The caller supplies the recorded exponent type and sign facts. -/
theorem integerp_expt_nonneg_int (base : Int) (power : SExpr)
    (hi : integerp power = .t)
    (hn : lt power (.atom (.number (.int 0))) = .nil) :
    integerp (expt (.atom (.number (.int base))) power) = .t := by
  cases power with
  | nil | cons _ _ => simp [integerp] at hi
  | atom a =>
    cases a with
    | number n =>
      cases n with
      | rational _ _ _ | complex _ _ _ => simp [integerp] at hi
      | int i =>
        have hn' : 0 ≤ i := by simpa [lt, toRat] using hn
        by_cases hz : i = 0
        · simp [expt, hz, integerp]
        · have hp : 0 < i := by omega
          by_cases hb : base = 0
          · simp [expt, hz, hb, toRat, integerp]
          · simp [expt, hz, hb, hp, mkNumber, toRat, integerp]
    | _ => simp [integerp] at hi

end ACL2.Logic
