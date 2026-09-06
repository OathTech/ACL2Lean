import ACL2Lean.Replay.Lemmas.TsAlgebra

namespace ACL2.Replay
open ACL2

/-- ACL2-NUMBERP is two-valued on every value, including genuine complexes. -/
theorem logic_acl2Numberp_ne_nil_t (v : SExpr)
    (h : Logic.acl2Numberp v ≠ SExpr.nil) : Logic.acl2Numberp v = SExpr.t := by
  cases v with
  | atom a => cases a <;> simp_all [Logic.acl2Numberp]
  | _ => simp_all [Logic.acl2Numberp]

/-- RATIONALP supplies ACL2's rational mask, excluding genuine complexes.
The clause walker intersects this with the separately recorded sign fact;
MOD-BOUND-LINEAR-ARG2's equality test is the first consumer. -/
theorem inTs_rationalp_true {v : SExpr}
    (h : Logic.toBool (Logic.rationalp v) = true) : InTs 63 v := by
  cases v with
  | nil | cons _ _ => simp [Logic.rationalp, Logic.toBool] at h
  | atom a =>
    cases a with
    | number n =>
      cases n with
      | int i =>
        show tsMember 63 (tsIndex (.atom (.number (.int i)))) = true
        simp only [tsIndex_int]
        split_ifs <;> decide
      | rational p q hc =>
        show tsMember 63 (tsIndex (.atom (.number (.rational p q hc)))) = true
        simp only [tsIndex_rat]
        split_ifs <;> decide
      | complex _ _ _ => simp [Logic.rationalp, Logic.toBool] at h
    | _ => simp [Logic.rationalp, Logic.toBool] at h

/-- The seven numeric bits describe precisely ACL2 numbers. -/
theorem logic_acl2Numberp_t_of_inTs {m : Int} {v : SExpr}
    (hm : tsSubsumedM m 127 = true) (hv : InTs m v) :
    Logic.acl2Numberp v = SExpr.t := by
  have h127 : InTs 127 v := inTs_weaken hm hv
  cases v with
  | nil => exact absurd h127 (by simp only [InTs, tsIndex_nil]; decide)
  | cons a d =>
    exact absurd h127 (by simp only [InTs, tsIndex_cons]; split_ifs <;> decide)
  | atom a =>
    cases a with
    | number _ => rfl
    | symbol s =>
      exact absurd h127 (by simp only [InTs, tsIndex_symbol]; split_ifs <;> decide)
    | keyword _ => exact absurd h127 (by simp only [InTs, tsIndex_keyword]; decide)
    | string _ => exact absurd h127 (by simp only [InTs, tsIndex_string]; decide)
    | char _ => exact absurd h127 (by simp only [InTs, tsIndex_char]; decide)

/-- Primitive rational type cells consumed at INTEGERP-MOD's recorded
RATIONALP multiplication/reciprocal node (argument mask 40, true mask 63).
These prove the numeric model's closure; they do not prove the book theorem. -/
theorem not_complex_of_inTs_rational {v : SExpr} (h : InTs 63 v) :
    Logic.isComplex v = false := by
  cases v with
  | nil | cons _ _ => rfl
  | atom a =>
    cases a with
    | number n =>
      cases n with
      | int _ | rational _ _ _ => rfl
      | complex _ _ _ =>
        exact absurd h (by simp only [InTs, tsIndex_complex]; decide)
    | _ => rfl

theorem inTs_mkNumber_rational (n : Int) (d : Nat) : InTs 63 (Logic.mkNumber n d) := by
  apply inTs_rationalp_true
  unfold Logic.mkNumber
  split
  · rfl
  · dsimp only
    split <;> rfl

theorem inTs_times_rat {a b : SExpr} (ha : InTs 63 a) (hb : InTs 63 b) :
    InTs 63 (Logic.times a b) := by
  simp only [Logic.times, not_complex_of_inTs_rational ha, not_complex_of_inTs_rational hb,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  exact inTs_mkNumber_rational _ _

theorem inTs_reciprocal_rat {a : SExpr} (ha : InTs 63 a) :
    InTs 63 (Logic.reciprocal a) := by
  simp only [Logic.reciprocal, Logic.div,
    show Logic.isComplex (.atom (.number (.int 1))) = false from rfl,
    not_complex_of_inTs_rational ha,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  split
  · exact inTs_rationalp_true rfl
  · exact inTs_mkNumber_rational _ _

theorem logic_rationalp_t_of_inTs {m : Int} {v : SExpr}
    (hm : tsSubsumedM m 63 = true) (h : InTs m v) :
    Logic.rationalp v = SExpr.t := by
  have h63 : InTs 63 v := inTs_weaken hm h
  cases v with
  | nil => exact absurd h63 (by simp only [InTs, tsIndex_nil]; decide)
  | cons a d =>
    exact absurd h63 (by simp only [InTs, tsIndex_cons]; split_ifs <;> decide)
  | atom a =>
    cases a with
    | number n =>
      cases n with
      | int _ | rational _ _ _ => rfl
      | complex _ _ _ => exact absurd h63 (by simp only [InTs, tsIndex_complex]; decide)
    | symbol s => exact absurd h63 (by simp only [InTs, tsIndex_symbol]; split_ifs <;> decide)
    | keyword _ => exact absurd h63 (by simp only [InTs, tsIndex_keyword]; decide)
    | string _ => exact absurd h63 (by simp only [InTs, tsIndex_string]; decide)
    | char _ => exact absurd h63 (by simp only [InTs, tsIndex_char]; decide)

/-- A refuted equality to zero excludes exactly ACL2's zero type bit. -/
theorem inTs_not_zero {v : SExpr}
    (h : Logic.toBool (Logic.equal v (.atom (.number (.int 0)))) = false) : InTs (-2) v := by
  cases v with
  | nil => show tsMember (-2) 7 = true; decide
  | cons a d =>
    show tsMember (-2) (tsIndex (.cons a d)) = true
    simp only [tsIndex_cons]; split_ifs <;> decide
  | atom a =>
    cases a with
    | number n =>
      cases n with
      | int i =>
        have hi : i ≠ 0 := by
          intro hz; subst i
          simp [Logic.equal, Logic.toBool, SExpr.t] at h
        show tsMember (-2) (tsIndex (.atom (.number (.int i)))) = true
        simp only [tsIndex_int, if_neg hi]; split_ifs <;> decide
      | rational p q hc =>
        show tsMember (-2) (tsIndex (.atom (.number (.rational p q hc)))) = true
        simp only [tsIndex_rat]; split_ifs <;> decide
      | complex r i hi => show tsMember (-2) 6 = true; decide
    | symbol s =>
      show tsMember (-2) (tsIndex (.atom (.symbol s))) = true
      simp only [tsIndex_symbol]; split_ifs <;> decide
    | keyword _ => show tsMember (-2) 9 = true; decide
    | string _ => show tsMember (-2) 12 = true; decide
    | char _ => show tsMember (-2) 13 = true; decide

/-- The positive rational type-set resolves a recorded comparison to true. -/
theorem zero_lt_of_inTs {m : Int} {v : SExpr}
    (hm : tsSubsumedM m 14 = true) (hv : InTs m v) :
    Logic.lt (.atom (.number (.int 0))) v = .t := by
  have h := inTs_weaken hm hv
  cases v with
  | nil => exact absurd h (by simp only [InTs, tsIndex_nil]; decide)
  | cons a d => exact absurd h (by simp only [InTs, tsIndex_cons]; split_ifs <;> decide)
  | atom a =>
    cases a with
    | number n =>
      cases n with
      | int i =>
        have hi : 0 < i := by
          by_contra hn
          have h0 : i ≠ 1 := by omega
          simp only [InTs, tsIndex_int, if_neg h0, if_neg (show ¬1 < i by omega)] at h
          split_ifs at h <;> contradiction
        simp [Logic.lt, Logic.isComplex, Logic.toRat, hi]
      | rational p q hc =>
        have hp : 0 < p := by
          by_contra hn
          simp only [InTs, tsIndex_rat, if_neg hn] at h
          contradiction
        simp [Logic.lt, Logic.isComplex, Logic.toRat, hp]
      | complex _ _ _ => exact absurd h (by simp only [InTs, tsIndex_complex]; decide)
    | symbol s => exact absurd h (by simp only [InTs, tsIndex_symbol]; split_ifs <;> decide)
    | keyword _ => exact absurd h (by simp only [InTs, tsIndex_keyword]; decide)
    | string _ => exact absurd h (by simp only [InTs, tsIndex_string]; decide)
    | char _ => exact absurd h (by simp only [InTs, tsIndex_char]; decide)

/-- Integer multiplication at INTEGERP-MOD's emitted argument leaves. -/
theorem inTs_times_int {a b : SExpr} (ha : InTs 23 a) (hb : InTs 23 b) :
    InTs 23 (Logic.times a b) := by
  obtain ⟨n, rfl⟩ := int_of_inTs23 ha
  obtain ⟨m, rfl⟩ := int_of_inTs23 hb
  rw [Logic.times_int]
  exact inTs_integerp_true rfl

/-- Primitive negation preserves the integer type-set. -/
theorem inTs_neg_int {a : SExpr} (ha : InTs 23 a) : InTs 23 (Logic.neg a) := by
  obtain ⟨n, rfl⟩ := int_of_inTs23 ha
  apply inTs_integerp_true
  simp [Logic.neg, Logic.toRat, Logic.mkNumber, Logic.integerp, Logic.toBool]

/-- NUMERATOR returns an integer also at ACL2's non-rational completion. -/
theorem inTs_numerator (a : SExpr) : InTs 23 (Logic.numerator a) := by
  apply inTs_integerp_true
  cases a with
  | nil | cons _ _ => rfl
  | atom a => cases a with
    | number n => cases n <;> rfl
    | _ => rfl

end ACL2.Replay
