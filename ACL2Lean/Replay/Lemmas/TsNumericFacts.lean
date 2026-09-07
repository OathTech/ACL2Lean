import ACL2Lean.Replay.Lemmas.TsAlgebra
import ACL2Lean.NumericReciprocal
import ACL2Lean.NumericMultiplication
import ACL2Lean.NumericOrder

namespace ACL2.Replay
open ACL2

/-- The complete primitive comparison range, including complex and
nonnumeric inputs. Used by a recorded Boolean type-set query. -/
theorem logic_lt_range (a b : SExpr) : Logic.lt a b = .t ∨ Logic.lt a b = .nil := by
  rw [Logic.lt_parts]
  split <;> simp

/-- Numeric values occupy exactly the seven numeric type-set cells. -/
theorem inTs_acl2Numberp {v : SExpr} (h : Logic.acl2Numberp v = .t) : InTs 127 v := by
  cases v with
  | nil | cons _ _ => simp [Logic.acl2Numberp] at h
  | atom a => cases a with
    | number n => cases n with
      | int i => simp only [InTs, tsIndex_int]; split_ifs <;> decide
      | rational p q hc => simp only [InTs, tsIndex_rat]; split_ifs <;> decide
      | complex r i hi => simp only [InTs, tsIndex_complex]; decide
    | _ => simp [Logic.acl2Numberp] at h

/-- The recorded ACL2-NUMBERP reciprocal node in inverse uniqueness has
TYPESET 126 and TRUETS 127. Its primitive numeric range suffices. -/
theorem inTs_reciprocal_number (v : SExpr) : InTs 127 (Logic.reciprocal v) :=
  inTs_acl2Numberp (Logic.acl2Numberp_reciprocal v)

/-- The sharp zero-product cell consumed by the reciprocal-zero theorem's
recorded disjoint-type equality node. Both factors remain unrestricted. -/
theorem inTs_times_zero_right (v : SExpr) :
    InTs 1 (Logic.times v (.atom (.number (.int (Int.ofNat 0))))) := by
  rw [Logic.times_zero_right]
  unfold InTs
  decide

theorem inTs_times_zero_left (v : SExpr) :
    InTs 1 (Logic.times (.atom (.number (.int (Int.ofNat 0)))) v) := by
  rw [Logic.times_comm]
  exact inTs_times_zero_right v

/-- ACL2-NUMBERP is two-valued on every value, including genuine complexes. -/
theorem logic_acl2Numberp_ne_nil_t (v : SExpr)
    (h : Logic.acl2Numberp v ≠ SExpr.nil) : Logic.acl2Numberp v = SExpr.t := by
  cases v with
  | atom a => cases a <;> simp_all [Logic.acl2Numberp]
  | _ => simp_all [Logic.acl2Numberp]

/-- The positive numeric context entry used by recorded linear queries. -/
theorem inTs_acl2Numberp_true {v : SExpr}
    (h : Logic.toBool (Logic.acl2Numberp v) = true) : InTs 127 v :=
  inTs_acl2Numberp (logic_acl2Numberp_ne_nil_t v ((Logic.toBool_eq_true _).mp h))

/-- RATIONALP's true branch is exactly T, including the complex rejection. -/
theorem logic_rationalp_ne_nil_t (v : SExpr)
    (h : Logic.rationalp v ≠ SExpr.nil) : Logic.rationalp v = SExpr.t := by
  cases v with
  | atom a => cases a with
    | number n => cases n <;> simp_all [Logic.rationalp]
    | _ => simp_all [Logic.rationalp]
  | _ => simp_all [Logic.rationalp]

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

/-- The multiplication helper's recorded complex type mask comes from its
COMPLEX-RATIONALP case. This is the primitive recognizer's exact cell. -/
theorem inTs_complexRationalp_true {v : SExpr}
    (h : Logic.toBool (Logic.complexRationalp v) = true) : InTs 64 v := by
  cases v with
  | nil | cons _ _ => simp [Logic.complexRationalp, Logic.toBool] at h
  | atom a => cases a with
    | number n => cases n with
      | complex _ _ _ => simp only [InTs, tsIndex_complex]; decide
      | _ => simp [Logic.complexRationalp, Logic.toBool] at h
    | _ => simp [Logic.complexRationalp, Logic.toBool] at h

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

/-- The helper's two negative recognizer tests exclude all seven numeric
cells when their masks are intersected at the emitted ACL2-NUMBERP node. -/
theorem inTs_rationalp_false {v : SExpr}
    (h : Logic.toBool (Logic.rationalp v) = false) : InTs (-64) v := by
  cases v with
  | nil => simp only [InTs, tsIndex_nil]; decide
  | cons a d => simp only [InTs, tsIndex_cons]; split_ifs <;> decide
  | atom a => cases a with
    | number n => cases n with
      | int _ | rational _ _ _ => simp [Logic.rationalp, Logic.toBool] at h
      | complex _ _ _ => simp only [InTs, tsIndex_complex]; decide
    | symbol s => simp only [InTs, tsIndex_symbol]; split_ifs <;> decide
    | keyword _ => simp only [InTs, tsIndex_keyword]; decide
    | string _ => simp only [InTs, tsIndex_string]; decide
    | char _ => simp only [InTs, tsIndex_char]; decide

theorem inTs_complexRationalp_false {v : SExpr}
    (h : Logic.toBool (Logic.complexRationalp v) = false) : InTs (-65) v := by
  cases v with
  | nil => simp only [InTs, tsIndex_nil]; decide
  | cons a d => simp only [InTs, tsIndex_cons]; split_ifs <;> decide
  | atom a => cases a with
    | number n => cases n with
      | int i => simp only [InTs, tsIndex_int]; split_ifs <;> decide
      | rational _ _ _ => simp only [InTs, tsIndex_rat]; split_ifs <;> decide
      | complex _ _ _ => simp [Logic.complexRationalp, Logic.toBool] at h
    | symbol s => simp only [InTs, tsIndex_symbol]; split_ifs <;> decide
    | keyword _ => simp only [InTs, tsIndex_keyword]; decide
    | string _ => simp only [InTs, tsIndex_string]; decide
    | char _ => simp only [InTs, tsIndex_char]; decide

theorem logic_acl2Numberp_nil_of_ts_disjoint {m : Int} {v : SExpr}
    (hm : tsDisjointM m 127 = true) (hv : InTs m v) :
    Logic.acl2Numberp v = .nil := by
  cases v with
  | nil | cons _ _ => rfl
  | atom a => cases a with
    | number _ => exact False.elim (inTs_disjoint_absurd hm hv (inTs_acl2Numberp rfl))
    | _ => rfl

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

/-- Rational sum and negation cells at the recorded RATIONALP query in
the multiplication-order cancellation proof's POSITIVE instance. -/
theorem inTs_plus_rat {a b : SExpr} (ha : InTs 63 a) (hb : InTs 63 b) :
    InTs 63 (Logic.plus a b) := by
  simp only [Logic.plus, not_complex_of_inTs_rational ha, not_complex_of_inTs_rational hb,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  exact inTs_mkNumber_rational _ _

theorem inTs_neg_rat {a : SExpr} (ha : InTs 63 a) : InTs 63 (Logic.neg a) := by
  simp only [Logic.neg, not_complex_of_inTs_rational ha, Bool.false_eq_true, ↓reduceIte]
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

/-- The false zero-on-left comparison excludes positive rationals.
The weak multiplication helper intersects this with its other emitted
context tests before solidifying the singleton zero cell. -/
theorem inTs_zero_lt_false {v : SExpr}
    (h : Logic.toBool (Logic.lt (.atom (.number (.int 0))) v) = false) :
    InTs (-15) v := by
  have partition : ∀ i : Nat, i < 14 →
      tsMember 14 i = true ∨ tsMember (-15) i = true := by
    intro i hi
    interval_cases i <;> decide
  rcases partition (tsIndex v) (tsIndex_lt v) with hp | hn
  · have ht := zero_lt_of_inTs (show tsSubsumedM 14 14 = true by decide) hp
    rw [ht] at h
    contradiction
  · exact hn

/-- ACL2's zero type cell has exactly the canonical integer-zero value. -/
theorem zero_of_inTs1 {v : SExpr} (h : InTs 1 v) :
    v = .atom (.number (.int 0)) := by
  obtain ⟨n, rfl⟩ := int_of_inTs23 (inTs_weaken (show tsSubsumedM 1 23 = true by decide) h)
  have hn : n = 0 := by
    by_contra hn
    simp only [InTs, tsIndex_int, if_neg hn] at h
    split_ifs at h <;> contradiction
  subst n
  rfl

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
