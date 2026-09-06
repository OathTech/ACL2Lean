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

end ACL2.Replay
