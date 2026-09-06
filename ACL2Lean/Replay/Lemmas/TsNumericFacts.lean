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

end ACL2.Replay
