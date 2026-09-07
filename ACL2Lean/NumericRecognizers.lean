import ACL2Lean.Logic

namespace ACL2.Logic

/-- Rational completion discards genuine complexes as well as nonnumbers.
This is used to normalize the recorded complex-constructor verdict leaf. -/
theorem rationalValue_zero_of_nonrational {v : SExpr}
    (h : rationalp v = .nil) : rationalValue v = 0 := by
  cases v with
  | nil | cons _ _ => rfl
  | atom a => cases a with
    | number n => cases n with
      | int _ | rational _ _ _ => simp [rationalp, SExpr.t] at h
      | complex _ _ _ => rfl
    | _ => rfl

/-- The recorded ELIM guard leaf compares a nonnumber with zero.
ACL2's numeric completion makes that strict comparison false. -/
theorem lt_zero_nil_of_nonnumber {v : SExpr} (h : acl2Numberp v = .nil) :
    lt v (.atom (.number (.int 0))) = .nil := by
  cases v with
  | nil | cons _ _ => rfl
  | atom a => cases a with
    | number _ => simp [acl2Numberp, SExpr.t] at h
    | _ => rfl

/-- The ACL2 numeric universe consists of rationals and genuine complex
rationals. This equation relates the primitive recognizers without exposing
arithmetic operations on their argument. -/
theorem acl2Numberp_nil_iff (v : SExpr) :
    acl2Numberp v = .nil ↔ rationalp v = .nil ∧ complexRationalp v = .nil := by
  cases v with
  | nil | cons _ _ => simp [acl2Numberp, rationalp, complexRationalp, isComplex]
  | atom a => cases a with
    | number n => cases n <;> simp [acl2Numberp, rationalp, complexRationalp, isComplex, SExpr.t]
    | _ => simp [acl2Numberp, rationalp, complexRationalp, isComplex]

end ACL2.Logic
