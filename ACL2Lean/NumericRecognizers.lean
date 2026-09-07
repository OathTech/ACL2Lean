import ACL2Lean.Logic

namespace ACL2.Logic

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
