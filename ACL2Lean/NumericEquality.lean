import ACL2Lean.NumericCompletion

namespace ACL2.Logic

/-- Numeric completion preserves values carrying an explicit number premise. -/
theorem fix_of_number (v : SExpr) (h : acl2Numberp v ≠ .nil) : fix v = v := by
  cases v with
  | nil | cons _ _ => simp [acl2Numberp] at h
  | atom a => cases a <;> simp_all [acl2Numberp, fix]

/-- Equality of ACL2 numbers is equality of their canonical components.
The number premises are essential: completion identifies distinct nonnumbers. -/
theorem number_eq_iff (a b : SExpr) (ha : acl2Numberp a ≠ .nil)
    (hb : acl2Numberp b ≠ .nil) : a = b ↔ numberParts a = numberParts b := by
  constructor
  · exact congrArg numberParts
  · intro h
    have hm := congrArg (fun p : Rat × Rat => mkParts p.1 p.2) h
    simpa only [mkParts_numberParts, fix_of_number a ha, fix_of_number b hb] using hm

/-- Constructor-headed normalization for numeric equality in recorded tau
leaves. Keeps the other operand's explicit number hypothesis. -/
theorem mkParts_eq_iff (r i : Rat) (b : SExpr) (hb : acl2Numberp b ≠ .nil) :
    mkParts r i = b ↔ (r, i) = numberParts b := by
  rw [number_eq_iff _ _ (by change SExpr.t ≠ SExpr.nil; decide) hb, numberParts_mkParts]

end ACL2.Logic
