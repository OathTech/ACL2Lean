import ACL2Lean.NumericLemmas

namespace ACL2.Logic

/-- Reassembling the numeric components is ACL2's numeric completion. -/
theorem mkParts_numberParts (v : SExpr) :
    mkParts (numberParts v).1 (numberParts v).2 = fix v := by
  cases v with
  | nil | cons _ _ => rfl
  | atom a =>
    cases a with
    | number n =>
      cases n with
      | int k => simp [numberParts, rationalValue, mkParts, Number.fromParts,
          Number.fromRat, fix]
      | rational n d hc =>
        have hd : 2 ≤ d := by
          simp only [canonRat, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
          exact hc.1
        simp [numberParts, rationalValue, mkParts, Number.fromParts,
          Number.fromRat, fix, show d ≠ 1 by omega]
      | complex r i hi =>
        simp [numberParts, mkParts, Number.fromParts, hi, fix]
    | _ => rfl

/-- The primitive UNICITY-OF-0 equation, on the full ACL2 value universe. -/
theorem plus_zero_fix (v : SExpr) :
    plus (.atom (.number (.int 0))) v = fix v := by
  rw [plus_parts]
  change mkParts (0 + (numberParts v).1) (0 + (numberParts v).2) = _
  rw [Rat.zero_add, Rat.zero_add, mkParts_numberParts]

end ACL2.Logic
