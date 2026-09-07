import ACL2Lean.NumericLemmas

namespace ACL2.Logic

/-- The component view completes every nonnumeric value to zero. -/
theorem numberParts_nonnumber {v : SExpr} (h : acl2Numberp v = .nil) :
    numberParts v = (0, 0) := by
  cases v with
  | nil | cons _ _ => rfl
  | atom a => cases a with
    | number _ => simp [acl2Numberp] at h
    | _ => rfl

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

/-- FIX completes an explicitly nonnumeric value to zero. -/
theorem fix_nonnumber {v : SExpr} (h : acl2Numberp v = .nil) :
    fix v = .atom (.number (.int 0)) := by
  rw [← mkParts_numberParts, numberParts_nonnumber h]
  rfl

/-- The primitive UNICITY-OF-0 equation, on the full ACL2 value universe. -/
theorem plus_zero_fix (v : SExpr) :
    plus (.atom (.number (.int 0))) v = fix v := by
  rw [plus_parts]
  change mkParts (0 + (numberParts v).1) (0 + (numberParts v).2) = _
  rw [Rat.zero_add, Rat.zero_add, mkParts_numberParts]

/-- The same primitive zero-completion equation in the commuted position. -/
theorem plus_zero_right_fix (v : SExpr) :
    plus v (.atom (.number (.int 0))) = fix v := by
  rw [plus_comm, plus_zero_fix]

end ACL2.Logic
