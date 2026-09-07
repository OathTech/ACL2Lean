import ACL2Lean.NumericLemmas
import ACL2Lean.NumericEquality

namespace ACL2.Logic

/-- The completed primitive constructor always returns an ACL2 number. -/
theorem acl2Numberp_complex (a b : SExpr) : acl2Numberp (complex a b) = .t := by
  rfl

/-- Primitive component completion before expanding arithmetic on a nonnumber. -/
private theorem components_nonnumber {v : SExpr} (h : acl2Numberp v = .nil) :
    realpart v = .atom (.number (.int 0)) ∧
    imagpart v = .atom (.number (.int 0)) := by
  cases v with
  | nil | cons _ _ => exact ⟨rfl, rfl⟩
  | atom a => cases a with
    | number _ => simp [acl2Numberp] at h
    | _ => exact ⟨rfl, rfl⟩

theorem realpart_nonnumber {v : SExpr} (h : acl2Numberp v = .nil) :
    realpart v = .atom (.number (.int 0)) := (components_nonnumber h).1

theorem imagpart_nonnumber {v : SExpr} (h : acl2Numberp v = .nil) :
    imagpart v = .atom (.number (.int 0)) := (components_nonnumber h).2

/-- The two range conjuncts of the primitive COMPLEX-IMPLIES1 axiom. -/
theorem rationalp_realpart (v : SExpr) : rationalp (realpart v) = .t := by
  cases v with
  | atom a => cases a with
    | number n => cases n with
      | complex r _ _ =>
        simp only [realpart, Number.fromRat]
        split <;> rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

theorem rationalp_imagpart (v : SExpr) : rationalp (imagpart v) = .t := by
  cases v with
  | atom a => cases a with
    | number n => cases n with
      | complex _ i _ =>
        simp only [imagpart, Number.fromRat]
        split <;> rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

/-- Projection into the rational components of the completed numeric value.
Used to normalize recorded decision-procedure clauses about REALPART. -/
theorem numberParts_realpart (v : SExpr) :
    numberParts (realpart v) = ((numberParts v).1, 0) := by
  cases v with
  | atom a => cases a with
    | number n => cases n with
      | complex r i h => exact numberParts_fromRat r
      | _ => rfl
    | _ => rfl
  | _ => rfl

/-- IMAGPART is itself rational, including the nonnumber completion. -/
theorem numberParts_imagpart (v : SExpr) :
    numberParts (imagpart v) = ((numberParts v).2, 0) := by
  cases v with
  | atom a => cases a with
    | number n => cases n with
      | complex r i h => exact numberParts_fromRat i
      | _ => rfl
    | _ => rfl
  | _ => rfl

/-- ACL2's primitive REALPART-IMAGPART-ELIM axiom, consumed by the
recorded destructor-elimination processor under its numeric guard. -/
theorem complex_realpart_imagpart {v : SExpr} (h : acl2Numberp v ≠ .nil) :
    complex (realpart v) (imagpart v) = v := by
  have hr : rationalValue (realpart v) = (numberParts v).1 := by
    cases v with
    | atom a => cases a with
      | number n => cases n with
        | complex r _ _ => exact rationalValue_fromRat r
        | _ => rfl
      | _ => rfl
    | _ => rfl
  have hi : rationalValue (imagpart v) = (numberParts v).2 := by
    cases v with
    | atom a => cases a with
      | number n => cases n with
        | complex _ i _ => exact rationalValue_fromRat i
        | _ => rfl
      | _ => rfl
    | _ => rfl
  rw [complex, hr, hi, mkParts_numberParts, fix_of_number v h]

end ACL2.Logic
