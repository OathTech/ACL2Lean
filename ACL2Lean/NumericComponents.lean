import ACL2Lean.NumericLemmas

namespace ACL2.Logic

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

end ACL2.Logic
