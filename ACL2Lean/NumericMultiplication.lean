import ACL2Lean.NumericLemmas

namespace ACL2.Logic

/-- ACL2's primitive multiplication commutativity axiom, including complex
values and nonnumber completion. Consumed at the recorded COMMUTATIVITY-OF-*
node in arithmetic-3's basic book. -/
theorem times_comm (a b : SExpr) : times a b = times b a := by
  simp [times, Bool.or_comm, Rat.mul_comm, Rat.add_comm, Int.mul_comm, Nat.mul_comm]

end ACL2.Logic
