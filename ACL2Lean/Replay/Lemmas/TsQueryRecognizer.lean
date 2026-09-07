import ACL2Lean.Replay.Lemmas.TsBooleanFacts

namespace ACL2.Replay
open ACL2

/-- The translated two-cell test in an ordinary recognizer theorem.
The predicate's value is abstract: the equivalence must come from replay. -/
def booleanCellTest (v : SExpr) : SExpr :=
  cond (Logic.toBool (Logic.equal v .t)) (Logic.equal v .t) (Logic.equal v .nil)

theorem booleanCellTest_ne_nil_iff (v : SExpr) :
    booleanCellTest v ≠ .nil ↔ v = .t ∨ v = .nil := by
  simp only [booleanCellTest, Logic.equal, Logic.toBool]
  split_ifs <;> simp_all

/-- Decode membership using the instantiated ordinary theorem, not a
handwritten fact about the predicate implementing that recognizer. -/
theorem inTs_of_recognizer_equivalence {p v : SExpr}
    (heq : p = booleanCellTest v) (hp : p ≠ .nil) : InTs 384 v :=
  inTs_of_boolean_range ((booleanCellTest_ne_nil_iff v).mp (heq ▸ hp))

theorem recognizer_equivalence_of_inTs {p v : SExpr}
    (heq : p = booleanCellTest v) (hv : InTs 384 v) : p = .t := by
  rw [heq]
  rcases boolean_range_of_inTs hv with h | h <;> subst v <;> decide

end ACL2.Replay
