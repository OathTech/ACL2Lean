import ACL2Lean.NumericLinear
import ACL2Lean.Replay.Lemmas.TsNumericFacts

namespace ACL2.Replay
open ACL2

/-- POLYS-FROM-TYPE-SET's zero cell constructs this positive weak row. -/
theorem linear_zero_cell_positive {v : SExpr} (h : InTs 1 v) :
    Logic.LinearNonnegative (Logic.linearDifference v (.atom (.number (.int 0)))) := by
  rw [zero_of_inTs1 h]
  simp only [Logic.LinearNonnegative, Logic.linearDifference, Logic.linear_int_parts, Rat.sub_self]
  exact ⟨by decide, fun _ => by decide⟩

/-- The same zero cell constructs the complementary negative weak row. -/
theorem linear_zero_cell_negative {v : SExpr} (h : InTs 1 v) :
    Logic.LinearNonnegative (Logic.linearDifference (.atom (.number (.int 0))) v) := by
  rw [zero_of_inTs1 h]
  simp only [Logic.LinearNonnegative, Logic.linearDifference, Logic.linear_int_parts, Rat.sub_self]
  exact ⟨by decide, fun _ => by decide⟩

end ACL2.Replay
