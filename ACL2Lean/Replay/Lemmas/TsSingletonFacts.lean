import ACL2Lean.Replay.Lemmas.TsBooleanFacts
import ACL2Lean.Replay.Lemmas.TsNumericFacts

namespace ACL2.Replay
open ACL2

/-- Removing the NIL singleton from a Boolean entry leaves T. -/
theorem boolean_exclude_nil {v : SExpr} (hv : InTs 384 v)
    (he : Logic.equal v .nil = .nil) : v = .t := by
  rcases boolean_range_of_inTs hv with hn | ht
  · exact False.elim ((Logic.equal_nil_iff _ _).mp he hn)
  · exact ht

/-- Removing the T singleton from a Boolean entry leaves NIL. -/
theorem boolean_exclude_t {v : SExpr} (hv : InTs 384 v)
    (he : Logic.equal v .t = .nil) : v = .nil := by
  rcases boolean_range_of_inTs hv with hn | ht
  · exact hn
  · exact False.elim ((Logic.equal_nil_iff _ _).mp he ht)

/-- Equal singleton-zero operand cells make the equality true. -/
theorem equal_t_of_zero_cells {a b : SExpr} (ha : InTs 1 a) (hb : InTs 1 b) :
    Logic.equal a b = .t := by
  rw [zero_of_inTs1 ha, zero_of_inTs1 hb]
  rfl

end ACL2.Replay
