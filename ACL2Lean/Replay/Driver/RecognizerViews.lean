import ACL2Lean.Replay.Driver.NodeCore
import ACL2Lean.NumericRecognizers

namespace ACL2.Replay.Driver
open ACL2 Lean Lean.Meta

/-- Resolve numeric-partition contradictions inside an emitted DP leaf
before exposing the arithmetic carried by its other literals. The complete
leaf stays the goal; only primitive recognizer and Boolean equations are
normalized. Failure restores that goal for the existing numeric routes.
First consumer: the recorded Subgoal 9' type-set leaves of Kestrel's strict
multiplication helper. -/
def dpRecognizerViewTactic : MetaM (TSyntax `tactic) :=
  `(tactic| try solve
   | simp_all only [Int.ofNat_eq_natCast, Int.ofNat_zero,
       Logic.lt_zero_nil_of_nonnumber, Logic.not_nil_iff,
       Logic.toBool_nil, Bool.false_eq_true]
   |
    simp_all only [Bool.cond_eq_ite, Logic.toBool_eq_true, ne_eq,
      Logic.not_nil_iff, not_not, Logic.acl2Numberp_nil_iff,
      and_true, true_and, ite_true, ite_false, not_true_eq_false, not_false_eq_true])

end ACL2.Replay.Driver
