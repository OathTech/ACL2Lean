import ACL2Lean.Replay.Driver.NodeCore
import ACL2Lean.NumericComplexView

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- Arithmetic normalization for actual verdict leaves. Only equalities
with proved NUMBERP premises move to the field; completed primitive products
and explicit nonnumber premises have their own representation equations. -/
def dpComplexViewTactic : MetaM (TSyntax `tactic) :=
  `(tactic|
    (try simp_all only [Logic.not_nil_iff, Logic.toBool_eq_true,
      Logic.toBool_eq_false, Logic.equal_ne_nil_iff, Logic.equal_nil_iff]) <;>
    (try intro h) <;>
    (try simp_all only [Logic.not_nil_iff, Logic.equal_ne_nil_iff, not_not]) <;>
    (try simp (disch := first | assumption | decide |
      (simp only [Logic.acl2Numberp_times]; decide)) only
      [ne_eq, Logic.number_eq_iff_complex, Logic.acl2Numberp_times,
       Logic.complexValue_times, Logic.complexValue_zero,
       Logic.complexValue_nonnumber] at *) <;>
    solve
      | simp_all [mul_eq_zero]
      | grind -matchEqs -splitMatch [mul_eq_zero])

end ACL2.Replay.Driver
