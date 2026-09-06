import ACL2Lean.Replay.Driver.NodeCore
import ACL2Lean.NumericComplexView

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

private theorem equalNumberNonnumber (a b : SExpr)
    (ha : Logic.acl2Numberp a ≠ .nil) (hb : Logic.acl2Numberp b = .nil) :
    Logic.equal a b = .nil := by
  apply (Logic.equal_nil_iff a b).mpr
  intro h
  exact ha (h.symm ▸ hb)

/-- Completion normalization for recorded tau leaves with nonnumeric
inputs. The NUMBERP premise remains a hypothesis of that exact leaf. -/
def dpReciprocalCompletionTactic : MetaM (TSyntax `tactic) :=
  `(tactic| simp_all only [Logic.not_nil_iff, Logic.toBool_eq_true,
    Logic.equal_ne_nil_iff, Logic.equal_nil_iff, Logic.reciprocal_nonnumber] <;>
    first | assumption | contradiction | (symm; assumption))

private theorem equalNonnumberNumber (a b : SExpr)
    (ha : Logic.acl2Numberp a = .nil) (hb : Logic.acl2Numberp b ≠ .nil) :
    Logic.equal a b = .nil := by
  apply (Logic.equal_nil_iff a b).mpr
  intro h
  exact hb (h ▸ ha)

/-- Primitive completion and number/nonnumber separation inside a recorded
verdict leaf. Explicit nonnumber premises come from that leaf's context. -/
def dpNumericSeparationTactic : MetaM (TSyntax `tactic) :=
  `(tactic|
    simp only [Logic.equal_ne_nil_iff] <;>
    simp (disch := first | assumption | decide |
      (simp only [Logic.acl2Numberp_reciprocal, Logic.acl2Numberp_times]; decide)) only
      [equalNumberNonnumber, equalNonnumberNumber, Logic.times_nonnumber_right] <;>
    simp [Logic.equal_atom_int])

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
