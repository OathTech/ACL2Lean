import ACL2Lean.Replay.Driver.NodeCore
import ACL2Lean.NumericComplexView
import ACL2Lean.NumericNegation
import ACL2Lean.NumericPositive

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

private theorem guardedNumberEquality (a b : SExpr) (ha : Logic.acl2Numberp a ≠ .nil) :
    a = b ↔ Logic.acl2Numberp b ≠ .nil ∧ Logic.numberParts a = Logic.numberParts b := by
  constructor
  · intro h
    exact ⟨h ▸ ha, congrArg Logic.numberParts h⟩
  · rintro ⟨hb, h⟩
    exact (Logic.number_eq_iff a b ha hb).mpr h

private theorem plusNumber (a b : SExpr) : Logic.acl2Numberp (Logic.plus a b) ≠ .nil := by
  rw [Logic.plus_parts]
  change SExpr.t ≠ SExpr.nil
  decide

/-- Expose component and negation signs in an emitted verdict while keeping
products abstract. The strict helper's 7' verdict contains opposite positive
signs for the same imaginary component; linear arithmetic closes its context. -/
def dpComponentSignTactic : MetaM (TSyntax `tactic) :=
  `(tactic|
    simp_all only [Logic.not_nil_iff, Logic.toBool_eq_true, Logic.lt_parts, Logic.neg_parts,
      Logic.numberParts_mkParts, Logic.numberParts_realpart, Logic.numberParts_imagpart,
      show Logic.numberParts (.atom (.number (.int (Int.ofNat 0)))) = ((0 : Rat), (0 : Rat)) from rfl,
      Prod.fst, Prod.snd, Rat.neg_zero, Rat.lt_irrefl, and_false, or_false,
      ne_eq, ite_eq_right_iff, SExpr.t, reduceCtorEq, imp_false, not_not] <;>
    linarith)

/-- Normalize a numeric equality conclusion at an emitted verdict before
context-wide rewriting. IMAGPART-OF--'s final linear leaf otherwise loops
through its recursive sum equalities. Both numeric guards remain checked. -/
def dpComponentGoalTactic : MetaM (TSyntax `tactic) :=
  `(tactic|
    simp only [dpHideValue, logic_not_equal_nil_iff, Logic.equal_ne_nil_iff] at * <;>
    apply (Logic.number_eq_iff _ _ ?_ ?_).mpr <;>
    first
    | assumption
    | exact plusNumber _ _
    | (simp only [Logic.neg_parts]; change SExpr.t ≠ SExpr.nil; decide)
    | (simp only [ne_eq, Logic.acl2Numberp_nil_iff, Logic.rationalp_realpart,
        Logic.rationalp_imagpart, SExpr.t, reduceCtorEq, false_and, not_false_eq_true])
    | (simp only [Logic.neg_parts, Logic.plus_parts, Logic.numberParts_mkParts,
        Logic.numberParts_realpart, Logic.numberParts_imagpart,
        Prod.fst, Prod.snd, Rat.neg_zero, Rat.neg_neg, Rat.zero_add, Rat.add_zero]))

/-- Preserve the numeric guard when a verdict's equality identifies a sum
    or component with an arbitrary value. Then compare canonical components,
    keeping products abstract. The first witness is IMAGPART-OF-*-OF-I's
    final linear verdict: its sum equality supplies the required guard. -/
def dpComponentEqualityTactic : MetaM (TSyntax `tactic) :=
  `(tactic|
    simp only [dpHideValue, logic_not_equal_nil_iff, Logic.equal_ne_nil_iff] at * <;>
    simp (disch := first | exact plusNumber _ _ | assumption |
      (simp only [ne_eq, Logic.acl2Numberp_nil_iff, Logic.rationalp_realpart,
        Logic.rationalp_imagpart, SExpr.t, reduceCtorEq, false_and, not_false_eq_true])) only
      [guardedNumberEquality] at * <;>
    simp_all only [Logic.plus_parts, Logic.numberParts_mkParts, Logic.numberParts_imagpart,
      Logic.numberParts_realpart, Prod.ext_iff, Prod.fst, Prod.snd, Rat.zero_add, Rat.add_zero] <;>
    grind only [Rat.zero_add])

/-- Normalize primitive sums using the equalities of an emitted verdict leaf.
Keeping other numeric operations abstract preserves those recorded premises. -/
def dpPrimitiveAdditiveTactic : MetaM (TSyntax `tactic) :=
  `(tactic| simp_all only [logic_not_equal_nil_iff, Logic.equal_ne_nil_iff,
    Logic.plus_assoc, Logic.plus_comm, Logic.plus_left_comm])

private theorem subtractSummand (a b c : SExpr)
    (ha : Logic.acl2Numberp a ≠ .nil) (h : Logic.plus a b = c) :
    a = Logic.plus c (Logic.neg b) := by
  rw [← h, Logic.plus_assoc, Logic.plus_neg_right, Logic.plus_zero_right_fix,
    Logic.fix_of_number a ha]

/-- Cancel a summand using the equality in a recorded arithmetic verdict.
The numeric guard is checked from the leaf context or component range law. -/
def dpAdditiveCancellationTactic : MetaM (TSyntax `tactic) :=
  `(tactic| simp only [logic_not_equal_nil_iff, Logic.equal_ne_nil_iff] at * <;>
    apply subtractSummand <;> first | assumption |
      (simp only [ne_eq, Logic.acl2Numberp_nil_iff, Logic.rationalp_realpart,
        Logic.rationalp_imagpart, SExpr.t, reduceCtorEq, false_and, not_false_eq_true]))

/-- Complete components at an emitted verdict leaf before expanding numeric
constructors. The zero equation leaves FIX, whose numeric guard is checked
from the component recognizer law. -/
def dpComponentZeroTactic : MetaM (TSyntax `tactic) :=
  `(tactic| simp_all only [Logic.times_nonnumber_right, Logic.realpart_nonnumber,
    Logic.imagpart_nonnumber, Logic.equal_ne_nil_iff] <;>
    (try simp_all only [
      -- Component completion produces the numeral form of zero; captured
      -- literals use Int.ofNat. Both are the same checked primitive law.
      show ∀ a, Logic.times a (.atom (.number (.int 0))) =
        .atom (.number (.int 0)) from Logic.times_zero_right,
      show Logic.neg (.atom (.number (.int 0))) = .atom (.number (.int 0)) from rfl,
      Logic.plus_zero_right_fix, Logic.fix_nonnumber]) <;>
    (try simp (disch := simp only [ne_eq, Logic.acl2Numberp_nil_iff,
      Logic.rationalp_realpart, Logic.rationalp_imagpart, SExpr.t,
      reduceCtorEq, false_and, not_false_eq_true]) only
      [Logic.plus_zero_right_fix, Logic.plus_zero_fix, Logic.fix_of_number] at *) <;>
    first
    | rfl
    | (simp_all only [Logic.plus_parts, Logic.numberParts_nonnumber, Prod.fst, Prod.snd,
        Rat.zero_add, Rat.add_zero,
        show Logic.mkParts (0 : Rat) 0 = .atom (.number (.int 0)) from rfl] <;> rfl))

/-- Boolean normalization plus the primitive POSITIVE laws inside a recorded
verdict leaf. Numeric subterms stay abstract; the leaf itself must supply all
rationality and sign premises. This avoids constructor enumeration for the
isolated rewrite-atm verdict in multiplication cancellation. -/
def dpPrimitivePositiveTactic : MetaM (TSyntax `tactic) :=
  `(tactic|
    simp only [Bool.cond_eq_ite, Logic.toBool_eq_true] <;>
    grind only [Logic.positiveTimes, Logic.positiveAdd])

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
