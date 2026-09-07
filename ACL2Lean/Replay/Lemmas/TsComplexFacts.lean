import ACL2Lean.Replay.Lemmas.TsNumericFacts
import ACL2Lean.NumericEquality

namespace ACL2.Replay
open ACL2

/-- The complex bit supplies the primitive recognizer's true verdict.
Consumed by the multiplication helper's recorded known-true hypothesis. -/
theorem logic_complexRationalp_t_of_inTs {m : Int} {v : SExpr}
    (hm : tsSubsumedM m 64 = true) (hv : InTs m v) :
    Logic.complexRationalp v = .t := by
  unfold Logic.complexRationalp
  split
  · rfl
  · rename_i hc
    have hf : Logic.toBool (Logic.complexRationalp v) = false := by
      simp only [Logic.complexRationalp, if_neg hc]
      rfl
    exact False.elim (inTs_disjoint_absurd (by decide)
      (inTs_weaken hm hv) (inTs_complexRationalp_false hf))

/-- Component projections have rational range even outside numeric guards.
The strict multiplication helper records both recognizer queries. -/
theorem inTs_realpart (v : SExpr) : InTs 63 (Logic.realpart v) := by
  apply inTs_rationalp_true
  cases v with
  | atom a => cases a with
    | number n => cases n with
      | complex r _ _ =>
        simp only [Logic.realpart, Number.fromRat]
        split <;> rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

theorem inTs_imagpart (v : SExpr) : InTs 63 (Logic.imagpart v) := by
  apply inTs_rationalp_true
  cases v with
  | atom a => cases a with
    | number n => cases n with
      | complex _ i _ =>
        simp only [Logic.imagpart, Number.fromRat]
        split <;> rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

/-- A proved complex mask exposes the nonzero imaginary component. -/
theorem imag_num_ne_zero_of_inTs_complex {v : SExpr} (hv : InTs 64 v) :
    (Logic.numberParts v).2.num ≠ 0 := by
  have hc := logic_complexRationalp_t_of_inTs (by decide : tsSubsumedM 64 64 = true) hv
  cases v with
  | nil | cons _ _ => simp [Logic.complexRationalp, Logic.isComplex, SExpr.t] at hc
  | atom a => cases a with
    | number n => cases n with
      | complex _ _ hi => exact hi
      | _ => simp [Logic.complexRationalp, Logic.isComplex, SExpr.t] at hc
    | _ => simp [Logic.complexRationalp, Logic.isComplex, SExpr.t] at hc

theorem inTs_mkParts_complex (r i : Rat) (hi : i.num ≠ 0) :
    InTs 64 (Logic.mkParts r i) := by
  simp only [Logic.mkParts, Number.fromParts, hi, ↓reduceDIte, InTs, tsIndex_complex]
  decide

/-- The strict helper's Subgoal 9.18 records COMPLEX-RATIONALP(X1 + Y).
Adding a rational leaves a complex value's imaginary component unchanged. -/
theorem inTs_plus_complex_rat {a b : SExpr} (ha : InTs 64 a) (hb : InTs 63 b) :
    InTs 64 (Logic.plus a b) := by
  rw [Logic.plus_parts, Logic.numberParts_of_not_complex b (not_complex_of_inTs_rational hb)]
  simp only [Rat.add_zero]
  exact inTs_mkParts_complex _ _ (imag_num_ne_zero_of_inTs_complex ha)

/-- The actual COMPLEX-RATIONALP(* X1 Y) query uses a complex factor and
a nonzero rational factor. Imaginary-part multiplication preserves the
complex bit. This is a primitive type cell, not an order theorem. -/
theorem inTs_times_complex_rat {a b : SExpr} (ha : InTs 64 a) (hb : InTs 62 b) :
    InTs 64 (Logic.times a b) := by
  have hb63 : InTs 63 b := inTs_weaken (by decide) hb
  have hbNum := logic_acl2Numberp_t_of_inTs (by decide : tsSubsumedM 62 127 = true) hb
  have hbNe : Logic.acl2Numberp b ≠ .nil := by rw [hbNum]; decide
  have hbReal := not_complex_of_inTs_rational hb63
  have hrep := Logic.mkParts_numberParts b
  rw [Logic.numberParts_of_not_complex b hbReal, Logic.fix_of_number b hbNe] at hrep
  have hq : Logic.rationalValue b ≠ 0 := by
    intro hz
    rw [hz] at hrep
    have hzero : b = .atom (.number (.int 0)) := hrep.symm
    have impossible : InTs 62 (.atom (.number (.int 0))) := hzero ▸ hb
    exact (by unfold InTs; decide : ¬ InTs 62 (.atom (.number (.int 0)))) impossible
  have hi := imag_num_ne_zero_of_inTs_complex ha
  have hin : (Logic.numberParts a).2 ≠ 0 := fun h => hi (congrArg Rat.num h)
  have hp : ((Logic.numberParts a).2 * Logic.rationalValue b).num ≠ 0 := fun h =>
    (mul_ne_zero hin hq) (Rat.num_eq_zero.mp h)
  rw [Logic.times_parts, Logic.numberParts_of_not_complex b hbReal]
  simp only [Rat.mul_zero, Rat.zero_add]
  exact inTs_mkParts_complex _ _ hp

end ACL2.Replay
