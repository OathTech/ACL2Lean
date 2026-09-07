import ACL2Lean.Replay.Lemmas.TsNumericFacts
import ACL2Lean.NumericEquality
import ACL2Lean.NumericComponents

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
  rw [Logic.rationalp_realpart]
  rfl

theorem inTs_imagpart (v : SExpr) : InTs 63 (Logic.imagpart v) := by
  apply inTs_rationalp_true
  rw [Logic.rationalp_imagpart]
  rfl

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

/-- The IMAGPART query in the recorded elimination restriction has
child mask 64 and result mask 62: a genuine complex has nonzero imaginary part. -/
theorem inTs_imagpart_complex {v : SExpr} (hv : InTs 64 v) :
    InTs 62 (Logic.imagpart v) := by
  have hn : Logic.imagpart v ≠ .atom (.number (.int 0)) := by
    intro hz
    have hc := congrArg (fun z => (Logic.numberParts z).1.num) hz
    rw [Logic.numberParts_imagpart] at hc
    exact imag_num_ne_zero_of_inTs_complex hv hc
  have he := (Logic.equal_nil_iff _ _).mpr hn
  exact inTs_inter2 (by decide : tsInter2Subsumed 63 (-2) 62 = true)
    (inTs_imagpart v) (inTs_not_zero ((Logic.toBool_eq_false _).mpr he))

/-- The executed IMAGPART query of a rational argument returns the
singleton zero cell in REALPART-WHEN-RATIONALP's elimination record. -/
theorem inTs_imagpart_rational {v : SExpr} (h : InTs 63 v) :
    InTs 1 (Logic.imagpart v) := by
  have hc := not_complex_of_inTs_rational h
  have hz : InTs 1 (.atom (.number (.int 0))) := by unfold InTs; decide
  cases v with
  | nil | cons _ _ => exact hz
  | atom a => cases a with
    | number n => cases n with
      | complex _ _ _ => simp [Logic.isComplex] at hc
      | _ => exact hz
    | _ => exact hz

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

/-- The elimination child records the rational component on the left.
This is the same primitive sum cell through addition's core commutativity. -/
theorem inTs_plus_rat_complex {a b : SExpr} (ha : InTs 63 a) (hb : InTs 64 b) :
    InTs 64 (Logic.plus a b) := by
  rw [Logic.plus_comm]
  exact inTs_plus_complex_rat hb ha

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
