import ACL2Lean.Replay.Lemmas.TsNumericFacts
import ACL2Lean.NumericEquality
import ACL2Lean.NumericComponents
import ACL2Lean.NumericNegation

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

/-- Both component queries in the bootstrap addition proof complete a
nonnumeric value to singleton zero. -/
private theorem inTs_components_nonnumber {v : SExpr} (h : InTs (-128) v) :
    InTs 1 (Logic.realpart v) ∧ InTs 1 (Logic.imagpart v) := by
  have hn := logic_acl2Numberp_nil_of_ts_disjoint
    (by decide : tsDisjointM (-128) 127 = true) h
  have hz : InTs 1 (.atom (.number (.int 0))) := by unfold InTs; decide
  rw [Logic.realpart_nonnumber hn, Logic.imagpart_nonnumber hn]
  exact ⟨hz, hz⟩

theorem inTs_realpart_nonnumber {v : SExpr} (h : InTs (-128) v) :
    InTs 1 (Logic.realpart v) := (inTs_components_nonnumber h).1

theorem inTs_imagpart_nonnumber {v : SExpr} (h : InTs (-128) v) :
    InTs 1 (Logic.imagpart v) := (inTs_components_nonnumber h).2

/-- The bootstrap's executed COMPLEX query has two singleton-zero children. -/
theorem inTs_complex_zero_zero {a b : SExpr} (ha : InTs 1 a) (hb : InTs 1 b) :
    InTs 1 (Logic.complex a b) := by
  rw [zero_of_inTs1 ha, zero_of_inTs1 hb]
  unfold InTs
  decide

theorem inTs_mkParts_complex (r i : Rat) (hi : i.num ≠ 0) :
    InTs 64 (Logic.mkParts r i) := by
  simp only [Logic.mkParts, Number.fromParts, hi, ↓reduceDIte, InTs, tsIndex_complex]
  decide

/-- ACL2's type-set-unary-- preserves the complex-rational bit. The strict
helper's Subgoal 7' needs this cell inside its complex-difference query. -/
theorem inTs_neg_complex {v : SExpr} (h : InTs 64 v) : InTs 64 (Logic.neg v) := by
  rw [Logic.neg_parts]
  apply inTs_mkParts_complex
  intro hz
  have hzero : (Logic.numberParts v).2 = 0 := by
    have hn := congrArg (fun q : Rat => -q) (Rat.num_eq_zero.mp hz)
    simpa only [Rat.neg_neg, Rat.neg_zero] using hn
  exact imag_num_ne_zero_of_inTs_complex h (congrArg Rat.num hzero)

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

/-- Nonzero rational membership, shared by the recorded product and
COMPLEX constructor cells. -/
private theorem rationalValue_ne_zero_of_nonzero_rat {b : SExpr} (hb : InTs 62 b) :
    Logic.rationalValue b ≠ 0 := by
  have hb63 : InTs 63 b := inTs_weaken (by decide) hb
  have hbNum := logic_acl2Numberp_t_of_inTs (by decide : tsSubsumedM 62 127 = true) hb
  have hbNe : Logic.acl2Numberp b ≠ .nil := by rw [hbNum]; decide
  have hbReal := not_complex_of_inTs_rational hb63
  have hrep := Logic.mkParts_numberParts b
  rw [Logic.numberParts_of_not_complex b hbReal, Logic.fix_of_number b hbNe] at hrep
  intro hz
  rw [hz] at hrep
  have hzero : b = .atom (.number (.int 0)) := hrep.symm
  have impossible : InTs 62 (.atom (.number (.int 0))) := hzero ▸ hb
  exact (by unfold InTs; decide : ¬ InTs 62 (.atom (.number (.int 0)))) impossible

/-- The actual COMPLEX-RATIONALP(* X1 Y) query uses a complex factor and
a nonzero rational factor. Imaginary-part multiplication preserves the
complex bit. This is a primitive type cell, not an order theorem. -/
theorem inTs_times_complex_rat {a b : SExpr} (ha : InTs 64 a) (hb : InTs 62 b) :
    InTs 64 (Logic.times a b) := by
  have hbReal := not_complex_of_inTs_rational (inTs_weaken (by decide : tsSubsumedM 62 63 = true) hb)
  have hq := rationalValue_ne_zero_of_nonzero_rat hb
  have hi := imag_num_ne_zero_of_inTs_complex ha
  have hin : (Logic.numberParts a).2 ≠ 0 := fun h => hi (congrArg Rat.num h)
  have hp : ((Logic.numberParts a).2 * Logic.rationalValue b).num ≠ 0 := fun h =>
    (mul_ne_zero hin hq) (Rat.num_eq_zero.mp h)
  rw [Logic.times_parts, Logic.numberParts_of_not_complex b hbReal]
  simp only [Rat.mul_zero, Rat.zero_add]
  exact inTs_mkParts_complex _ _ hp

/-- The executed ADD-DEF-COMPLEX product query allows a zero rational factor.
The nonzero branch reuses the existing complex/rational primitive cell. -/
theorem inTs_times_complex_rat_or_zero {a b : SExpr} (ha : InTs 64 a) (hb : InTs 63 b) :
    InTs 65 (Logic.times a b) := by
  by_cases hz : b = .atom (.number (.int 0))
  · rw [hz]
    exact (congrArg (InTs 65) (Logic.times_zero_right a)).mpr (by unfold InTs; decide)
  · have hb62 : InTs 62 b := inTs_inter2 (by decide : tsInter2Subsumed 63 (-2) 62 = true)
      hb (inTs_not_zero ((Logic.toBool_eq_false _).mpr ((Logic.equal_nil_iff _ _).mpr hz)))
    exact inTs_weaken (by decide) (inTs_times_complex_rat ha hb62)

/-- TYPE-SET-COMPLEX preserves the nonzero rational imaginary cell.
The first argument is completed independently; its executed query is still
an explicit argument of this primitive transfer. -/
theorem inTs_complex_nonzero_rat {a b : SExpr} (_ha : InTs (-1) a) (hb : InTs 62 b) :
    InTs 64 (Logic.complex a b) := by
  apply inTs_mkParts_complex
  intro hzero
  exact rationalValue_ne_zero_of_nonzero_rat hb (Rat.num_eq_zero.mp hzero)

end ACL2.Replay
