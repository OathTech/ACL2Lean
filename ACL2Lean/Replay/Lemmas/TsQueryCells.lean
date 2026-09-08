import ACL2Lean.Replay.Lemmas.TsNumericFacts
import ACL2Lean.Replay.Lemmas.TsBooleanFacts
import ACL2Lean.NumericPositive
import ACL2Lean.NumericEquality
import ACL2Lean.NumericComplexView

namespace ACL2.Replay
open ACL2

/-- TYPE-SET-REC's unbound-variable return, over the complete basic partition. -/
theorem inTs_unknown (v : SExpr) : InTs (-1) v := by
  unfold InTs
  have hi := tsIndex_lt v
  generalize tsIndex v = i at *
  interval_cases i <;> decide

theorem equal_zero_t_of_inTs {v : SExpr} (h : InTs 1 v) :
    Logic.equal v (.atom (.number (.int 0))) = .t := by
  rw [zero_of_inTs1 h]
  rfl

/-- The executed multiplication query in the strict helper has a nonnumeric
left operand. ACL2's primitive completion makes the product zero. -/
theorem inTs_times_nonnumber_left {a : SExpr} (b : SExpr) (ha : InTs (-128) a) :
    InTs 1 (Logic.times a b) := by
  have hn := logic_acl2Numberp_nil_of_ts_disjoint
    (by decide : tsDisjointM (-128) 127 = true) ha
  rw [Logic.times_comm, Logic.times_nonnumber_right b a hn]
  unfold InTs
  decide

/-- The other executed product query has a singleton-zero right child. -/
theorem inTs_times_singleton_zero_right (a : SExpr) {b : SExpr} (hb : InTs 1 b) :
    InTs 1 (Logic.times a b) := by
  rw [zero_of_inTs1 hb]
  exact inTs_times_zero_right a

/-- The negative-rational restriction excludes the false comparison cell. -/
theorem lt_zero_of_inTs {v : SExpr} (h : InTs 48 v) :
    Logic.lt v (.atom (.number (.int 0))) = .t := by
  rcases logic_lt_range v (.atom (.number (.int 0))) with ht | hf
  · exact ht
  · exact False.elim (inTs_disjoint_absurd
      (by decide : tsDisjointM 48 (-49) = true) h
      (inTs_lt_zero_false ((Logic.toBool_eq_false _).mpr hf)))

/-- Excluding the singleton zero bit proves the recorded nonzero
restriction; the emitted mask selects this primitive conversion. -/
theorem equal_zero_nil_of_inTs {m : Int} {v : SExpr}
    (hm : tsDisjointM m 1 = true) (hv : InTs m v) :
    Logic.equal v (.atom (.number (.int 0))) = .nil := by
  apply (Logic.equal_nil_iff _ _).mpr
  intro hz
  subst v
  exact inTs_disjoint_absurd hm hv (by unfold InTs; decide)

/-- The recorded BINARY-+ table cell for two positive rationals. Combine
the primitive rational range and POSITIVE addition law; no arithmetic is
re-solved at the hypothesis-query consumer. -/
theorem inTs_plus_positive_rat {a b : SExpr} (ha : InTs 14 a) (hb : InTs 14 b) :
    InTs 14 (Logic.plus a b) := by
  have hrat := inTs_plus_rat
    (inTs_weaken (by decide : tsSubsumedM 14 63 = true) ha)
    (inTs_weaken (by decide : tsSubsumedM 14 63 = true) hb)
  have positive {v : SExpr} (hv : InTs 14 v) :
      Logic.lt (.atom (.number (.int 0))) v ≠ .nil := by
    rw [zero_lt_of_inTs (by decide : tsSubsumedM 14 14 = true) hv]
    decide
  have hsign := inTs_zero_lt_true ((Logic.toBool_eq_true _).mpr
    (Logic.positiveAdd a b (positive ha) (positive hb)))
  exact inTs_inter2 (by decide : tsInter2Subsumed 63 78 14 = true) hrat hsign

/-- The next executed addition query in the strict helper permits zero in
the right operand. Split that primitive cell and reuse positive addition. -/
theorem inTs_plus_positive_nonneg_rat {a b : SExpr}
    (ha : InTs 14 a) (hb : InTs 15 b) : InTs 14 (Logic.plus a b) := by
  by_cases hz : b = .atom (.number (.int 0))
  · subst b
    rw [Logic.plus_comm, Logic.plus_zero_fix, Logic.fix_of_number a]
    · exact ha
    · rw [logic_acl2Numberp_t_of_inTs (by decide : tsSubsumedM 14 127 = true) ha]
      decide
  · have hne := (Logic.equal_nil_iff _ _).mpr hz
    have hb14 := inTs_inter2 (by decide : tsInter2Subsumed 15 (-2) 14 = true)
      hb (inTs_not_zero ((Logic.toBool_eq_false _).mpr hne))
    exact inTs_plus_positive_rat ha hb14

/-- The singleton NIL type cell, consumed by an emitted NOT query. -/
theorem nil_of_inTs128 {v : SExpr} (h : InTs 128 v) : v = .nil := by
  rcases boolean_range_of_inTs (inTs_weaken (show tsSubsumedM 128 384 = true by decide) h) with hv | hv
  · exact hv
  · subst v
    exact absurd h (by unfold InTs; decide)

/-- The singleton T cell, consumed by a recorded positive IF query. -/
theorem t_of_inTs256 {v : SExpr} (h : InTs 256 v) : v = .t := by
  rcases boolean_range_of_inTs (inTs_weaken (show tsSubsumedM 256 384 = true by decide) h) with hv | hv
  · subst v
    exact absurd h (by unfold InTs; decide)
  · exact hv

theorem inTs_of_eq_t {v : SExpr} (h : v = .t) : InTs 256 v := by
  rw [h]; unfold InTs; decide

theorem inTs_of_eq_nil {v : SExpr} (h : v = .nil) : InTs 128 v := by
  rw [h]; unfold InTs; decide

/-- A selected strict reverse bound excludes this primitive comparison.
This includes lexicographic complex order and numeric completion. -/
theorem logic_lt_nil_of_reverse_t {a b : SExpr} (h : Logic.lt b a = .t) :
    Logic.lt a b = .nil := by
  have hb : (Logic.numberParts b).1 < (Logic.numberParts a).1 ∨
      ((Logic.numberParts b).1 = (Logic.numberParts a).1 ∧
        (Logic.numberParts b).2 < (Logic.numberParts a).2) := by
    by_contra hn
    rw [Logic.lt_parts, if_neg hn] at h
    cases h
  rw [Logic.lt_parts]
  split
  · rename_i ha
    rcases ha with ha | ⟨he, ha⟩ <;>
      rcases hb with hb | ⟨hf, hb⟩ <;> exfalso <;> linarith
  · rfl

/-- The reciprocal cell in the recorded FC hypothesis query: a nonnegative
integer gives zero, one, or a positive proper ratio. This proves primitive
semantics; the recorded call and child masks select its application. -/
theorem inTs_reciprocal_nonneg_int {v : SExpr} (h : InTs 7 v) :
    InTs 11 (Logic.reciprocal v) := by
  obtain ⟨n, rfl⟩ := int_of_inTs23 (inTs_weaken (show tsSubsumedM 7 23 = true by decide) h)
  have hn : 0 ≤ n := by
    by_contra hn
    have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    have h2 : ¬ 1 < n := by omega
    simp only [InTs, tsIndex_int, if_neg h0, if_neg h1, if_neg h2] at h
    contradiction
  simp only [Logic.reciprocal, Logic.div, Logic.isComplex, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte, Logic.toRat, Int.one_mul, Nat.one_mul]
  by_cases hz : n = 0
  · subst n; unfold InTs; decide
  simp only [beq_iff_eq, if_neg hz, if_neg (show ¬ n < 0 by omega)]
  unfold Logic.mkNumber
  split
  · unfold InTs; decide
  · dsimp only
    split <;> norm_num [InTs, tsIndex, tsMember] <;> decide

end ACL2.Replay
