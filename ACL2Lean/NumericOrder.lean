import ACL2Lean.NumericLemmas

namespace ACL2.Logic

/-- Equality cancellation in the rational components of primitive addition. -/
theorem rat_add_right_eq (a b c : Rat) : a + c = b + c ↔ a = b :=
  ⟨Rat.add_right_cancel c, fun h => congrArg (· + c) h⟩

theorem rat_add_left_eq (a b c : Rat) : c + a = c + b ↔ a = b :=
  ⟨Rat.add_left_cancel c, fun h => congrArg (c + ·) h⟩

theorem lt_int_int (a b : Int) :
    lt (.atom (.number (.int a))) (.atom (.number (.int b))) =
      if a < b then .t else .nil := by simp [lt, toRat]

theorem lt_parts (a b : SExpr) :
    lt a b = if (numberParts a).1 < (numberParts b).1 ∨
      ((numberParts a).1 = (numberParts b).1 ∧ (numberParts a).2 < (numberParts b).2)
      then .t else .nil := by
  by_cases h : (isComplex a || isComplex b) = true
  · simp only [lt, h, ↓reduceIte]
  · have ha : isComplex a = false := by cases h1 : isComplex a <;> simp_all
    have hb : isComplex b = false := by cases h1 : isComplex b <;> simp_all
    have hn := rationalValue_num_den a
    have hm := rationalValue_num_den b
    have he : (rationalValue a < rationalValue b) ↔
        (toRat a).1 * ((toRat b).2 : Int) < (toRat b).1 * ((toRat a).2 : Int) := by
      rw [Rat.lt_iff, hn.1, hn.2, hm.1, hm.2]
    simp only [lt, ha, hb, Bool.false_or, Bool.false_eq_true, ↓reduceIte, numberParts_of_not_complex a ha,
      numberParts_of_not_complex b hb, Rat.lt_irrefl, and_false, or_false]
    simp only [he]

/-- A strict unit shift in the real component separates both values,
including complex values and ACL2's nonnumber completion. -/
theorem lt_of_not_lt_sub_one (x y : SExpr)
    (h : lt (plus (.atom (.number (.int (-1)))) y) x = .nil) :
    lt x y = .t := by
  have hparts : numberParts (plus (.atom (.number (.int (-1)))) y) =
      (-1 + (numberParts y).1, (numberParts y).2) := by
    rw [plus_parts, numberParts_mkParts]
    change ((-1 : Rat) + (numberParts y).1, 0 + (numberParts y).2) = _
    rw [Rat.zero_add]
  rw [lt_parts, hparts] at h
  have hle : (numberParts x).1 ≤ -1 + (numberParts y).1 := by
    apply Rat.not_lt.mp
    intro hg
    rw [if_pos (Or.inl hg)] at h
    cases h
  have hstep : -1 + (numberParts y).1 < (numberParts y).1 := by
    have hneg : (-1 : Rat) < 0 := by decide
    have hsum := (Rat.add_lt_add_right (c := (numberParts y).1)).mpr hneg
    simpa only [Rat.zero_add] using hsum
  have hlt : (numberParts x).1 < (numberParts y).1 :=
    Std.lt_of_le_of_lt hle hstep
  rw [lt_parts, if_pos (Or.inl hlt)]

/-- Chaining a non-strict and a strict primitive comparison, including
ACL2's complex lexicographic order and nonnumber completion. -/
theorem lt_of_not_lt_of_lt (a b c : SExpr)
    (hab : lt b a = .nil) (hbc : lt b c = .t) : lt a c = .t := by
  rw [lt_parts] at hab hbc ⊢
  have hab' : ¬ ((numberParts b).1 < (numberParts a).1 ∨
      ((numberParts b).1 = (numberParts a).1 ∧
        (numberParts b).2 < (numberParts a).2)) := by
    intro h
    rw [if_pos h] at hab
    cases hab
  have hbc' : (numberParts b).1 < (numberParts c).1 ∨
      ((numberParts b).1 = (numberParts c).1 ∧
        (numberParts b).2 < (numberParts c).2) := by
    apply Classical.byContradiction
    intro h
    rw [if_neg h] at hbc
    cases hbc
  have har : (numberParts a).1 ≤ (numberParts b).1 :=
    Rat.not_lt.mp (fun h => hab' (Or.inl h))
  apply if_pos
  rcases hbc' with hr | ⟨hr, hi⟩
  · exact Or.inl (Std.lt_of_le_of_lt har hr)
  · rcases Rat.le_iff_lt_or_eq.mp har with ha | ha
    · exact Or.inl (hr ▸ ha)
    · apply Or.inr
      refine ⟨ha.trans hr, ?_⟩
      have hai : (numberParts a).2 ≤ (numberParts b).2 :=
        Rat.not_lt.mp (fun h => hab' (Or.inr ⟨ha.symm, h⟩))
      exact Std.lt_of_le_of_lt hai hi

theorem lt_of_nonpos_of_pos (a b : SExpr)
    (ha : lt (.atom (.number (.int 0))) a = .nil)
    (hb : lt (.atom (.number (.int 0))) b = .t) : lt a b = .t :=
  lt_of_not_lt_of_lt a (.atom (.number (.int 0))) b ha hb

end ACL2.Logic
