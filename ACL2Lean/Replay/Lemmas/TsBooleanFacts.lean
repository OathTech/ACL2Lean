import ACL2Lean.Replay.Lemmas.TsAlgebra

namespace ACL2.Replay
open ACL2

/-- A local IF test's own value inhabits ACL2's non-NIL partition. -/
theorem inTs_toBool_true {v : SExpr} (h : Logic.toBool v = true) : InTs (-129) v := by
  have hn := (Logic.toBool_eq_true v).mp h
  match v with
  | .nil => exact False.elim (hn rfl)
  | .cons a d => simp only [InTs, tsIndex_cons]; split_ifs <;> decide
  | .atom (.symbol s) => simp only [InTs, tsIndex_symbol]; split_ifs <;> decide
  | .atom (.number (.int n)) => simp only [InTs, tsIndex_int]; split_ifs <;> decide
  | .atom (.number (.rational n d hc)) =>
    simp only [InTs, tsIndex_rat]; split_ifs <;> decide
  | .atom (.number (.complex _ _ _)) => change tsMember (-129) 6 = true; decide
  | .atom (.keyword _) => change tsMember (-129) 9 = true; decide
  | .atom (.string _) => change tsMember (-129) 12 = true; decide
  | .atom (.char _) => change tsMember (-129) 13 = true; decide

theorem inTs_toBool_false {v : SExpr} (h : Logic.toBool v = false) : InTs 128 v := by
  have hn := (Logic.toBool_eq_false v).mp h
  subst v
  unfold InTs
  decide

/-- The primitive NOT result is always in the two Boolean cells. -/
theorem inTs_not (v : SExpr) : InTs 384 (Logic.not v) := by
  unfold Logic.not InTs
  split <;> decide

theorem inTs_of_boolean_range {v : SExpr} (h : v = .t ∨ v = .nil) : InTs 384 v := by
  rcases h with h | h <;> subst v <;> unfold InTs <;> decide

theorem boolean_range_of_inTs {v : SExpr} (h : InTs 384 v) : v = .nil ∨ v = .t := by
  match v with
  | .nil => exact Or.inl rfl
  | .atom (.symbol s) =>
    simp only [InTs, tsIndex_symbol] at h
    split_ifs at h with hs
    · exact Or.inr (eq_of_beq hs)
    · exfalso; revert h; decide
  | .cons a d =>
    simp only [InTs, tsIndex_cons] at h
    split_ifs at h <;> (exfalso; revert h; decide)
  | .atom (.number (.int n)) =>
    simp only [InTs, tsIndex_int] at h
    split_ifs at h <;> (exfalso; revert h; decide)
  | .atom (.number (.rational n d hc)) =>
    simp only [InTs, tsIndex_rat] at h
    split_ifs at h <;> (exfalso; revert h; decide)
  | .atom (.number (.complex _ _ _)) | .atom (.keyword _) |
    .atom (.string _) | .atom (.char _) =>
    simp only [InTs, tsIndex] at h
    exfalso; revert h; decide

theorem equal_t_of_inTs {v : SExpr} (h : InTs 384 v) : Logic.equal v .t = v := by
  rcases boolean_range_of_inTs h with hv | hv <;> subst v <;> rfl

theorem ne_nil_of_inTs {m : Int} {v : SExpr}
    (hn : tsMember m 7 = false) (h : InTs m v) : v ≠ SExpr.nil := by
  intro hv
  subst v
  simp only [InTs, tsIndex_nil, hn, Bool.false_eq_true] at h

/-- The IF collector records mask zero for an unreachable addressed branch.
Its ruling test contradicts the same test's value in the outer context. -/
theorem bool_value_conflict {b : Bool} (ht : b = true) (hf : b = false) : False :=
  Bool.noConfusion (ht.symm.trans hf)

end ACL2.Replay
