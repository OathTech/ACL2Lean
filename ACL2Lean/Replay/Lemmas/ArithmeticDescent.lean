import ACL2Lean.ValueCount

/-! Arithmetic decreases of ACL2-COUNT, used only after the driver matches
an emitted admission obligation and obtains its recorded ruling facts. -/

namespace ACL2.Replay
open ACL2

private theorem nfix_ne_zero_int {b : SExpr}
    (h : Logic.toBool (Logic.equal (Logic.nfix b) (.atom (.number (.int 0)))) = false) :
    ∃ j : Int, b = .atom (.number (.int j)) ∧ 0 < j := by
  cases b with
  | atom a =>
    cases a with
    | number n =>
      cases n with
      | int j =>
        by_cases hj : 0 ≤ j
        · refine ⟨j, rfl, ?_⟩
          have hn : j ≠ 0 := by
            intro hz
            subst j
            simp [Logic.nfix, Logic.equal, Logic.toBool] at h
          omega
        · simp [Logic.nfix, hj, Logic.equal, Logic.toBool] at h
      | rational _ _ _ | complex _ _ _ =>
        simp [Logic.nfix, Logic.equal, Logic.toBool] at h
    | _ => simp [Logic.nfix, Logic.equal, Logic.toBool] at h
  | _ => simp [Logic.nfix, Logic.equal, Logic.toBool] at h

private theorem ifix_ge_pos_int {a : SExpr} {j : Int} (hj : 0 < j)
    (h : Logic.toBool (Logic.lt (Logic.ifix a) (.atom (.number (.int j)))) = false) :
    ∃ i : Int, a = .atom (.number (.int i)) ∧ j ≤ i := by
  cases a with
  | atom b =>
    cases b with
    | number n =>
      cases n with
      | int i =>
        refine ⟨i, rfl, ?_⟩
        by_cases hij : i < j
        · simp [Logic.ifix, Logic.toRat, Logic.toBool, hij] at h
        · omega
      | rational _ _ _ | complex _ _ _ =>
        simp [Logic.ifix, Logic.toRat, Logic.toBool, hj] at h
    | _ => simp [Logic.ifix, Logic.toRat, Logic.toBool, hj] at h
  | _ => simp [Logic.ifix, Logic.toRat, Logic.toBool, hj] at h

/-- Subtracting a positive integer without crossing zero decreases ACL2-COUNT.
    The completion-aware hypotheses are exactly the two ruling tests in
    NONNEGATIVE-INTEGER-QUOTIENT's emitted admission clause. -/
theorem valueCount_sub_lt_of_rulers {a b : SExpr}
    (hb : Logic.toBool (Logic.equal (Logic.nfix b) (.atom (.number (.int 0)))) = false)
    (ha : Logic.toBool (Logic.lt (Logic.ifix a) b) = false) :
    (Logic.plus a (Logic.neg b)).valueCount < a.valueCount := by
  obtain ⟨j, rfl, hj⟩ := nfix_ne_zero_int hb
  obtain ⟨i, rfl, hi⟩ := ifix_ge_pos_int hj ha
  simp [Logic.neg, Logic.toRat, Logic.mkNumber, SExpr.valueCount, Number.valueCount]
  omega

end ACL2.Replay
