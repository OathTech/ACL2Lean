import ACL2Lean.Replay.Lemmas.TsAlgebra

namespace ACL2.Replay
open ACL2

/-- The value-level true-list corollary carried by the existing TP registry.
EVENS supplies it by checked admission replay, never by its return mask. -/
theorem inTs_of_trueListp_t {v : SExpr} (h : Logic.trueListp v = .t) : InTs 1152 v := by
  cases v with
  | nil => unfold InTs; decide
  | atom a => simp [Logic.trueListp, SExpr.t] at h
  | cons a b => simp only [InTs, tsIndex_cons, h]; decide

theorem trueListp_t_of_inTs {v : SExpr} (h : InTs 1152 v) : Logic.trueListp v = .t := by
  cases v with
  | nil => rfl
  | cons a b =>
    apply (Logic.trueListp_ne_nil_iff _).mp
    intro hn
    simp only [InTs, tsIndex_cons, hn] at h
    exact (by decide : ¬ (tsMember 1152 11 = true)) h
  | atom a =>
    exfalso
    cases a with
    | number n => cases n with
      | int z => simp only [InTs, tsIndex_int] at h; split_ifs at h <;> contradiction
      | rational z d hc => simp only [InTs, tsIndex_rat] at h; split_ifs at h <;> contradiction
      | complex r i hi => exact (by unfold InTs; simp only [tsIndex_complex]; decide : ¬ InTs 1152 (.atom (.number (.complex r i hi)))) h
    | symbol s => simp only [InTs, tsIndex_symbol] at h; split_ifs at h <;> contradiction
    | keyword k => exact (by simp only [InTs, tsIndex_keyword]; decide : ¬ InTs 1152 (.atom (.keyword k))) h
    | string s => exact (by simp only [InTs, tsIndex_string]; decide : ¬ InTs 1152 (.atom (.string s))) h
    | char c => exact (by simp only [InTs, tsIndex_char]; decide : ¬ InTs 1152 (.atom (.char c))) h

theorem inTs_cons_proper (a : SExpr) {b : SExpr} (hb : InTs 1152 b) :
    InTs 1024 (.cons a b) := by
  have ht := trueListp_t_of_inTs hb
  simp only [InTs, tsIndex_cons, Logic.trueListp_cons, ht]
  decide

theorem inTs_cons_range (a b : SExpr) : InTs 3072 (.cons a b) :=
  inTs_consp_true (by rfl)
end ACL2.Replay
