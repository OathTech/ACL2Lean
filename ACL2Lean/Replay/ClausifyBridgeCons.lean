/-
  Replay/ClausifyBridgeCons — the CONS-CONS clausify-expansion registry
  identity (equal-descent restructure arc; module-size norm split from
  ClausifyBridge).
-/
import ACL2Lean.Replay.ClausifyBridge

namespace ACL2.Replay

open ACL2

/-- The CONS-CONS specialization of the decomposition (the ground-zero
    CONS-EQUAL rewrite's shape): both sides are conses, so the CONSP guard
    and the CAR/CDR projections evaluate away. -/
private theorem equal_cons_cons_decomp (x1 y1 x2 y2 : SExpr) :
    Logic.equal (SExpr.cons x1 y1) (SExpr.cons x2 y2)
      = cond (Logic.toBool (Logic.equal x1 x2)) (Logic.equal y1 y2)
          SExpr.nil := by
  by_cases hx : x1 = x2
  · subst hx
    by_cases hy : y1 = y2
    · subst hy; simp [Logic.equal]
    · have hc : SExpr.cons x1 y1 ≠ SExpr.cons x1 y2 := by
        intro h; injection h with _ h2; exact hy h2
      simp [Logic.equal, beq_eq_false_iff_ne.mpr hy,
            beq_eq_false_iff_ne.mpr hc]
  · have hc : SExpr.cons x1 y1 ≠ SExpr.cons x2 y2 := by
      intro h; injection h with h1 _; exact hx h1
    simp [Logic.equal, beq_eq_false_iff_ne.mpr hx,
          beq_eq_false_iff_ne.mpr hc]

/-- `(EQUAL (CONS x1 y1) (CONS x2 y2)) ⇒
    (IF (EQUAL x1 x2) (EQUAL y1 y2) 'NIL)`: the CONS-CONS expansion
    preserves the lift — the ground-zero `(:REWRITE CONS-EQUAL)` fired as
    a clausify expansion (equal-descent restructure arc,
    ORDEREDP-WHEN-BNEXT-CONSTANT Subgoal *1/4.2'; the driver validates
    the target shape verbatim and the record cites the rune). -/
theorem dpLiftF_equal_cons_cons_expand {vars : List (Symbol × SExpr)}
    {opq : List (SExpr × SExpr)} (hwf : dpOpqWF opq = true)
    (x1 y1 x2 y2 : SExpr) :
    dpLiftF vars opq (equalAppCB (consAppCB x1 y1) (consAppCB x2 y2))
      = dpLiftF vars opq
          (ifT (equalAppCB x1 x2) (equalAppCB y1 y2) quoteNil) := by
  have hqn : dpLiftF vars opq quoteNil = some SExpr.nil := dpLiftF_quote hwf _
  have hEo := dpLiftF_prim2 (vars := vars) hwf "EQUAL" (consAppCB x1 y1)
    (consAppCB x2 y2) (by decide) (by decide) (by decide) (by decide)
  have hC1 := dpLiftF_prim2 (vars := vars) hwf "CONS" x1 y1
    (by decide) (by decide) (by decide) (by decide)
  have hC2 := dpLiftF_prim2 (vars := vars) hwf "CONS" x2 y2
    (by decide) (by decide) (by decide) (by decide)
  have hEx := dpLiftF_prim2 (vars := vars) hwf "EQUAL" x1 x2
    (by decide) (by decide) (by decide) (by decide)
  have hEy := dpLiftF_prim2 (vars := vars) hwf "EQUAL" y1 y2
    (by decide) (by decide) (by decide) (by decide)
  have hIf := dpLiftF_ifT (vars := vars) (opq := opq) hwf
    (equalAppCB x1 x2) (equalAppCB y1 y2) quoteNil
  have hCB1 : ∀ a b : SExpr, callBuiltin "CONS" [a, b]
      = some (SExpr.cons a b) := fun _ _ => rfl
  have hCB5 : ∀ a b : SExpr, callBuiltin "EQUAL" [a, b]
      = some (Logic.equal a b) := fun _ _ => rfl
  simp only [hIf, hEo, hC1, hC2, hEx, hEy, hqn, hCB1, hCB5]
  cases hx1 : dpLiftF vars opq x1 <;> cases hy1 : dpLiftF vars opq y1 <;>
    cases hx2 : dpLiftF vars opq x2 <;> cases hy2 : dpLiftF vars opq y2 <;>
      simp only [Option.bind, equal_cons_cons_decomp]

/-! ### Expansion DETAIL-step recipes (2e, design ruled 2026-08-10)

`expand-and-or` re-runs abbreviation rewriting on the expanded body and
the fork records those steps as the expansion's detail chain. The two
recorded classes both preserve the LIFT VALUE outright — strictly
stronger than the approved nilEquiv weakening, which remains the
designed fallback for an IFF collapse over a NON-boolean carrier (a
loud driver frontier until a witness demands it). -/

/-- equal-self detail step: `(EQUAL u u) ⇒ 'T` preserves the lift GIVEN
    `u` lifts — the step DISCARDS `u`, so liftability is a side condition
    (the driver decides it on the reflected closed bundle). -/
theorem dpLiftF_equal_self {vars : List (Symbol × SExpr)}
    {opq : List (SExpr × SExpr)} (hwf : dpOpqWF opq = true) (u : SExpr)
    (hu : (dpLiftF vars opq u).isSome = true) :
    dpLiftF vars opq (equalAppCB u u) = dpLiftF vars opq quoteT := by
  have hqt : dpLiftF vars opq quoteT = some SExpr.t := dpLiftF_quote hwf _
  have hE := dpLiftF_prim2 (vars := vars) hwf "EQUAL" u u
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨uv, huv⟩ := Option.isSome_iff_exists.mp hu
  rw [hE, huv, hqt]
  show callBuiltin "EQUAL" [uv, uv] = some SExpr.t
  show some (Logic.equal uv uv) = some SExpr.t
  rw [Logic.equal_self]

/-- Congruence at the direct IF branches (detail steps carry no `:PATH`;
    the driver's consumption matches the whole term or a direct branch). -/
theorem dpLiftF_ifT_congr {vars : List (Symbol × SExpr)}
    {opq : List (SExpr × SExpr)} (hwf : dpOpqWF opq = true)
    (c : SExpr) {b b' e e' : SExpr}
    (hb : dpLiftF vars opq b = dpLiftF vars opq b')
    (he : dpLiftF vars opq e = dpLiftF vars opq e') :
    dpLiftF vars opq (ifT c b e) = dpLiftF vars opq (ifT c b' e') := by
  rw [dpLiftF_ifT hwf, dpLiftF_ifT hwf, hb, he]

/-- if-iff detail step over a BOOLEAN carrier:
    `(IF (EQUAL a b) 'T 'NIL) ⇒ (EQUAL a b)` is a VALUE equality —
    `Logic.equal` is t/nil-valued, so the `cond (toBool ·) t nil` wrapper
    is the identity on it. This is why the recorded `:EQUIV IFF` collapse
    needs no relation weakening on this class. -/
theorem dpLiftF_if_t_nil_equal {vars : List (Symbol × SExpr)}
    {opq : List (SExpr × SExpr)} (hwf : dpOpqWF opq = true) (a b : SExpr) :
    dpLiftF vars opq (ifT (equalAppCB a b) quoteT quoteNil)
      = dpLiftF vars opq (equalAppCB a b) := by
  have hqt : dpLiftF vars opq quoteT = some SExpr.t := dpLiftF_quote hwf _
  have hqn : dpLiftF vars opq quoteNil = some SExpr.nil := dpLiftF_quote hwf _
  have hE := dpLiftF_prim2 (vars := vars) hwf "EQUAL" a b
    (by decide) (by decide) (by decide) (by decide)
  rw [dpLiftF_ifT hwf, hqt, hqn, hE]
  cases ha : dpLiftF vars opq a with
  | none => rfl
  | some av =>
    cases hb : dpLiftF vars opq b with
    | none => rfl
    | some bv =>
      show some (cond (Logic.toBool (Logic.equal av bv)) SExpr.t SExpr.nil)
        = some (Logic.equal av bv)
      by_cases h : av = bv
      · subst h; rw [Logic.equal_self]; rfl
      · have hn : Logic.equal av bv = SExpr.nil := by
          simp [Logic.equal, beq_eq_false_iff_ne.mpr h]
        rw [hn]; rfl

/-- `clausifyPure_sound` over a RECORDED clause that is a mem-sublist of
    the recompute (2e + item E: `add-literal`'s member-term drop can
    remove a COMMUTED duplicate the exact-dup `dedupClause` cannot see —
    ORDEREDP-WHEN-BNEXT-CONSTANT *1/4.1.3''s `(NOT (EQUAL X1 X3))` next
    to the kept `(NOT (EQUAL X3 X1))`). The driver accepts the recorded
    clause only when removing the RECORDED `(:DEDUP-DROP …)` literals
    from the recompute reproduces it; the PROOF needs only membership —
    a true sub-disjunction trues the full one. -/
theorem clausifyPure_sound_sub (w : World) (env : Env)
    {vars : List (Symbol × SExpr)} {opq : List (SExpr × SExpr)}
    (hvars : ∀ q ∈ vars,
      ∃ N, ∀ f ≥ N, evalOpt f w env (.atom (.symbol q.1)) = some q.2)
    (hopq : ∀ p ∈ opq, ∃ N, ∀ f ≥ N, evalOpt f w env p.1 = some p.2)
    (hns : dpNoShadow w) (hwf : dpOpqWF opq = true) :
    ∀ t pos (rec : List SExpr),
      (rec.all (fun l => (clausifyPure t pos).contains l)) = true →
      (dpLiftF vars opq t).isSome →
      EvTrue w env (disjoinTerm rec) →
      ClausifyGoal w env t pos := by
  intro t pos rec hsub hsome hrec
  have sound := dpLiftF_sound w env vars opq hvars hopq hns
  have litconvs : ∀ l ∈ clausifyPure t pos,
      ∃ vl, ∃ N, ∀ f ≥ N, evalOpt f w env l = some vl :=
    fun l hl => by
      obtain ⟨vl, hvl⟩ :=
        Option.isSome_iff_exists.mp (clausifyPure_lifts hwf t pos hsome l hl)
      exact ⟨vl, sound l vl hvl⟩
  refine clausifyPure_sound w env hvars hopq hns hwf t pos hsome ?_
  refine evtrue_disjoin_of_sublist w env _ _ litconvs ?_ hrec
  intro l hl
  have hc := List.all_eq_true.mp hsub l hl
  exact List.mem_of_elem_eq_true hc

end ACL2.Replay
