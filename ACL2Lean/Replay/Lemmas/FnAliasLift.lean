import ACL2Lean.Replay.Lemmas.FnAlias

/-! # Statement-level fn-alias lifts (Phase 3 2c W3)

The parametric premises at the alias world are RULE-HYPOTHESIS shapes
(`∀ env', ∃N ∀f≥N, evalOpt f w env' ⟦lhs⟧ = evalOpt f w env' ⟦rhs⟧`,
optionally under `EvTrue` hypotheses).  The consumer world proves the
SUBSTITUTED shapes (its own concrete rules — `ORDEREDP-MSORT` for
`ORDEREDP (SSORTFN1 X)` etc.); these lemmas lift them across:

- `evtrue_fnfree_agree_iff` — alias-free `EvTrue` crosses freely (for
  the rule hypotheses' direction reversal);
- `fuelEq_fnalias_lift_const` — a constant-rhs rule fact lifts by pure
  value transport (the quote side supplies the convergence);
- `fuelEq_fnalias_lift` — the general form takes a convergence
  side-fact for the (alias-free) rhs, which the fuel-equality shape
  alone does not carry (supplied by the totality machinery at the
  composition site).

All are compositions of Lemma A / B″ — no new inductions. -/

namespace ACL2.Replay

open ACL2

/-- Alias-free truths cross between the base and alias worlds freely
    (Lemma A is an equality). -/
theorem evtrue_fnfree_agree_iff (names : List Symbol) (w w' : World)
    (hagree : ∀ s : Symbol, names.contains s = false →
      w'.defs.get? s = w.defs.get? s)
    (hw : aliasFreeWorld names w = true)
    (env : Env) (t : SExpr) (hfree : fnFreeTerm names t = true) :
    EvTrue w' env t ↔ EvTrue w env t := by
  constructor <;>
    · intro ⟨N, hN⟩
      refine ⟨N, fun f hf => ?_⟩
      obtain ⟨v, hv, hne⟩ := hN f hf
      refine ⟨v, ?_, hne⟩
      first
        | rw [← evalOpt_fnfree_agree names w w' hagree hw f env t hfree]
        | rw [evalOpt_fnfree_agree names w w' hagree hw f env t hfree]
      exact hv

/-- Lift a CONSTANT-rhs rule fact into the alias world: from
    `substFn t ≐ (QUOTE c)` at the base world conclude `t ≐ (QUOTE c)`
    at the alias world.  The quote side converges by itself, so the
    fuel-equality carries a value and A + B″ transport it. -/
theorem fuelEq_fnalias_lift_const
    (σ : List (Symbol × List Symbol × SExpr)) (w w' : World)
    (hσdef : ∀ e ∈ σ, w'.defs.get? e.1 = some (e.2.1, e.2.2))
    (hσns : ∀ e ∈ σ, (e.1.isNamed "QUOTE" || e.1.isNamed "IF" ||
      e.1.isNamed "LET" || e.1.isNamed "LET*" ||
      e.1.isNamed "LAMBDA") = false)
    (hσws : ∀ e ∈ σ, WellScoped e.2.2 = true)
    (hσcl : ∀ e ∈ σ, (freeVars e.2.2).all (fun x => e.2.1.contains x) = true)
    (hagree : ∀ s : Symbol, (σ.map (·.1)).contains s = false →
      w'.defs.get? s = w.defs.get? s)
    (hw : aliasFreeWorld (σ.map (·.1)) w = true)
    (t c : SExpr) (hws : WellScoped t = true)
    (hsimp : aliasArgsSimple (σ.map (·.1)) t = true)
    (hfree : fnFreeTerm (σ.map (·.1)) (substFnCalls σ t) = true)
    (env : Env)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env (substFnCalls σ t)
      = evalOpt f w env (.cons (.atom (.symbol { name := "QUOTE" }))
          (.cons c .nil))) :
    ∃ N, ∀ f ≥ N, evalOpt f w' env t
      = evalOpt f w' env (.cons (.atom (.symbol { name := "QUOTE" }))
          (.cons c .nil)) := by
  obtain ⟨N, hN⟩ := h
  -- the quote side: some c at any fuel ≥ 1
  have hquote : ∀ (u : World) (f : Nat), f ≥ 1 →
      evalOpt f u env (.cons (.atom (.symbol { name := "QUOTE" }))
        (.cons c .nil)) = some c := by
    intro u f hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rfl
  -- image converges to c at the base world
  have himg : evalOpt (max N 1) w env (substFnCalls σ t) = some c := by
    rw [hN (max N 1) (by omega), hquote w (max N 1) (by omega)]
  -- cross to the alias world on the alias-free image (A)
  have himg' : evalOpt (max N 1) w' env (substFnCalls σ t) = some c := by
    rw [evalOpt_fnfree_agree (σ.map (·.1)) w w' hagree hw _ env _ hfree]
    exact himg
  -- contract inside the alias world (B″)
  obtain ⟨N', hN'⟩ := evalOpt_fncontract_transport σ w' hσdef hσns hσws
    hσcl (max N 1) env t c hws hsimp himg'
  refine ⟨max N' 1, fun f hf => ?_⟩
  rw [hN' f (by omega), hquote w' f (by omega)]

/-- Lift a GENERAL rule fact into the alias world: from
    `substFn lhs ≐ rhs` at the base world (rhs alias-free) plus a
    CONVERGENCE side-fact for rhs, conclude `lhs ≐ rhs` at the alias
    world. -/
theorem fuelEq_fnalias_lift
    (σ : List (Symbol × List Symbol × SExpr)) (w w' : World)
    (hσdef : ∀ e ∈ σ, w'.defs.get? e.1 = some (e.2.1, e.2.2))
    (hσns : ∀ e ∈ σ, (e.1.isNamed "QUOTE" || e.1.isNamed "IF" ||
      e.1.isNamed "LET" || e.1.isNamed "LET*" ||
      e.1.isNamed "LAMBDA") = false)
    (hσws : ∀ e ∈ σ, WellScoped e.2.2 = true)
    (hσcl : ∀ e ∈ σ, (freeVars e.2.2).all (fun x => e.2.1.contains x) = true)
    (hagree : ∀ s : Symbol, (σ.map (·.1)).contains s = false →
      w'.defs.get? s = w.defs.get? s)
    (hw : aliasFreeWorld (σ.map (·.1)) w = true)
    (lhs rhs : SExpr) (hws : WellScoped lhs = true)
    (hsimp : aliasArgsSimple (σ.map (·.1)) lhs = true)
    (hfreeL : fnFreeTerm (σ.map (·.1)) (substFnCalls σ lhs) = true)
    (hfreeR : fnFreeTerm (σ.map (·.1)) rhs = true)
    (env : Env)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env (substFnCalls σ lhs)
      = evalOpt f w env rhs)
    (hconv : ∃ v, ∃ N, ∀ f ≥ N, evalOpt f w env rhs = some v) :
    ∃ N, ∀ f ≥ N, evalOpt f w' env lhs = evalOpt f w' env rhs := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨v, Nr, hr⟩ := hconv
  -- image converges to rhs's value at the base world
  have himg : evalOpt (max N Nr) w env (substFnCalls σ lhs) = some v := by
    rw [hN (max N Nr) (by omega)]
    exact hr (max N Nr) (by omega)
  -- cross both sides to the alias world (A, both alias-free)
  have himg' : evalOpt (max N Nr) w' env (substFnCalls σ lhs) = some v := by
    rw [evalOpt_fnfree_agree (σ.map (·.1)) w w' hagree hw _ env _ hfreeL]
    exact himg
  have hr' : ∀ f ≥ Nr, evalOpt f w' env rhs = some v := fun f hf => by
    rw [evalOpt_fnfree_agree (σ.map (·.1)) w w' hagree hw f env rhs hfreeR]
    exact hr f hf
  -- contract the lhs inside the alias world (B″)
  obtain ⟨N', hN'⟩ := evalOpt_fncontract_transport σ w' hσdef hσns hσws
    hσcl (max N Nr) env lhs v hws hsimp himg'
  refine ⟨max N' Nr, fun f hf => ?_⟩
  rw [hN' f (by omega), hr' f (by omega)]

/-- A defined-fn application converges when its arguments do and its
    body does under the bound (fresh) env — the step reassembly of B″'s
    non-alias arm as a standalone (consumed by the alias-WRAPPER
    totality derivation: an alias fn `(fn X) := (g X)` is total because
    `g` is). -/
theorem conv_defcall (w : World) (env : Env) (s : Symbol)
    (argsExpr : SExpr) (args vals : List SExpr)
    (formals : List Symbol) (body : SExpr) (v : SExpr)
    (hq : s.isNamed "QUOTE" = false) (hif : s.isNamed "IF" = false)
    (hlet : (s.isNamed "LET" || s.isNamed "LET*") = false)
    (hal : argsExpr.toList? = some args)
    (hget : w.defs.get? s = some (formals, body))
    (hlen : formals.length = vals.length)
    (hlenA : args.length = vals.length)
    (hargs : ∀ p ∈ args.zip vals,
      ∃ N, ∀ f ≥ N, evalOpt f w env p.1 = some p.2)
    (hbody : ∃ N, ∀ f ≥ N,
      evalOpt f w (bindArgs formals vals) body = some v) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol s)) argsExpr) = some v := by
  obtain ⟨Nm, hm⟩ := mapM_conv_of_zip w env args vals hlenA hargs
  obtain ⟨Nb, hb⟩ := hbody
  refine ⟨max Nm Nb + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  show evalOptStep (evalOpt g) w env _ = some v
  simp only [evalOptStep_cons_symbol,
    if_neg (by simp [hq] : ¬(s.isNamed "QUOTE" = true)),
    if_neg (by simp [hif] : ¬(s.isNamed "IF" = true)),
    if_neg (by simp [Bool.or_eq_true] at hlet ⊢; exact hlet :
      ¬((s.isNamed "LET" || s.isNamed "LET*") = true)), hal]
  try dsimp only []
  rw [hm g (by omega), hget]
  have hfin : (if formals.length = vals.length then
      evalOpt g w (bindArgs formals vals) body
    else none) = some v := by
    rw [if_pos hlen]
    exact hb g (by omega)
  exact hfin

end ACL2.Replay
