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

/-- Unary alias-WRAPPER totality: a fn defined as `(fn x) := (g x)` is
    total when `g` is (both statements in the driver\'s offered totality
    shape `∀ env a, conv a → conv (fn a)` with `∃N ∃v ∀f`-packed
    convergence). -/
theorem wrapper_total_1 (w : World) (fn g x : Symbol)
    (hdef : w.defs.get? fn = some ([x],
      .cons (.atom (.symbol g)) (.cons (.atom (.symbol x)) .nil)))
    (hq : fn.isNamed "QUOTE" = false) (hif : fn.isNamed "IF" = false)
    (hlet : (fn.isNamed "LET" || fn.isNamed "LET*") = false)
    (hg : ∀ (env : Env) (a : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env a = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env
        (.cons (.atom (.symbol g)) (.cons a .nil)) = some v)) :
    ∀ (env : Env) (a : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env a = some v) →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env
        (.cons (.atom (.symbol fn)) (.cons a .nil)) = some v := by
  intro env a ⟨Na, va, ha⟩
  have hx : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w (bindArgs [x] [va])
      (.atom (.symbol x)) = some v := by
    refine ⟨1, va, fun f hf => ?_⟩
    obtain ⟨gg, rfl⟩ : ∃ gg, f = gg + 1 := ⟨f - 1, by omega⟩
    show evalOptStep (evalOpt gg) w _ _ = some va
    simp only [evalOptStep]
    have : (bindArgs [x] [va]).get? x = some va := by
      show ((bindArgs [] []).insert x va).get? x = some va
      rw [Env.get?_insert]
      simp
    rw [this]
  obtain ⟨Ng, vg, hgv⟩ := hg (bindArgs [x] [va]) (.atom (.symbol x)) hx
  obtain ⟨N', h'⟩ := conv_defcall w env fn (.cons a .nil) [a] [va] [x]
    (.cons (.atom (.symbol g)) (.cons (.atom (.symbol x)) .nil)) vg
    hq hif hlet (by simp [SExpr.toList?]) hdef (by simp) (by simp)
    (by
      intro p hp
      have : p = (a, va) := by simpa [List.zip_cons_cons] using hp
      subst this
      exact ⟨Na, ha⟩)
    ⟨Ng, hgv⟩
  exact ⟨N', vg, h'⟩

/-- STEP INVERSION for a defined-fn call: a converging application
    yields converging arguments and a converging body under the bound
    env. -/
theorem defcall_body_inversion (w : World) (env : Env) (s : Symbol)
    (argsExpr : SExpr) (args : List SExpr)
    (formals : List Symbol) (body : SExpr) (v : SExpr)
    (hq : s.isNamed "QUOTE" = false) (hif : s.isNamed "IF" = false)
    (hlet : (s.isNamed "LET" || s.isNamed "LET*") = false)
    (hal : argsExpr.toList? = some args)
    (hget : w.defs.get? s = some (formals, body))
    (hconv : ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol s)) argsExpr) = some v) :
    ∃ vals, formals.length = vals.length ∧
      (∀ p ∈ args.zip vals,
        ∃ N, ∀ f ≥ N, evalOpt f w env p.1 = some p.2) ∧
      ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs formals vals) body = some v := by
  obtain ⟨N, hN⟩ := hconv
  have h := hN (N + 1) (by omega)
  rw [show evalOpt (N+1) w env (.cons (.atom (.symbol s)) argsExpr)
    = evalOptStep (evalOpt N) w env _ from rfl] at h
  simp only [evalOptStep_cons_symbol,
    if_neg (by simp [hq] : ¬(s.isNamed "QUOTE" = true)),
    if_neg (by simp [hif] : ¬(s.isNamed "IF" = true)),
    if_neg (by simp [Bool.or_eq_true] at hlet ⊢; exact hlet :
      ¬((s.isNamed "LET" || s.isNamed "LET*") = true)), hal] at h
  revert h
  cases hmap : args.mapM (fun a => evalOpt N w env a) with
  | none => intro h; exact absurd h (by simp)
  | some vals =>
    intro h
    rw [hget] at h
    replace h : (if formals.length = vals.length then
        evalOpt N w (bindArgs formals vals) body
      else none) = some v := h
    by_cases hlen : formals.length = vals.length
    case neg => rw [if_neg hlen] at h; exact absurd h (by simp)
    rw [if_pos hlen] at h
    refine ⟨vals, hlen, ?_, ⟨N, fun f hf =>
      evalOpt_ge_fuel N f w _ body v h hf⟩⟩
    intro p hp
    exact ⟨N, fun f hf => evalOpt_ge_fuel N f w env p.1 p.2
      (mapM_some_zip hmap p hp) hf⟩

/-- TOTALITY TRANSPORT into the alias world (unary): a consumer-world
    totality fact for an alias-free-bodied fn lifts to the alias world —
    the consumer hypothesis is probed at the QUOTED value, its step
    inverted, the body crossed by Lemma A, and the call reassembled by
    `conv_defcall`. -/
theorem total_fnalias_transport (names : List Symbol) (w w' : World)
    (hagree : ∀ s : Symbol, names.contains s = false →
      w'.defs.get? s = w.defs.get? s)
    (hw : aliasFreeWorld names w = true)
    (fn x : Symbol) (body : SExpr)
    (hq : fn.isNamed "QUOTE" = false) (hif : fn.isNamed "IF" = false)
    (hlet : (fn.isNamed "LET" || fn.isNamed "LET*") = false)
    (hget : w.defs.get? fn = some ([x], body))
    (hfnFree : names.contains fn = false)
    (hbodyFree : fnFreeTerm names body = true)
    (htot : ∀ (env : Env) (a : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env a = some v) →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env
        (.cons (.atom (.symbol fn)) (.cons a .nil)) = some v) :
    ∀ (env : Env) (a : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w' env a = some v) →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w' env
        (.cons (.atom (.symbol fn)) (.cons a .nil)) = some v := by
  intro env a ⟨Na, va, ha⟩
  -- probe the consumer fact at the QUOTED value
  have hquote : ∃ N, ∃ u, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "QUOTE" })) (.cons va .nil))
      = some u := by
    refine ⟨1, va, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rfl
  obtain ⟨Nc, v, hc⟩ := htot env _ hquote
  -- invert the converging call's step
  obtain ⟨vals, hlen, hzip, hbody⟩ := defcall_body_inversion w env fn
    (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
      (.cons va .nil)) .nil)
    [.cons (.atom (.symbol { name := "QUOTE" })) (.cons va .nil)]
    [x] body v hq hif hlet (by simp [SExpr.toList?]) hget ⟨Nc, hc⟩
  -- the single bound value IS va (quote determinism)
  obtain ⟨u, rfl⟩ : ∃ u, vals = [u] := by
    match vals, hlen with
    | [u], _ => exact ⟨u, rfl⟩
  have huv : u = va := by
    have hq1 : ∃ N, ∀ f ≥ N, evalOpt f w env
        (.cons (.atom (.symbol { name := "QUOTE" })) (.cons va .nil))
        = some u := by
      have := hzip (.cons (.atom (.symbol { name := "QUOTE" }))
        (.cons va .nil), u) (by simp [List.zip_cons_cons])
      exact this
    have hq2 : ∃ N, ∀ f ≥ N, evalOpt f w env
        (.cons (.atom (.symbol { name := "QUOTE" })) (.cons va .nil))
        = some va := ⟨1, fun f hf => by
          obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
          rfl⟩
    exact conv_unique hq1 hq2
  subst huv
  -- cross the body evaluation by A, reassemble at the alias world
  obtain ⟨Nb, hb⟩ := hbody
  have hb' : ∀ f ≥ Nb, evalOpt f w' (bindArgs [x] [u]) body = some v :=
    fun f hf => by
      rw [evalOpt_fnfree_agree names w w' hagree hw f _ body hbodyFree]
      exact hb f hf
  obtain ⟨N', h'⟩ := conv_defcall w' env fn (.cons a .nil) [a] [u] [x]
    body v hq hif hlet (by simp [SExpr.toList?])
    (by rw [hagree fn hfnFree]; exact hget) (by simp) (by simp)
    (by
      intro p hp
      have : p = (a, u) := by simpa [List.zip_cons_cons] using hp
      subst this
      exact ⟨Na, ha⟩)
    ⟨Nb, hb'⟩
  exact ⟨N', v, h'⟩

end ACL2.Replay
