/-
  Replay/Lemmas/Totality — section-aligned positional slice of the former
  EvalLemmas monolith (perf arc, 2026-08-07): MOVE-ONLY; the cut points
  are the file's own section-header layer boundaries, which sit in def-before-use
  order, so the import chain IS the dependency order.
-/
import ACL2Lean.Replay.Lemmas.Derived

namespace ACL2.Replay

open ACL2

/-! ## Totality-from-admission walk lemmas (#37)

The body-convergence walk for admission-derived totality proofs: the walk is
CASE-SPLIT style — at each `if`, the test's value is characterized and the
two branch walks proceed under an explicit `toBool`-fact hypothesis (which is
exactly what the emitted decrease obligations consume at recursive call
sites). Conclusions are in the ∃N∃v totality shape of the driver's
`total:fn` hypotheses. -/

/-- Split an `if` on its test's VALUE: each branch converges under its
    branch fact, so the `if` converges. -/
theorem conv_if_split (w : World) (env : Env) (c t e vc : SExpr)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some vc)
    (ht : Logic.toBool vc = true →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env t = some v)
    (he : Logic.toBool vc = false →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env e = some v) :
    ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil))))
      = some v := by
  obtain ⟨Nc, hc'⟩ := hc
  cases hb : Logic.toBool vc with
  | true =>
    obtain ⟨Nt, v, ht'⟩ := ht hb
    refine ⟨max Nc Nt + 1, v, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [evalOpt_if_true g w env c t e vc (hc' g (by omega)) hb]
    exact ht' g (by omega)
  | false =>
    obtain ⟨Ne, v, he'⟩ := he hb
    have hnil : vc = SExpr.nil := by
      cases vc with
      | nil => rfl
      | atom a => simp [Logic.toBool] at hb
      | cons a b => simp [Logic.toBool] at hb
    refine ⟨max Nc Ne + 1, v, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [evalOpt_if_false g w env c t e (hnil ▸ hc' g (by omega))]
    exact he' g (by omega)

/-- A 1-ary defined call converges when its argument and its body (at the
    argument's value) converge — ∃N∃v walk form. -/
theorem conv_defn_1_ex (w : World) (env : Env) (s : Symbol) (formal : Symbol)
    (body arg av : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal], body))
    (harg : ∃ N, ∀ f ≥ N, evalOpt f w env arg = some av)
    (hbody : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w (bindArgs [formal] [av]) body = some v) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol s)) (.cons arg .nil)) = some v := by
  obtain ⟨Nb, v, hb⟩ := hbody
  obtain ⟨N, h⟩ := conv_defn_1 w env s arg av formal body v h_ns h_def harg ⟨Nb, hb⟩
  exact ⟨N, v, h⟩

/-- A 2-ary defined call converges when its arguments and its body (at the
    argument values) converge — ∃N∃v walk form. -/
theorem conv_defn_2_ex (w : World) (env : Env) (s : Symbol)
    (formal1 formal2 : Symbol) (body arg1 arg2 av1 av2 : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2], body))
    (h1 : ∃ N, ∀ f ≥ N, evalOpt f w env arg1 = some av1)
    (h2 : ∃ N, ∀ f ≥ N, evalOpt f w env arg2 = some av2)
    (hbody : ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w (bindArgs [formal1, formal2] [av1, av2]) body = some v) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol s)) (.cons arg1 (.cons arg2 .nil)))
        = some v := by
  obtain ⟨Nb, v, hb⟩ := hbody
  obtain ⟨N, h⟩ := conv_defn_2 w env s arg1 arg2 av1 av2 formal1 formal2 body v
    h_ns h_def h1 h2 ⟨Nb, hb⟩
  exact ⟨N, v, h⟩

/-- WELL-FOUNDED (strong) induction over an ARBITRARY Nat measure — the
    spine of admission-derived totality proofs (#37) and of the TP body
    inductions. The driver instantiates the motive `P av := the function
    converges at argument VALUE av`; the inductive hypothesis covers every
    value of strictly smaller μ, and the admission's emitted decrease
    obligations justify applying it at each recursive call's argument
    value. μ is proof bookkeeping only (design I1) — it appears in no
    statement the driver produces.

    THE ONE COPY (T1+2 sprint P4b): `consCount_strong_induction` below and
    `Judgments`' copy of `measure_strong_induction_val` were the same
    theorem stated twice; both are now this one, instantiated. (The
    ENV-level `measure_strong_induction` below is a different lemma.) -/
theorem measure_strong_induction_val (μ : SExpr → Nat) (P : SExpr → Prop)
    (step : ∀ x, (∀ y, μ y < μ x → P y) → P x) : ∀ x, P x := by
  intro x
  generalize h : μ x = n
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih => exact step x (fun y hy => ih (μ y) (h ▸ hy) y rfl)

/-- Strong induction on `consCount` — `measure_strong_induction` at the
    `count` measure-table row's μ. -/
theorem consCount_strong_induction (P : SExpr → Prop)
    (step : ∀ x, (∀ y, y.consCount < x.consCount → P y) → P x) : ∀ x, P x :=
  measure_strong_induction_val SExpr.consCount P step

/-- ENV-LEVEL strong induction over an interpreted MEASURE (the
    induction-generality scaffold lemma, design §I2 — J1-spike-validated).
    `μ` is the μ-registry's total meta-level interpretation of the emitted
    measure term (Nat `MeasureImage` instance); the motive is the pushed
    pool entry's `EvTrue` at the ambient env. Relation-polymorphic in
    spirit (per-carrier instances re-prove this lemma over their own wf
    relation — theory-audit T5). Multiple emitted IH alists instantiate
    the ONE strong hypothesis (axis A1); swaps and ride-along
    substitutions are plain env updates (A3). -/
theorem measure_strong_induction (μ : Env → Nat) (P : Env → Prop)
    (step : ∀ env, (∀ env', μ env' < μ env → P env') → P env) : ∀ env, P env := by
  intro env
  generalize h : μ env = n
  induction n using Nat.strong_induction_on generalizing env with
  | _ n ih => exact step env (fun env' hlt => ih (μ env') (h ▸ hlt) env' rfl)

/-- `Logic.trueListp` is two-valued — the TRUE-LISTP twin of
    `lexorder_boolean` (J1(a)-surfaced; the recognizer/boolean decode for
    TRUE-LISTP-headed facts). -/
theorem trueListp_boolean (v : SExpr) :
    Logic.trueListp v = SExpr.t ∨ Logic.trueListp v = SExpr.nil := by
  induction v with
  | cons a b iha ihb => simpa [Logic.trueListp] using ihb
  | nil => exact .inl rfl
  | atom x => exact .inr rfl

/-- `Logic.len` always returns an int atom (both arms of its match do) —
    the value decode the arithmetic recipes need (J1(b)-surfaced). -/
theorem len_int (v : SExpr) :
    ∃ k : Int, Logic.len v = .atom (.number (.int k)) := by
  cases v <;> exact ⟨_, rfl⟩

/-- Integer addition at the value layer: `Logic.plus` on int atoms
    (J1(b)-surfaced; the arithmetic recipes' decode). -/
theorem plus_int (j k : Int) :
    Logic.plus (.atom (.number (.int j))) (.atom (.number (.int k)))
      = .atom (.number (.int (j + k))) := by
  simp [Logic.plus, Logic.toRat, Logic.mkNumber]

/-- J3 compound-test INVERSION, the OR-form step: a nil-valued
    `(IF a a c)` (ACL2's or-form — the compound ruling tests of
    multi-controller schemes, e.g. ZIP2's `(IF (ATOM X) (ATOM X) (ATOM Y))`)
    forces BOTH components nil. Recursing this along the emitted term's
    shape inverts any or-nesting (ZIP3 = two applications). -/
theorem cond_or_nil_inv {va vc : SExpr}
    (h : cond (Logic.toBool va) va vc = SExpr.nil) :
    va = SExpr.nil ∧ vc = SExpr.nil := by
  by_cases hb : Logic.toBool va = true
  · rw [hb] at h
    simp only [cond] at h
    subst h
    simp [Logic.toBool] at hb
  · have hn : va = SExpr.nil := by
      cases va <;> simp_all [Logic.toBool]
    rw [hn] at h ⊢
    simp only [Logic.toBool, cond] at h
    exact ⟨rfl, h⟩

/-- J3: a nil `Logic.atom` verdict IS consp-ness of the value — the decode
    from an inverted `(ATOM v)` leaf to the decrease precondition. -/
theorem consp_toBool_of_atom_nil {v : SExpr}
    (h : Logic.atom v = SExpr.nil) :
    Logic.toBool (Logic.consp v) = true := by
  cases v <;> simp_all [Logic.atom, Logic.consp, Logic.toBool]

/-- Value-characterized convergence of a VARIABLE from a concrete env-get
    fact (the formals of a `bindArgs` env during the totality walk). -/
theorem re_val_var_get (w : World) (env : Env) (s : Symbol) (v : SExpr)
    (h : env.get? s = some v) :
    ∃ N, ∀ f ≥ N, evalOpt f w env (.atom (.symbol s)) = some v :=
  ⟨1, fun f hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact evalOpt_var g w env s v h⟩

/-- Eliminate a derived ∃N∃v convergence into a continuation expecting the
    value and its v-fixed convergence — the DP-leaf harness consumes
    admission-derived totality this way (#37): the leaf's per-opaque
    `total:(fn args)` hypothesis becomes a DERIVATION instead. -/
theorem exists_conv_elim {w : World} {env : Env} {t : SExpr} {motive : Prop}
    (h : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env t = some v)
    (k : ∀ v, (∃ N, ∀ f ≥ N, evalOpt f w env t = some v) → motive) : motive := by
  obtain ⟨N, v, hv⟩ := h
  exact k v ⟨N, hv⟩

/-- Pack a value-characterized convergence into the ∃N∃v walk shape. -/
theorem conv_ex_of_vfix {w : World} {env : Env} {t v : SExpr}
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env t = some v) :
    ∃ N, ∃ u, ∀ f ≥ N, evalOpt f w env t = some u := by
  obtain ⟨N, h⟩ := h; exact ⟨N, v, h⟩

/-- `t` evaluates (fuel-stably) to exactly `v`. The totality prover
    constructs this type when it binds an OPAQUE test verdict. -/
abbrev ConvTo (w : World) (env : Env) (t v : SExpr) : Prop :=
  ∃ N, ∀ f ≥ N, evalOpt f w env t = some v

/-- `conv_if_split` over an EXISTENTIAL test verdict: the test converges to
    some (unknown) value — e.g. a call to an already-total user fn — and
    each branch converges under the corresponding `toBool` verdict of that
    value. The totality prover's user-fn-if-test extension: exactly the move
    `dis_perm_total` made by hand (`conv_if_split` over memb's existential
    verdict), mechanized. -/
theorem conv_if_split_ex (w : World) (env : Env) (c t e : SExpr)
    (hc : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env c = some v)
    (ht : ∀ vc, ConvTo w env c vc → Logic.toBool vc = true →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env t = some v)
    (he : ∀ vc, ConvTo w env c vc → Logic.toBool vc = false →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env e = some v) :
    ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil))))
      = some v := by
  obtain ⟨N, vc, hvc⟩ := hc
  exact conv_if_split w env c t e vc ⟨N, hvc⟩ (ht vc ⟨N, hvc⟩) (he vc ⟨N, hvc⟩)

/-- A 1-ary BUILTIN call converges when its argument does (∃N∃v walk form);
    `g`/`hg` are the primitive's total value function and its `callBuiltin`
    characterization (the dpUnary rfl lemma). -/
theorem conv_builtin1_ex (w : World) (env : Env) (s : Symbol) (a : SExpr)
    (g : SExpr → SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_no : w.defs.get? s = none)
    (hg : ∀ v, callBuiltin s.name [v] = some (g v))
    (ha : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env a = some v) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol s)) (.cons a .nil)) = some v := by
  obtain ⟨Na, av, ha'⟩ := ha
  obtain ⟨N, h⟩ := conv_builtin1 w env s a av (g av) h_ns h_no ⟨Na, ha'⟩ (hg av)
  exact ⟨N, g av, h⟩

/-- A 2-ary BUILTIN call converges when its arguments do (∃N∃v walk form). -/
theorem conv_builtin2_ex (w : World) (env : Env) (s : Symbol) (a b : SExpr)
    (g : SExpr → SExpr → SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_no : w.defs.get? s = none)
    (hg : ∀ u v, callBuiltin s.name [u, v] = some (g u v))
    (ha : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env a = some v)
    (hb : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env b = some v) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol s)) (.cons a (.cons b .nil)))
        = some v := by
  obtain ⟨Na, av, ha'⟩ := ha
  obtain ⟨Nb, bv, hb'⟩ := hb
  obtain ⟨N, h⟩ := conv_builtin2 w env s a b av bv (g av bv) h_ns h_no
    ⟨Na, ha'⟩ ⟨Nb, hb'⟩ (hg av bv)
  exact ⟨N, g av bv, h⟩

/-- TOTALITY of a NON-RECURSIVE 1-ary defined fn from its body's convergence
    at every argument value — the capper the totality prover applies; the
    driver supplies `hbody` as the body walk λ-abstracted over the value. -/
theorem totality_1_of_body (w : World) (s : Symbol) (formal : Symbol) (body : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal], body))
    (hbody : ∀ av : SExpr, ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w (bindArgs [formal] [av]) body = some v) :
    ∀ (env' : Env) (a0 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N,
        evalOpt f w env' (.cons (.atom (.symbol s)) (.cons a0 .nil)) = some v := by
  intro env' a0 h0
  obtain ⟨N0, av, h0'⟩ := h0
  exact conv_defn_1_ex w env' s formal body a0 av h_ns h_def ⟨N0, h0'⟩ (hbody av)

/-- TOTALITY of a NON-RECURSIVE 2-ary defined fn (see `totality_1_of_body`). -/
theorem totality_2_of_body (w : World) (s : Symbol) (formal1 formal2 : Symbol)
    (body : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2], body))
    (hbody : ∀ av1 av2 : SExpr, ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w (bindArgs [formal1, formal2] [av1, av2]) body = some v) :
    ∀ (env' : Env) (a0 a1 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a1 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N,
        evalOpt f w env' (.cons (.atom (.symbol s)) (.cons a0 (.cons a1 .nil)))
          = some v := by
  intro env' a0 a1 h0 h1
  obtain ⟨N0, av1, h0'⟩ := h0
  obtain ⟨N1, av2, h1'⟩ := h1
  exact conv_defn_2_ex w env' s formal1 formal2 body a0 a1 av1 av2 h_ns h_def
    ⟨N0, h0'⟩ ⟨N1, h1'⟩ (hbody av1 av2)

/-- TOTALITY of a RECURSIVE 1-ary defined fn by WELL-FOUNDED induction on the
    argument value's `consCount` (the admitted measure, D5 scope): the driver
    supplies `step` — the body walk under the inductive hypothesis, which it
    applies at each self-call's argument value justified by the emitted
    decrease obligation. -/
theorem totality_1_rec (w : World) (s : Symbol) (formal : Symbol) (body : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal], body))
    (step : ∀ av : SExpr,
      (∀ bv : SExpr, bv.consCount < av.consCount →
        ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w (bindArgs [formal] [bv]) body = some v) →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w (bindArgs [formal] [av]) body = some v) :
    ∀ (env' : Env) (a0 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N,
        evalOpt f w env' (.cons (.atom (.symbol s)) (.cons a0 .nil)) = some v := by
  have hbody := consCount_strong_induction
    (fun av => ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w (bindArgs [formal] [av]) body = some v) step
  exact totality_1_of_body w s formal body h_ns h_def hbody

/-- TOTALITY of a RECURSIVE 2-ary defined fn, measure on the FIRST formal
    (the measured one; the driver permutes when the measured formal is the
    second). The second argument's value is universally quantified INSIDE the
    induction, so self-calls may pass any second argument. -/
theorem totality_2_rec (w : World) (s : Symbol) (formal1 formal2 : Symbol)
    (body : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2], body))
    (step : ∀ av1 : SExpr,
      (∀ bv : SExpr, bv.consCount < av1.consCount → ∀ cv : SExpr,
        ∃ N, ∃ v, ∀ f ≥ N,
          evalOpt f w (bindArgs [formal1, formal2] [bv, cv]) body = some v) →
      ∀ av2 : SExpr, ∃ N, ∃ v, ∀ f ≥ N,
        evalOpt f w (bindArgs [formal1, formal2] [av1, av2]) body = some v) :
    ∀ (env' : Env) (a0 a1 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a1 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N,
        evalOpt f w env' (.cons (.atom (.symbol s)) (.cons a0 (.cons a1 .nil)))
          = some v := by
  have hbody := consCount_strong_induction
    (fun av1 => ∀ av2 : SExpr, ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w (bindArgs [formal1, formal2] [av1, av2]) body = some v) step
  exact totality_2_of_body w s formal1 formal2 body h_ns h_def
    (fun av1 av2 => hbody av1 av2)

/-- `totality_2_rec` for a defun measured on its SECOND formal (e.g.
    `(rm e x)` / `(memb a x)` recurring on `x`): strong induction on the
    second argument's count, the first universally quantified inside. -/
theorem totality_2_rec_snd (w : World) (s : Symbol) (formal1 formal2 : Symbol)
    (body : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2], body))
    (step : ∀ av2 : SExpr,
      (∀ cv : SExpr, cv.consCount < av2.consCount → ∀ bv : SExpr,
        ∃ N, ∃ v, ∀ f ≥ N,
          evalOpt f w (bindArgs [formal1, formal2] [bv, cv]) body = some v) →
      ∀ av1 : SExpr, ∃ N, ∃ v, ∀ f ≥ N,
        evalOpt f w (bindArgs [formal1, formal2] [av1, av2]) body = some v) :
    ∀ (env' : Env) (a0 a1 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a1 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N,
        evalOpt f w env' (.cons (.atom (.symbol s)) (.cons a0 (.cons a1 .nil)))
          = some v := by
  have hbody := consCount_strong_induction
    (fun av2 => ∀ av1 : SExpr, ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w (bindArgs [formal1, formal2] [av1, av2]) body = some v) step
  exact totality_2_of_body w s formal1 formal2 body h_ns h_def
    (fun av1 av2 => hbody av2 av1)

-- CONVENTION: convergence is stated in **v-fixed totality** form
-- `∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env t = some v` — a single definite value `v`
-- (`evalOpt` is fuel-monotone, so a converging term HAS one value). This feeds any
-- value-specific lemma: `obtain ⟨N, v, h⟩` gives `∀ f ≥ N, … = some v`. (The weaker
-- v-inside form `∃ N, ∀ f ≥ N, ∃ v` supplies no usable witness.)

theorem re_conv_quote (w : World) (env : Env) (v : SExpr) :
    ∃ N, ∃ v', ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "QUOTE" })) (.cons v .nil)) = some v' :=
  ⟨1, v, fun f _ => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact evalOpt_quote g w env v⟩

/-- Convergence (v-fixed) of a VARIABLE: `(var s)` converges to its binding (or `nil`
    if unbound, provided `s` is not the constant `t`) in ANY environment — the
    variable-convergence fact the replayed statement's `∀ env` quantification needs. -/
theorem re_conv_var (w : World) (env : Env) (s : Symbol) (h_not_t : s.isNamed "T" = false) :
    ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env (.atom (.symbol s)) = some v := by
  match h : env.get? s with
  | some v => exact ⟨1, v, fun f _ => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      exact evalOpt_var g w env s v h⟩
  | none => exact ⟨1, .nil, fun f _ => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      exact evalOpt_var_unbound g w env s h h_not_t⟩

/-- equal-self, fuel-robust closing form: if `A` converges (v-fixed) and `equal` is
    not shadowed, then `(equal A A)` converges to `t`. The driver supplies only `A`'s
    convergence. -/
theorem re_equal_self (w : World) (env : Env) (A : SExpr)
    (hconv : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env A = some v)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "EQUAL" })) (.cons A (.cons A .nil))) = some SExpr.t := by
  obtain ⟨N, v, hN⟩ := hconv
  refine ⟨N + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  exact evalOpt_equal_self g w env A v (hN g (by omega)) h_no_equal

/-- RUNE `cdr-cons`, driver-facing (v-fixed convergence): `(cdr (cons a b)) ⇒ b` given
    `a`, `b` converge. A thin wrapper over the value-specific `re_cdr_cons` that
    `obtain`s the fixed operand witnesses — so the driver passes `proveConv`'s output
    straight in (no `Exists.elim` threading). -/
theorem re_cdr_cons_conv (w : World) (env : Env) (a b : SExpr)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∃ bv, ∀ f ≥ N, evalOpt f w env b = some bv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "CDR" }))
        (.cons (.cons (.atom (.symbol { name := "CONS" })) (.cons a (.cons b .nil))) .nil))
      = evalOpt f w env b := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨Nb, bv, hb⟩ := hb
  exact re_cdr_cons w env a b av bv h_no_cdr h_no_cons ⟨Na, ha⟩ ⟨Nb, hb⟩

/-- RUNE `car-cons` (conv form): `(car (cons a b)) ⇒ a`, term-to-term. -/
theorem re_car_cons_conv (w : World) (env : Env) (a b : SExpr)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∃ bv, ∀ f ≥ N, evalOpt f w env b = some bv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "CAR" }))
        (.cons (.cons (.atom (.symbol { name := "CONS" })) (.cons a (.cons b .nil))) .nil))
      = evalOpt f w env a := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨Nb, bv, hb⟩ := hb
  exact re_car_cons w env a b av bv h_no_car h_no_cons ⟨Na, ha⟩ ⟨Nb, hb⟩

/-- Convergence (v-fixed) of a `(cons a b)` application: converges to `(cons av bv)`
    when `a`, `b` converge. The convergence-analyzer's compound-term case for `cons`
    (`car`/`cdr`/`binary-*`/… follow the same shape via their `callBuiltin` lemma). -/
theorem re_conv_cons (w : World) (env : Env) (a b : SExpr)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∃ bv, ∀ f ≥ N, evalOpt f w env b = some bv) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "CONS" })) (.cons a (.cons b .nil)))
      = some v := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨Nb, bv, hb⟩ := hb
  obtain ⟨N, h⟩ := conv_builtin2 w env { name := "CONS" } a b av bv (.cons av bv)
    (by decide) h_no_cons ⟨Na, ha⟩ ⟨Nb, hb⟩ rfl
  exact ⟨N, .cons av bv, h⟩

/-- Convergence (v-fixed) of a `(binary-* a b)` application: converges to `times av bv`
    when `a`, `b` converge. (Same shape as `re_conv_cons`.) -/
theorem re_conv_times (w : World) (env : Env) (a b : SExpr)
    (h_no_times : w.defs.get? ({ name := "BINARY-*" } : Symbol) = none)
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∃ bv, ∀ f ≥ N, evalOpt f w env b = some bv) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "BINARY-*" })) (.cons a (.cons b .nil)))
      = some v := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨Nb, bv, hb⟩ := hb
  obtain ⟨N, h⟩ := conv_builtin2 w env { name := "BINARY-*" } a b av bv (Logic.times av bv)
    (by decide) h_no_times ⟨Na, ha⟩ ⟨Nb, hb⟩ rfl
  exact ⟨N, Logic.times av bv, h⟩

/-- Convergence (v-fixed) of a `(binary-+ a b)` application: converges to `plus av bv`
    when `a`, `b` converge. (Same shape as `re_conv_times`.) -/
theorem re_conv_plus (w : World) (env : Env) (a b : SExpr)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∃ bv, ∀ f ≥ N, evalOpt f w env b = some bv) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "BINARY-+" })) (.cons a (.cons b .nil)))
      = some v := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨Nb, bv, hb⟩ := hb
  obtain ⟨N, h⟩ := conv_builtin2 w env { name := "BINARY-+" } a b av bv (Logic.plus av bv)
    (by decide) h_no_plus ⟨Na, ha⟩ ⟨Nb, hb⟩ rfl
  exact ⟨N, Logic.plus av bv, h⟩

/-- Convergence (v-fixed) of a UNARY builtin application `(car a)`: converges to
    `car av` when `a` converges. The convergence-analyzer's unary-builtin shape;
    `cdr`/`consp` follow identically via their `callBuiltin` lemma. -/
theorem re_conv_car (w : World) (env : Env) (a : SExpr)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "CAR" })) (.cons a .nil)) = some v := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨N, h⟩ := conv_builtin1 w env { name := "CAR" } a av (Logic.car av)
    (by decide) h_no_car ⟨Na, ha⟩ (callBuiltin_car av)
  exact ⟨N, Logic.car av, h⟩

/-- Convergence (v-fixed) of `(cdr a)`: converges to `cdr av` when `a` converges. -/
theorem re_conv_cdr (w : World) (env : Env) (a : SExpr)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "CDR" })) (.cons a .nil)) = some v := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨N, h⟩ := conv_builtin1 w env { name := "CDR" } a av (Logic.cdr av)
    (by decide) h_no_cdr ⟨Na, ha⟩ (callBuiltin_cdr av)
  exact ⟨N, Logic.cdr av, h⟩

/-- Convergence (v-fixed) of `(consp a)`: converges to `consp av` when `a` converges. -/
theorem re_conv_consp (w : World) (env : Env) (a : SExpr)
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "CONSP" })) (.cons a .nil)) = some v := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨N, h⟩ := conv_builtin1 w env { name := "CONSP" } a av (Logic.consp av)
    (by decide) h_no_consp ⟨Na, ha⟩ (callBuiltin_consp av)
  exact ⟨N, Logic.consp av, h⟩

/-- RUNE `definition` (1-arg), driver-facing: `(fn arg) ⇒ substTerm [formal] [arg] body`.
    Takes `arg`'s convergence (v-fixed) and the body's convergence in EVERY env
    (`hbodyAll` — the driver proves this by running the convergence analyzer under a
    quantified env). A wrapper over `evalOpt_unfold1_conv` that instantiates the body
    convergence at the `bindArgs` env (which mentions the obtained arg value `av`), so
    the driver needs no `Exists.elim` of its own. -/
theorem re_unfold1_conv (w : World) (env : Env) (fn formal : Symbol) (body arg : SExpr)
    (hns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
           fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (hdef : w.defs.get? fn = some ([formal], body))
    (hclosed : ∀ s ∈ freeVars body, s ∈ [formal]) (hws : WellScoped body = true)
    (harg : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env arg = some av)
    (hbodyAll : ∀ env', ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' body = some v) :
    ∃ N, ∀ f ≥ N, evalOpt f w env (.cons (.atom (.symbol fn)) (.cons arg .nil))
      = evalOpt f w env (substTerm [formal] [arg] body) := by
  obtain ⟨Na, av, ha⟩ := harg
  obtain ⟨Nb, v, hb⟩ := hbodyAll (bindArgs [formal] [av])
  exact evalOpt_unfold1_conv w env fn formal body arg av v hns hdef hclosed hws ⟨Na, ha⟩ ⟨Nb, hb⟩

/-- RUNE recognizer (true): `(acl2-numberp z) ⇒ t` when `z` converges to an integer — the
    form `type-prescription:my-len` supplies. Mirrors the recognizer node that feeds
    `definition:fix`'s `if` test in the base case (a builtin recognizer like the step
    case's `consp`; the operand value stays existential). -/
theorem re_acl2_numberp_int (w : World) (env : Env) (z : SExpr) (k : Int)
    (h_no : w.defs.get? ({ name := "ACL2-NUMBERP" } : Symbol) = none)
    (hz : ∃ N, ∀ f ≥ N, evalOpt f w env z = some (.atom (.number (.int k)))) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "ACL2-NUMBERP" })) (.cons z .nil)) = some .t :=
  conv_builtin1 w env { name := "ACL2-NUMBERP" } z (.atom (.number (.int k))) .t
    (by decide) h_no hz (by rfl)

/-! ## The not-consp VALUE-level nil pair

The recorded-termination route's ruler peel decodes an emitted NEGATIVE
recognizer ruler against the translated body's truthy `(CONSP …)` branch
fact. `BranchFacts.recogView` is the shared SHAPE rule (it duals `ENDP`
and `ATOM` alike); these two are its VALUE-level counterparts, and they
must be kept ADJACENT — the R0 item-9 bug was exactly a clone of the
shape rule that knew `ENDP` only, so a matching value lemma was missing
when the `ATOM` leg was enabled. Add a recognizer here and to `recogView`
together. (Moved from `Lemmas/Judgments.lean`, 2026-08-13.) -/

/-- A truthy `(consp v)` walk fact makes `endp v` NIL — the CONSP/ENDP
    duality at the VALUE level (audit F1, sorting arc 2026-07-29: the
    recorded route's ruler peel consumes emitted `(ENDP …)` rulers against
    the translated body's `(CONSP …)` branch facts). -/
theorem logic_endp_nil_of_consp_toBool {v : SExpr}
    (h : Logic.toBool (Logic.consp v) = true) :
    Logic.endp v = SExpr.nil := by
  cases v <;> simp_all [Logic.endp, Logic.consp, Logic.toBool]

/-- The `ATOM` sibling (R0 item 9, 2026-08-13): `(atom v)` is
    `(not (consp v))` by ACL2's own definition (`axioms.lisp`), so a truthy
    `(consp v)` fact makes it NIL exactly as it does `endp`. -/
theorem logic_atom_nil_of_consp_toBool {v : SExpr}
    (h : Logic.toBool (Logic.consp v) = true) :
    Logic.atom v = SExpr.nil := by
  cases v <;> simp_all [Logic.atom, Logic.consp, Logic.toBool]

end ACL2.Replay
