/-
  Replay/Lemmas/Discharge — section-aligned positional slice of the former
  EvalLemmas monolith (perf arc, 2026-08-07): MOVE-ONLY; the cut points
  are the file's own section-header layer boundaries, which sit in def-before-use
  order, so the import chain IS the dependency order.
-/
import ACL2Lean.Replay.Lemmas.Totality

namespace ACL2.Replay

open ACL2

/-! ## Decision-procedure discharge leaves (the ratified carve-out)

    A clause ACL2 closed by a verdict-only decision procedure (tau / type-set
    forward-chain) carries an emitted discharge node `(disjoin clause) ⇒ t`. The
    driver replays it by VALUE-characterized evaluation of the if-spine
    (`proveVal`): every subterm's value is an explicit `Logic`-primitive
    expression over the clause variables' env values, the spine splits on each
    literal's value via `evtrue_dp_if_split`, and the residual fact
    `∀ vars, v₁ = nil → … → vₖ = t` is closed by a kernel-checked decision
    procedure (`omega` after SExpr case-split — see the carve-out in CLAUDE.md). -/

@[simp] theorem callBuiltin_zp (a : SExpr) :
    callBuiltin "ZP" [a] = some (Logic.zp a) := by rfl
@[simp] theorem callBuiltin_lt (a b : SExpr) :
    callBuiltin "<" [a, b] = some (Logic.lt a b) := by rfl
@[simp] theorem callBuiltin_lexorder (a b : SExpr) :
    callBuiltin "LEXORDER" [a, b] = some (lexorder a b) := by rfl
@[simp] theorem callBuiltin_integerp (a : SExpr) :
    callBuiltin "INTEGERP" [a] = some (Logic.integerp a) := by rfl
@[simp] theorem callBuiltin_cons (a b : SExpr) :
    callBuiltin "CONS" [a, b] = some (SExpr.cons a b) := by rfl
@[simp] theorem callBuiltin_implies (a b : SExpr) :
    callBuiltin "IMPLIES" [a, b] = some (Logic.implies a b) := by rfl
@[simp] theorem callBuiltin_iff (a b : SExpr) :
    callBuiltin "IFF" [a, b] = some (Logic.iff a b) := by rfl

/-- Value-characterized convergence of a quoted constant: `(quote v) ⇒ v`. -/
theorem re_val_quote (w : World) (env : Env) (v : SExpr) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "QUOTE" })) (.cons v .nil)) = some v :=
  ⟨1, fun f hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact evalOpt_quote g w env v⟩

/-- Value-characterized convergence of a variable: `(var s) ⇒ (env.get? s).getD nil`
    (the binding, or `nil` if unbound — requires `s ≠ t`, the self-evaluating symbol). -/
theorem re_val_var (w : World) (env : Env) (s : Symbol)
    (h_not_t : s.isNamed "T" = false) :
    ∃ N, ∀ f ≥ N, evalOpt f w env (.atom (.symbol s)) = some ((env.get? s).getD .nil) := by
  match h : env.get? s with
  | some v => exact ⟨1, fun f _ => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      simpa [h] using evalOpt_var g w env s v h⟩
  | none => exact ⟨1, fun f _ => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      simpa [h] using evalOpt_var_unbound g w env s h h_not_t⟩

/-- Rewrite a value-characterized convergence along a value equality (used to close
    the spine's last literal with the decision-procedure fact `vk = t`). -/
theorem re_val_cast (w : World) (env : Env) (a v v' : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env a = some v) (hv : v = v') :
    ∃ N, ∀ f ≥ N, evalOpt f w env a = some v' := hv ▸ h

/-- TOTALITY → BODY convergence (1-arg): if the application `(fn arg)` converges to
    `rv`, its body converges to `rv` at the bound-argument environment. (The inverse
    reading of the defn equation — the c3 unfold recipe's first step.) -/
theorem re_body_conv1 (w : World) (env : Env) (fn formal : Symbol)
    (body arg av rv : SExpr)
    (h_ns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
            fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (h_def : w.defs.get? fn = some ([formal], body))
    (harg : ∃ N, ∀ f ≥ N, evalOpt f w env arg = some av)
    (happ : ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol fn)) (.cons arg .nil)) = some rv) :
    ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [formal] [av]) body = some rv := by
  obtain ⟨Na, ha⟩ := harg; obtain ⟨Nr, hr⟩ := happ
  refine ⟨max Na Nr + 1, fun f hf => ?_⟩
  have heq := evalOpt_defn_1 f w env fn arg av formal body h_ns h_def (ha f (by omega))
  rw [← heq]
  exact hr (f + 1) (by omega)

/-- TOTALITY → BODY convergence (2-arg). -/
theorem re_body_conv2 (w : World) (env : Env) (fn f1 f2 : Symbol)
    (body a1 a2 av1 av2 rv : SExpr)
    (h_ns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
            fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (h_def : w.defs.get? fn = some ([f1, f2], body))
    (ha1 : ∃ N, ∀ f ≥ N, evalOpt f w env a1 = some av1)
    (ha2 : ∃ N, ∀ f ≥ N, evalOpt f w env a2 = some av2)
    (happ : ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol fn)) (.cons a1 (.cons a2 .nil))) = some rv) :
    ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [f1, f2] [av1, av2]) body = some rv := by
  obtain ⟨N1, h1⟩ := ha1; obtain ⟨N2, h2⟩ := ha2; obtain ⟨Nr, hr⟩ := happ
  refine ⟨max N1 (max N2 Nr) + 1, fun f hf => ?_⟩
  have heq := evalOpt_defn_2 f w env fn a1 a2 av1 av2 f1 f2 body h_ns h_def
    (h1 f (by omega)) (h2 f (by omega))
  rw [← heq]
  exact hr (f + 1) (by omega)

/-- 3-arg body convergence from the application's pinned value. -/
theorem re_body_conv3 (w : World) (env : Env) (fn f1 f2 f3 : Symbol)
    (body a1 a2 a3 av1 av2 av3 rv : SExpr)
    (h_ns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
            fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (h_def : w.defs.get? fn = some ([f1, f2, f3], body))
    (ha1 : ∃ N, ∀ f ≥ N, evalOpt f w env a1 = some av1)
    (ha2 : ∃ N, ∀ f ≥ N, evalOpt f w env a2 = some av2)
    (ha3 : ∃ N, ∀ f ≥ N, evalOpt f w env a3 = some av3)
    (happ : ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol fn)) (.cons a1 (.cons a2 (.cons a3 .nil)))) = some rv) :
    ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [f1, f2, f3] [av1, av2, av3]) body = some rv := by
  obtain ⟨N1, h1⟩ := ha1; obtain ⟨N2, h2⟩ := ha2; obtain ⟨N3, h3⟩ := ha3
  obtain ⟨Nr, hr⟩ := happ
  refine ⟨max N1 (max N2 (max N3 Nr)) + 1, fun f hf => ?_⟩
  have heq := evalOpt_defn_3 f w env fn a1 a2 a3 av1 av2 av3 f1 f2 f3 body h_ns h_def
    (h1 f (by omega)) (h2 f (by omega)) (h3 f (by omega))
  rw [← heq]
  exact hr (f + 1) (by omega)

/-- A variable's value at a 1-arg `bindArgs` env (the unfold recipe's env'-side
    variable resolution). -/
theorem re_val_var_bind1 (w : World) (s : Symbol) (av : SExpr) :
    ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [s] [av]) (.atom (.symbol s)) = some av :=
  ⟨1, fun f hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact evalOpt_var g w _ s av (bindArgs_single_get_self s av)⟩

/-- First variable's value at a 2-arg `bindArgs` env. -/
theorem re_val_var_bind2_fst (w : World) (f1 f2 : Symbol) (v1 v2 : SExpr) :
    ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [f1, f2] [v1, v2]) (.atom (.symbol f1)) = some v1 :=
  ⟨1, fun f hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact evalOpt_var g w _ f1 v1 (bindArgs_pair_get_fst f1 f2 v1 v2)⟩

/-- Second variable's value at a 2-arg `bindArgs` env (distinct formals). -/
theorem re_val_var_bind2_snd (w : World) (f1 f2 : Symbol) (v1 v2 : SExpr)
    (hne : f1 ≠ f2) :
    ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [f1, f2] [v1, v2]) (.atom (.symbol f2)) = some v2 :=
  ⟨1, fun f hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact evalOpt_var g w _ f2 v2 (bindArgs_pair_get_snd f1 f2 v1 v2 hne)⟩

/-- GENERIC total-builtin convergence (1-arg): a builtin whose `callBuiltin` is
    total on its arity converges whenever its argument does. The totality witness
    is built from the registry (`fun av => ⟨Logic.zp av, rfl⟩`) — ONE lemma for
    every registered builtin, replacing the per-builtin `re_conv_*` family. -/
theorem re_conv_builtin1_reg (w : World) (env : Env) (s : Symbol) (a : SExpr)
    (g : SExpr → SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_not_def : w.defs.get? s = none)
    (h_reg : ∀ av : SExpr, callBuiltin s.name [av] = some (g av))
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol s)) (.cons a .nil)) = some v := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨N, h⟩ := conv_builtin1 w env s a av (g av) h_ns h_not_def ⟨Na, ha⟩ (h_reg av)
  exact ⟨N, g av, h⟩

/-- GENERIC total-builtin convergence (2-arg). -/
theorem re_conv_builtin2_reg (w : World) (env : Env) (s : Symbol) (a b : SExpr)
    (g : SExpr → SExpr → SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_not_def : w.defs.get? s = none)
    (h_reg : ∀ av bv : SExpr, callBuiltin s.name [av, bv] = some (g av bv))
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∃ bv, ∀ f ≥ N, evalOpt f w env b = some bv) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol s)) (.cons a (.cons b .nil))) = some v := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨Nb, bv, hb⟩ := hb
  obtain ⟨N, h⟩ := conv_builtin2 w env s a b av bv (g av bv) h_ns h_not_def
    ⟨Na, ha⟩ ⟨Nb, hb⟩ (h_reg av bv)
  exact ⟨N, g av bv, h⟩

/-- Congruence into an `if`'s TEST position: equal test evaluations give equal
    `if` evaluations (sound for the lazy `if` — both sides bind the test first).
    The `(1 . IF)` path frame's congruence step. -/
theorem evalOpt_congr_if_test (w : World) (env : Env) (c c' t e : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env c = evalOpt f w env c') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil))))
      = evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" })) (.cons c' (.cons t (.cons e .nil)))) := by
  obtain ⟨N, h⟩ := h
  refine ⟨N + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  show evalOptStep (evalOpt g) w env _ = evalOptStep (evalOpt g) w env _
  unfold evalOptStep
  simp only [Symbol.isNamed, SExpr.toList?]
  show (evalOpt g w env c).bind _ = (evalOpt g w env c').bind _
  rw [h g (by omega)]

/-- Congruence into an `if`'s THEN branch under UNCONDITIONAL eval-equality:
    `eval t = eval t'` (for all sufficient fuel) ⇒ the whole `if` agrees. Sound
    because the hypothesis is unconditional — when the test is false the THEN
    branch is irrelevant, when true `t = t'`. The preprocess chain's node proofs
    are exactly this unconditional shape; this lets the chain lift a rewrite
    through an `if`'s then-branch (e.g. a clause-disjunction position). -/
theorem evalOpt_congr_if_then (w : World) (env : Env) (c t t' e : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env t = evalOpt f w env t') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil))))
      = evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t' (.cons e .nil)))) := by
  obtain ⟨N, h⟩ := h
  refine ⟨N + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  show evalOptStep (evalOpt g) w env _ = evalOptStep (evalOpt g) w env _
  unfold evalOptStep
  simp only [Symbol.isNamed, SExpr.toList?]
  show (evalOpt g w env c).bind _ = (evalOpt g w env c).bind _
  cases hc : evalOpt g w env c with
  | none => rfl
  | some cv =>
    simp only [Option.bind_some]
    by_cases hb : Logic.toBool cv = true
    · simp only [if_pos hb]; exact h g (by omega)
    · simp only [if_neg hb]

/-- Congruence into an `if`'s ELSE branch under UNCONDITIONAL eval-equality:
    `eval e = eval e'` (for all sufficient fuel) ⇒ the whole `if` agrees. Sound
    because the hypothesis is unconditional — when the test is true the ELSE
    branch is irrelevant, when false `e = e'`. Lets the preprocess chain lift a
    rewrite through an `if`'s else-branch (the clause-disjunction TAIL). -/
theorem evalOpt_congr_if_else (w : World) (env : Env) (c t e e' : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env e = evalOpt f w env e') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil))))
      = evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e' .nil)))) := by
  obtain ⟨N, h⟩ := h
  refine ⟨N + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  show evalOptStep (evalOpt g) w env _ = evalOptStep (evalOpt g) w env _
  unfold evalOptStep
  simp only [Symbol.isNamed, SExpr.toList?]
  show (evalOpt g w env c).bind _ = (evalOpt g w env c).bind _
  cases hc : evalOpt g w env c with
  | none => rfl
  | some cv =>
    simp only [Option.bind_some]
    by_cases hb : Logic.toBool cv = true
    · simp only [if_pos hb]
    · simp only [if_neg hb]; exact h g (by omega)

/-- RUNE `:DEFINITION fn` on two general arguments, body convergence supplied for
    EVERY environment (the ∀-env analyzer form — the 2-arg sibling of
    `re_unfold1_conv`). -/
theorem re_unfold2_conv (w : World) (env : Env) (fn f1 f2 : Symbol)
    (body arg1 arg2 : SExpr)
    (hns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
           fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (hdef : w.defs.get? fn = some ([f1, f2], body))
    (hclosed : ∀ s ∈ freeVars body, s ∈ [f1, f2]) (hws : WellScoped body = true)
    (harg1 : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env arg1 = some av)
    (harg2 : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env arg2 = some av)
    (hbodyAll : ∀ env', ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' body = some v) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol fn)) (.cons arg1 (.cons arg2 .nil)))
      = evalOpt f w env (substTerm [f1, f2] [arg1, arg2] body) := by
  obtain ⟨N1, av1, h1⟩ := harg1
  obtain ⟨N2, av2, h2⟩ := harg2
  obtain ⟨Nb, v, hb⟩ := hbodyAll (bindArgs [f1, f2] [av1, av2])
  exact evalOpt_unfold2_conv w env fn f1 f2 body arg1 arg2 av1 av2 v hns hdef hclosed hws
    ⟨N1, h1⟩ ⟨N2, h2⟩ ⟨Nb, hb⟩

/-- 3-arg ∀-env-route unfold: the `re_unfold2_conv` analogue. -/
theorem re_unfold3_conv (w : World) (env : Env) (fn f1 f2 f3 : Symbol)
    (body arg1 arg2 arg3 : SExpr)
    (hns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
           fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (hdef : w.defs.get? fn = some ([f1, f2, f3], body))
    (hclosed : ∀ s ∈ freeVars body, s ∈ [f1, f2, f3]) (hws : WellScoped body = true)
    (harg1 : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env arg1 = some av)
    (harg2 : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env arg2 = some av)
    (harg3 : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env arg3 = some av)
    (hbodyAll : ∀ env', ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' body = some v) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol fn)) (.cons arg1 (.cons arg2 (.cons arg3 .nil))))
      = evalOpt f w env (substTerm [f1, f2, f3] [arg1, arg2, arg3] body) := by
  obtain ⟨N1, av1, h1⟩ := harg1
  obtain ⟨N2, av2, h2⟩ := harg2
  obtain ⟨N3, av3, h3⟩ := harg3
  obtain ⟨Nb, v, hb⟩ := hbodyAll (bindArgs [f1, f2, f3] [av1, av2, av3])
  exact evalOpt_unfold3_conv w env fn f1 f2 f3 body arg1 arg2 arg3 av1 av2 av3 v
    hns hdef hclosed hws ⟨N1, h1⟩ ⟨N2, h2⟩ ⟨N3, h3⟩ ⟨Nb, hb⟩

/-- The solidify value bridge: a FALSE `(not (equal a b))` literal value makes the
    two values EQUAL. (The clause hypothesis the `rewriting-equivalence` node cites:
    its falsity in the case branch is exactly the equation.) -/
theorem logic_not_equal_nil_eq (a b : SExpr)
    (h : Logic.not (Logic.equal a b) = SExpr.nil) : a = b := by
  by_cases hab : a = b
  · exact hab
  · exfalso
    have hbeq : (a == b) = false := beq_eq_false_iff_ne.mpr hab
    simp [Logic.not, Logic.equal, Logic.toBool, hbeq, SExpr.t] at h

/-- A TRUE `(not (equal a b))` literal value makes the equality nil (the
    linear-equalities case split's escape branch — 2b). -/
theorem logic_not_equal_ne_nil_eq_nil (a b : SExpr)
    (h : Logic.not (Logic.equal a b) ≠ SExpr.nil) :
    Logic.equal a b = SExpr.nil := by
  by_cases hab : a == b <;> simp_all [Logic.equal, Logic.not, Logic.toBool]

/-- A FALSE `(not P)` literal value makes `P`'s value non-nil. (The step case's
    `(not (consp x))` literal: its falsity gives `consp xv ≠ nil`.) -/
theorem logic_not_nil_ne (p : SExpr) (h : Logic.not p = SExpr.nil) : p ≠ SExpr.nil := by
  intro hp
  simp [Logic.not, Logic.toBool, hp, SExpr.t] at h

/-- `consp` is two-valued: non-nil means `t`. -/
theorem logic_consp_ne_nil_t (v : SExpr) (h : Logic.consp v ≠ SExpr.nil) :
    Logic.consp v = SExpr.t := by
  cases v <;> simp_all [Logic.consp]

/-- `zp` from a false `integerp`: the ZP-COMPOUND-RECOGNIZER derivation —
    `(ZP u) ⇒ 'T` when `(INTEGERP u)` is false in scope (`zp` is `t` on
    non-integers; `toInt` coerces them to 0). -/
theorem logic_zp_of_integerp_nil (v : SExpr) (h : Logic.integerp v = SExpr.nil) :
    Logic.zp v = SExpr.t := by
  cases v with
  | atom a => cases a with
    | number n => cases n with
      | int k => simp [Logic.integerp, SExpr.t] at h
      | rational n d hc => simp [Logic.zp, Logic.toInt]
    | _ => simp [Logic.zp, Logic.toInt]
  | nil => simp [Logic.zp, Logic.toInt]
  | cons a b => simp [Logic.zp, Logic.toInt]

/-- `atom` from a false `consp`: ACL2's typeset resolution of `(ATOM u) ⇒ 'T`
    inside the FALSE branch of an if on `(CONSP u)` (assume-true-false). -/
theorem logic_atom_of_consp_nil (v : SExpr) (h : Logic.consp v = SExpr.nil) :
    Logic.atom v = SExpr.t := by
  cases v <;> simp_all [Logic.consp, Logic.atom]

/-- `true-listp` is two-valued: non-nil means `t` (from `trueListp_boolean`). -/
theorem logic_trueListp_ne_nil_t (v : SExpr) (h : Logic.trueListp v ≠ SExpr.nil) :
    Logic.trueListp v = SExpr.t :=
  (trueListp_boolean v).resolve_right h

/-- A non-nil `cdr` forces a cons (`cdr` of any non-cons is `nil`) —
    consp evidence from a truthy `(CDR t)` clause fact
    (sorting-completion-2, ORDERED-PERMS Subgoal *1/2.2's (NOT (CDR B))). -/
theorem logic_consp_of_cdr_ne_nil {b : SExpr}
    (h : Logic.cdr b ≠ SExpr.nil) : Logic.consp b = SExpr.t := by
  cases b <;> simp_all [Logic.cdr, Logic.consp]

/-- A NON-NIL proper list is a cons (type-set closure: TRUE-LISTP ∧ ≠nil ⇒
    CONSP — ORDERED-PERMS Subgoal *1/2.2's (CONSP (CDR B)) recognizer). -/
theorem logic_consp_of_trueListp_ne_nil {v : SExpr}
    (ht : Logic.trueListp v ≠ SExpr.nil) (hv : v ≠ SExpr.nil) :
    Logic.consp v = SExpr.t := by
  cases v <;> simp_all [Logic.trueListp, Logic.consp]

/-- `consp` of an `if` whose BOTH branches are conses (type-set's if-split —
    ORDERED-PERMS: (CONSP (IF … (CDR B) (CONS …))) ⇒ 'T). -/
theorem logic_consp_if_branches (c : Bool) {a b : SExpr}
    (ha : Logic.consp a = SExpr.t) (hb : Logic.consp b = SExpr.t) :
    Logic.consp (cond c a b) = SExpr.t := by
  cases c <;> simpa

/-- A FALSE `(IF v 'NIL 'T)` value (the clausify-expanded `(NOT v)`) makes
    `v` truthy. -/
theorem logic_ne_nil_of_if_nil_t_nil {v : SExpr}
    (h : (cond (Logic.toBool v) SExpr.nil SExpr.t) = SExpr.nil) :
    v ≠ SExpr.nil := by
  intro hv
  subst hv
  simp [Logic.toBool, SExpr.t] at h

/-- An ADJACENT duplicate literal frame collapses out of a disjunction:
    `(IF l 'T (IF l 'T r)) ≡ (IF l 'T r)` (remove-trivial-equivalences'
    add-literal dedup after a branch substitution — ORDERED-PERMS
    Subgoal 2's B ⇒ A). -/
theorem re_if_dup_adjacent (w : World) (env : Env) (l t r : SExpr)
    (vl : SExpr)
    (hl : ∃ N, ∀ f ≥ N, evalOpt f w env l = some vl)
    (vr : SExpr)
    (hr : ∃ N, ∀ f ≥ N, evalOpt f w env r = some vr) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "IF" }))
        (.cons l (.cons t (.cons (.cons (.atom (.symbol { name := "IF" }))
          (.cons l (.cons t (.cons r .nil)))) .nil))))
      = evalOpt f w env (.cons (.atom (.symbol { name := "IF" }))
          (.cons l (.cons t (.cons r .nil)))) := by
  obtain ⟨Nl, hl'⟩ := hl
  obtain ⟨Nr, hr'⟩ := hr
  refine ⟨Nl + Nr + 2, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  cases htb : Logic.toBool vl with
  | true =>
    rw [evalOpt_if_true g w env l t _ vl (hl' g (by omega)) htb,
        evalOpt_if_true g w env l t r vl (hl' g (by omega)) htb]
  | false =>
    have hnil : vl = SExpr.nil := by
      cases vl with
      | nil => rfl
      | atom a => simp [Logic.toBool] at htb
      | cons a b => simp [Logic.toBool] at htb
    subst hnil
    rw [evalOpt_if_false g w env l t _ (hl' g (by omega)),
        evalOpt_if_false g w env l t r (hl' g (by omega))]
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    rw [evalOpt_if_false g' w env l t r (hl' g' (by omega))]
    have h1 := hr' g' (by omega)
    have h2 := hr' (g' + 1) (by omega)
    rw [h1, h2]

/-- `equal`'s falsity is symmetric (orientation bridge for context facts). -/
theorem logic_equal_nil_comm {a b : SExpr}
    (h : Logic.equal a b = SExpr.nil) : Logic.equal b a = SExpr.nil := by
  by_cases hab : b = a
  · subst hab
    simp [Logic.equal, SExpr.t] at h
  · simp [Logic.equal, beq_eq_false_iff_ne.mpr hab]

/-- Component decode: a TRUE `equal` pins value equality. -/
theorem logic_eq_of_equal_t {a b : SExpr} (h : Logic.equal a b = SExpr.t) :
    a = b := by
  by_cases hab : a = b
  · exact hab
  · exfalso
    simp [Logic.equal, beq_eq_false_iff_ne.mpr hab, SExpr.t] at h

/-- rewrite-equal's cons-decomposition REFUTATION at the CAR components
    (sorting-completion-2, ORDERED-PERMS Subgoal *1/7'5' literal 10): ACL2
    rewrites the synthesized components `(car a)`/`(car b)` to `x`/`y` and
    refutes the component equality from the type-alist; the outer
    `(equal a b)` is then false — `a = b` would force `car a = car b`. -/
theorem logic_equal_nil_of_car_components {a b x y : SExpr}
    (h1 : Logic.car a = x) (h2 : Logic.car b = y)
    (h : Logic.equal x y = SExpr.nil) : Logic.equal a b = SExpr.nil := by
  by_cases hab : a = b
  · exfalso
    subst hab
    rw [← h1, ← h2] at h
    simp [Logic.equal, SExpr.t] at h
  · simp [Logic.equal, beq_eq_false_iff_ne.mpr hab]

/-- The CDR twin of `logic_equal_nil_of_car_components`. -/
theorem logic_equal_nil_of_cdr_components {a b x y : SExpr}
    (h1 : Logic.cdr a = x) (h2 : Logic.cdr b = y)
    (h : Logic.equal x y = SExpr.nil) : Logic.equal a b = SExpr.nil := by
  by_cases hab : a = b
  · exfalso
    subst hab
    rw [← h1, ← h2] at h
    simp [Logic.equal, SExpr.t] at h
  · simp [Logic.equal, beq_eq_false_iff_ne.mpr hab]

/-- rewrite-equal's POSITIVE cons-decomposition (ORDERED-PERMS Subgoal
    *1/7'5' literal 10, the (EQUAL A1 (CAR B))-true branch): both sides
    proper conses with equal cars and equal cdrs are equal —
    cons-extensionality, exactly ACL2's "equality of the components"
    conclusion. -/
theorem logic_equal_t_of_components {a b : SExpr}
    (ha : Logic.consp a = SExpr.t) (hb : Logic.consp b = SExpr.t)
    (hcar : Logic.car a = Logic.car b) (hcdr : Logic.cdr a = Logic.cdr b) :
    Logic.equal a b = SExpr.t := by
  cases a <;> cases b <;>
    simp_all [Logic.consp, Logic.car, Logic.cdr, Logic.equal, SExpr.t]

/-- `integerp` is two-valued: non-nil means `t`. -/
theorem logic_integerp_ne_nil_t (v : SExpr) (h : Logic.integerp v ≠ SExpr.nil) :
    Logic.integerp v = SExpr.t := by
  cases v with
  | nil => simp_all [Logic.integerp]
  | atom a =>
    cases a with
    | number n => cases n <;> simp_all [Logic.integerp]
    | _ => simp_all [Logic.integerp]
  | cons a b => simp_all [Logic.integerp]

/-- `consp ⇒ nil` from a TP whose type part is `integerp`: ACL2's type-set
    bit DISJOINTNESS (an integer is never a cons), consuming the STANDARD
    emitted TP corollary encoding `(IF (INTEGERP app) <bound> 'NIL)` lifted
    to `cond (toBool (integerp v)) thn nil = t` — the justification a
    `recognizer/false` node records as `type-prescription:<fn>` (e.g.
    `(CONSP (ACL2-COUNT …)) ⇒ 'NIL` in admission waterfalls). The bound
    part `thn` is irrelevant to the disjointness and stays abstract. -/
theorem logic_consp_nil_of_tp_integerp {v thn : SExpr}
    (h : cond (Logic.toBool (Logic.integerp v)) thn SExpr.nil = SExpr.t) :
    Logic.consp v = SExpr.nil := by
  cases v with
  | nil => rfl
  | atom a => rfl
  | cons a b => simp [Logic.integerp, Logic.toBool, SExpr.t] at h

/-- `binary-+`'s RANGE is numbers, never a cons — ACL2's native type-set
    knowledge of the primitive (`type-set-binary-+`), consumed by
    `recognizer/false` nodes like `(CONSP (BINARY-+ …)) ⇒ 'NIL` (admission
    waterfalls unfolding ACL2-COUNT). Value-level: `plus` lands in
    `mkNumber`, which returns a number atom on every branch. -/
theorem logic_consp_mkNumber (n : Int) (d : Nat) :
    Logic.consp (Logic.mkNumber n d) = SExpr.nil := by
  unfold Logic.mkNumber
  by_cases hd : d = 0
  · simp [hd, Logic.consp]
  · by_cases hd' : d / Nat.gcd n.natAbs d = 1 <;>
      simp [hd, hd', Logic.consp]

theorem logic_consp_plus_nil (a b : SExpr) :
    Logic.consp (Logic.plus a b) = SExpr.nil := by
  unfold Logic.plus
  apply logic_consp_mkNumber

/-- The LIFTED nonneg-int TP hypothesis pins its value to a Nat-image
    integer atom: `(bif toBool (integerp v) then not (lt v '0) else nil) = t`
    forces `v = int ↑n`. The DP prover's int-view pre-pass
    (`introDpIntValues`) obtains-and-substs this, turning linear-arithmetic
    leaves into PURE Int facts — no value-shape splits (the 7-value
    admission leaves that exceed the split bound). -/
theorem dp_nonneg_int_of_tp {v : SExpr}
    (h : (bif Logic.toBool (Logic.integerp v)
          then Logic.not (Logic.lt v (.atom (.number (.int 0))))
          else SExpr.nil) = SExpr.t) :
    ∃ n : Nat, v = .atom (.number (.int (n : Int))) := by
  cases v with
  | atom a => cases a with
    | number num => cases num with
      | int k =>
        refine ⟨k.toNat, ?_⟩
        by_cases hk : k < 0
        · exfalso
          simp [Logic.integerp, Logic.toBool, Logic.not, Logic.lt,
                Logic.toRat, hk, SExpr.t] at h
        · simp only [SExpr.atom.injEq, Atom.number.injEq, Number.int.injEq]
          omega
      | rational n d hc => simp [Logic.integerp, Logic.toBool] at h
    | symbol s => simp [Logic.integerp, Logic.toBool] at h
    | keyword s => simp [Logic.integerp, Logic.toBool] at h
    | string s => simp [Logic.integerp, Logic.toBool] at h
    | char c => simp [Logic.integerp, Logic.toBool] at h
  | nil => simp [Logic.integerp, Logic.toBool] at h
  | cons a b => simp [Logic.integerp, Logic.toBool] at h


/-- The POSITIVE-SUM vs '0 type-set cell (2b): `1 + a + b` with `a b`
    nonneg integers (their emitted TP shape) can never equal 0 — the
    second registered disjointness cell of the `equal/type-set-nil`
    recipe (the first is cons-vs-atom). -/
theorem logic_equal_nil_of_plus1_nonneg {a b : SExpr}
    (ha : (bif Logic.toBool (Logic.integerp a)
          then Logic.not (Logic.lt a (.atom (.number (.int 0))))
          else SExpr.nil) = SExpr.t)
    (hb : (bif Logic.toBool (Logic.integerp b)
          then Logic.not (Logic.lt b (.atom (.number (.int 0))))
          else SExpr.nil) = SExpr.t) :
    Logic.equal (Logic.plus (.atom (.number (.int 1))) (Logic.plus a b))
      (.atom (.number (.int 0))) = SExpr.nil := by
  obtain ⟨m, rfl⟩ := dp_nonneg_int_of_tp ha
  obtain ⟨n, rfl⟩ := dp_nonneg_int_of_tp hb
  rw [logic_plus_int, logic_plus_int]
  simp [Logic.equal, SExpr.t]
  omega

/-- The eval-equality form of the L-fold, for the chain-end bridge
    (rewrite.lisp:3791-3793 — the if-interp call-stack fold):
    `(EQUAL 'T (EQUAL a b)) ≡ (EQUAL a b)` given both args converge
    and `EQUAL` is unshadowed. -/
theorem re_equal_t_fold_l (w : World) (env : Env) (a b va vb : SExpr)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some va)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some vb) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "EQUAL" }))
        (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))
          (.cons (.cons (.atom (.symbol { name := "EQUAL" }))
            (.cons a (.cons b .nil))) .nil)))
      = evalOpt f w env (.cons (.atom (.symbol { name := "EQUAL" }))
          (.cons a (.cons b .nil))) := by
  have hInner := conv_builtin2 w env { name := "EQUAL" } a b va vb
    (Logic.equal va vb) (by decide) h_no_equal ha hb
    (callBuiltin_equal va vb)
  have hOuter := conv_builtin2 w env { name := "EQUAL" }
    (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))
    (.cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil)))
    SExpr.t (Logic.equal va vb) (Logic.equal SExpr.t (Logic.equal va vb))
    (by decide) h_no_equal (re_val_quote w env SExpr.t) hInner
    (callBuiltin_equal SExpr.t (Logic.equal va vb))
  exact fuel_eq_of_conv hOuter hInner (logic_equal_t_equal_l va vb)

/-! ### Last-position nil-drop pack (RESURRECTED at the final
close-out — killed at 910785a; the PCE tower is its now-reachable
consumer). -/

/-- `(if x 't 'nil)` converges to `(bif toBool vx then t else nil)` — the
    boolean wrapper's value form (the literal-boundary iff-normalization
    bridge's wrapper). -/
theorem re_val_if_t_nil (w : World) (env : Env) (x vx : SExpr)
    (hx : ∃ N, ∀ f ≥ N, evalOpt f w env x = some vx) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "IF" }))
        (.cons x (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))
          (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil)) .nil))))
      = some (bif Logic.toBool vx then .t else .nil) := by
  cases htb : Logic.toBool vx with
  | true =>
    have h := conv_if_true w env x
      (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))
      (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
      vx SExpr.t hx htb (re_val_quote w env SExpr.t)
    simpa using h
  | false =>
    have hva : vx = SExpr.nil := by
      cases vx <;> simp_all [Logic.toBool]
    subst hva
    obtain ⟨Na, ha'⟩ := hx
    refine ⟨Na + 2, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
    rw [evalOpt_if_false (g + 1) w env x _ _ (ha' (g + 1) (by omega))]
    simpa using evalOpt_quote g w env SExpr.nil

/-- The boolean wrapper is the identity on `Logic.equal`'s range (the
    last-position nil-drop's tail-frame change). -/
theorem logic_boolwrap_self_equal (a b : SExpr) :
    (bif Logic.toBool (Logic.equal a b) then SExpr.t else SExpr.nil)
      = Logic.equal a b := by
  by_cases h : (a == b) = true <;>
    simp [Logic.equal, h, Logic.toBool, SExpr.t]

/-- The boolean wrapper is the identity on the constant `'T` (the
    last-position nil-drop's trivial predecessor). -/
theorem logic_boolwrap_self_t :
    (bif Logic.toBool SExpr.t then SExpr.t else SExpr.nil) = SExpr.t := rfl

/-- The boolean wrapper is the identity on `Logic.not`'s range. -/
theorem logic_boolwrap_self_not (v : SExpr) :
    (bif Logic.toBool (Logic.not v) then SExpr.t else SExpr.nil)
      = Logic.not v := by
  cases v <;> rfl

/-- The boolean wrapper is the identity on a value pinned two-valued by
    the emitted BOOLEAN TP corollary (the last-position nil-drop's
    world-fn predecessor — PERM/MEMB class). -/
theorem logic_boolwrap_self_of_boolean_tp {v : SExpr}
    (h : (bif Logic.toBool (Logic.equal v SExpr.t) then SExpr.t
          else Logic.equal v SExpr.nil) = SExpr.t) :
    (bif Logic.toBool v then SExpr.t else SExpr.nil) = v := by
  by_cases hv : (v == SExpr.t) = true
  · have hveq := eq_of_beq hv
    subst hveq; rfl
  · have h1 : Logic.equal v SExpr.t = SExpr.nil := by
      simp [Logic.equal, hv]
    rw [h1] at h
    simp only [Logic.toBool, cond_false] at h
    have hnil : v = SExpr.nil := by
      by_cases h2 : (v == SExpr.nil) = true
      · exact eq_of_beq h2
      · simp [Logic.equal, h2, SExpr.t] at h
    subst hnil; rfl

/-- The SINGLE-SUMMAND positive-sum cell (`1 + u` vs `'0`, `u` a
    nonneg integer by its emitted TP shape) — RESURRECTED at the final
    close-out (killed at 910785a with the tpthm stack; its consumer,
    the PCE tower, is now reachable). -/
theorem logic_equal_nil_of_plus1_nonneg1 {u : SExpr}
    (hu : (bif Logic.toBool (Logic.integerp u)
          then Logic.not (Logic.lt u (.atom (.number (.int 0))))
          else SExpr.nil) = SExpr.t) :
    Logic.equal (Logic.plus (.atom (.number (.int 1))) u)
      (.atom (.number (.int 0))) = SExpr.nil := by
  obtain ⟨m, rfl⟩ := dp_nonneg_int_of_tp hu
  rw [logic_plus_int]
  simp [Logic.equal, SExpr.t]
  omega

/-- Term-vs-sum disjointness, RIGHT orientation (RESURRECTED, same
    round): `u ≠ 1 + u` for a nonneg-int `u` (its emitted TP shape) —
    `(equal u (+ 1 u)) = nil`. -/
theorem logic_equal_nil_of_plus1_self_r {a : SExpr}
    (ha : (bif Logic.toBool (Logic.integerp a)
          then Logic.not (Logic.lt a (.atom (.number (.int 0))))
          else SExpr.nil) = SExpr.t) :
    Logic.equal a (Logic.plus (.atom (.number (.int 1))) a)
      = SExpr.nil := by
  obtain ⟨m, rfl⟩ := dp_nonneg_int_of_tp ha
  rw [logic_plus_int]
  simp [Logic.equal]

/-- Term-vs-sum disjointness, LEFT orientation. -/
theorem logic_equal_nil_of_plus1_self_l {a : SExpr}
    (ha : (bif Logic.toBool (Logic.integerp a)
          then Logic.not (Logic.lt a (.atom (.number (.int 0))))
          else SExpr.nil) = SExpr.t) :
    Logic.equal (Logic.plus (.atom (.number (.int 1))) a) a
      = SExpr.nil := by
  obtain ⟨m, rfl⟩ := dp_nonneg_int_of_tp ha
  rw [logic_plus_int]
  simp [Logic.equal]

/-- `car` of a NON-cons defaults to `nil` (ACL2's completion axiom, value
    level — the type-set entry composition consumes it). -/
theorem logic_car_of_consp_nil {v : SExpr} (h : Logic.consp v = SExpr.nil) :
    Logic.car v = SExpr.nil := by
  cases v with
  | cons a b => simp [Logic.consp, SExpr.t] at h
  | nil => rfl
  | atom a => rfl

/-- A non-nil `true-listp` value that is not a cons IS `nil` (the
    type-set composition TRUE-LISTP ∧ ¬CONSP → = 'NIL). -/
theorem logic_nil_of_trueListp_consp_nil {v : SExpr}
    (ht : Logic.trueListp v ≠ SExpr.nil) (hc : Logic.consp v = SExpr.nil) :
    v = SExpr.nil := by
  cases v with
  | nil => rfl
  | atom a =>
    exact absurd (by simp [Logic.trueListp] :
      Logic.trueListp (SExpr.atom a) = SExpr.nil) ht
  | cons a b => simp [Logic.consp, SExpr.t] at hc

/-- The cdr of a true-list is a true-list (exact `t` — the type-set
    closure the TRUE-LISTP/CDR recognizer verdict consumes). -/
theorem logic_trueListp_cdr_t {v : SExpr}
    (h : Logic.trueListp v ≠ SExpr.nil) :
    Logic.trueListp (Logic.cdr v) = SExpr.t := by
  cases v with
  | nil => rfl
  | atom a =>
    exact absurd (by simp [Logic.trueListp] :
      Logic.trueListp (SExpr.atom a) = SExpr.nil) h
  | cons a d =>
    have hd : Logic.trueListp d ≠ SExpr.nil := by
      simpa [Logic.trueListp] using h
    rcases (Logic.trueListp_ne_nil_iff d).mp hd with ht
    simpa [Logic.cdr] using ht

/-- `cdr` of a NON-cons defaults to `nil`. -/
theorem logic_cdr_of_consp_nil {v : SExpr} (h : Logic.consp v = SExpr.nil) :
    Logic.cdr v = SExpr.nil := by
  cases v with
  | cons a b => simp [Logic.consp, SExpr.t] at h
  | nil => rfl
  | atom a => rfl

/-- The car-cdr-elim rule at the VALUE level: a consp value is rebuilt by
    `cons`/`car`/`cdr` — the destructor-elimination bridge's collapse of
    `(cons (car v) (cdr v))` back to `v`. -/
theorem logic_cons_car_cdr_of_consp {v : SExpr} (h : Logic.consp v ≠ SExpr.nil) :
    SExpr.cons (Logic.car v) (Logic.cdr v) = v := by
  cases v <;> simp_all [Logic.consp, Logic.car, Logic.cdr]

/-- `Logic.not` of a nil value is `t` (the false-`(consp v)` head literal of
    the destructor-elimination split). -/
theorem logic_not_t_of_nil {v : SExpr} (h : v = SExpr.nil) :
    Logic.not v = SExpr.t := by
  subst h; simp [Logic.not, Logic.toBool]

/-- `Logic.equal` is two-valued, so the `(if tst 't 'nil)` boolean-identity
    collapse (an `if1/boolean` node over an `equal` test) IS the test's value. -/
theorem cond_toBool_equal (a b : SExpr) :
    cond (Logic.toBool (Logic.equal a b)) SExpr.t SExpr.nil = Logic.equal a b := by
  by_cases h : a == b <;> simp [Logic.equal, Logic.toBool, h, SExpr.t]

/-- A concrete-fuel evaluation lifts to the fuel-robust form (fuel monotonicity) —
    the replay form of an `executable-counterpart` PREPROCESS step: ACL2 COMPUTED
    the value, and the kernel re-checks the same computation by reduction of
    `evalOpt` at the recorded fuel. -/
theorem conv_of_eval_at (N : Nat) (w : World) (env : Env) (t v : SExpr)
    (h : evalOpt N w env t = some v) :
    ∃ N', ∀ f ≥ N', evalOpt f w env t = some v :=
  ⟨N, fun f hf => evalOpt_ge_fuel N f w env t v h hf⟩

/-- Transport a convergence along an eval-equality: `eval a = eval b` and
    `eval b = some v` give `eval a = some v`. -/
theorem fuel_conv_of_eq {a b : Nat → Option SExpr} {v : SExpr}
    (hab : ∃ N, ∀ f ≥ N, a f = b f) (hb : ∃ N, ∀ f ≥ N, b f = some v) :
    ∃ N, ∀ f ≥ N, a f = some v := by
  obtain ⟨n1, h1⟩ := hab; obtain ⟨n2, h2⟩ := hb
  exact ⟨max n1 n2, fun f hf => (h1 f (by omega)).trans (h2 f (by omega))⟩

/-- PIN an existential convergence: the (choice-selected) value a term converges
    to. The driver pins each opaque user-fn occurrence's value this way from the
    bound totality hypotheses — no `Exists.elim` plumbing in the proof terms. -/
noncomputable def pinVal {w : World} {env : Env} {t : SExpr}
    (h : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env t = some v) : SExpr :=
  h.choose_spec.choose

theorem pinVal_spec {w : World} {env : Env} {t : SExpr}
    (h : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env t = some v) :
    ∃ N, ∀ f ≥ N, evalOpt f w env t = some (pinVal h) :=
  ⟨h.choose, h.choose_spec.choose_spec⟩

/-- `(not t) = nil` (the step case's discharged test literal). -/
theorem logic_not_t_nil : Logic.not SExpr.t = SExpr.nil := by
  simp [Logic.not, Logic.toBool]

/-! ## Clausify-bridge helpers (formula → clause composition, #53C)

The bridge consumes a PROVED child clause (`EvTrue w env (disjoin cl)`, G2)
and rebuilds the truth of the clausify INPUT term by mirroring
`clausify-input1`'s pure if-recursion. Since G3 Fragment B the recomposition
is ONE instantiation of the once-proved `clausifyPure_sound` bridge lemma
(`Replay/ClausifyBridge.lean`); the value helpers below serve its proof and
the rest of the replay layer. -/

/-- `toBool` of a non-nil value is `true`. -/
theorem toBool_true_of_ne_nil {v : SExpr} (h : v ≠ SExpr.nil) :
    Logic.toBool v = true := by cases v <;> simp_all [Logic.toBool]

/-- A FALSY `(endp v)` IS a truthy `(consp v)` — `endp` is the
    guard-relaxed `atom` (logically `(not (consp _))`). The induction
    decrease consumes ruling tests of either spelling (R2: isort's fns test
    `endp` where perm's tested `consp`; the case tree records the STRIPPED
    positive test with a false sign). -/
theorem consp_toBool_of_endp_nil {v : SExpr}
    (h : Logic.endp v = SExpr.nil) :
    Logic.toBool (Logic.consp v) = true := by
  cases v <;> simp_all [Logic.endp, Logic.consp, Logic.toBool]

/-- `endp` as `not ∘ consp` — the DP leaf tactic's bridge (S1 2026-07-23):
    `endp`'s own match is stuck on a symbolic value, but through
    `not`/`consp` the `toBool` bridges and `split_ifs` machinery apply. -/
theorem logic_endp_eq_not_consp (s : SExpr) :
    Logic.endp s = Logic.not (Logic.consp s) := by
  cases s <;> rfl

/-- RUNE `if-same-branches` (`if1/same-branches`): `(if c a a) ⇒ a` — the
    branch value is the if value whichever way the test goes; the test must
    converge (lazy `if` evaluates it first). Term-to-term. -/
theorem re_if_same (w : World) (env : Env) (c a cv av : SExpr)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some cv)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some av) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons a (.cons a .nil))))
      = evalOpt f w env a := by
  have hconv : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons a (.cons a .nil)))) = some av := by
    obtain ⟨Nc, hc'⟩ := hc; obtain ⟨Na, ha'⟩ := ha
    refine ⟨max Nc Na + 1, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    by_cases hnil : cv = SExpr.nil
    · subst hnil
      rw [evalOpt_if_false g w env c a a (hc' g (by omega))]
      exact ha' g (by omega)
    · rw [evalOpt_if_true g w env c a a cv (hc' g (by omega))
            (toBool_true_of_ne_nil hnil)]
      exact ha' g (by omega)
  exact fuel_eq_of_conv hconv ha rfl

/-- The identity fuel-robust eval-equality (an if-finish branch with no
    effective rewrites). -/
theorem fuel_eq_refl (a : Nat → Option SExpr) : ∃ N, ∀ f ≥ N, a f = a f :=
  ⟨0, fun _ _ => rfl⟩

/-- A standard BOOLEAN type-prescription corollary (lifted) makes the
    `(if tst 't 'nil)` identity collapse (an `if1/boolean` node over a
    USER-FN test) the test's value: `v` is `t` or `nil`, and the cond agrees
    with `v` in both cases. The `Logic.equal`-test twin is
    `cond_toBool_equal`. -/
theorem cond_toBool_of_tp_boolean (v : SExpr) {X : SExpr}
    (h : cond (Logic.toBool (Logic.equal v SExpr.t)) X (Logic.equal v SExpr.nil)
         = SExpr.t) :
    cond (Logic.toBool v) SExpr.t SExpr.nil = v := by
  by_cases hv : v = SExpr.t
  · subst hv; simp [Logic.toBool, SExpr.t]
  · have h1 : (v == SExpr.t) = false := beq_eq_false_iff_ne.mpr hv
    have hnil : v = SExpr.nil := by
      by_cases h2 : v = SExpr.nil
      · exact h2
      · have h2' : (v == SExpr.nil) = false := beq_eq_false_iff_ne.mpr h2
        simp [Logic.equal, Logic.toBool, h1, h2', SExpr.t] at h
    subst hnil; simp [Logic.toBool]

/-- A standard BOOLEAN type-prescription corollary
    `(IF (EQUAL v 'T) 'T (EQUAL v 'NIL))` (lifted) being true pins a non-nil
    value to `t` — the truthy `type-alist` verdict's two-valuedness source
    (ACL2 recorded the fn's :TYPE-PRESCRIPTION rune on the node). -/
theorem tp_cond_boolean_t (v : SExpr) {X : SExpr}
    (h : cond (Logic.toBool (Logic.equal v SExpr.t)) X (Logic.equal v SExpr.nil)
         = SExpr.t)
    (hne : v ≠ SExpr.nil) : v = SExpr.t := by
  by_cases hv : v = SExpr.t
  · exact hv
  · have h1 : (v == SExpr.t) = false := beq_eq_false_iff_ne.mpr hv
    have h2 : (v == SExpr.nil) = false := beq_eq_false_iff_ne.mpr hne
    simp [Logic.equal, Logic.toBool, h1, h2, SExpr.t] at h

/-! Two-valuedness DISJUNCTION sources (G1 rung 1, inc-2 — the IF-headed
    `if1/boolean` test derives booleanness structurally from its branches). -/

theorem logic_equal_t_or_nil (a b : SExpr) :
    Logic.equal a b = SExpr.t ∨ Logic.equal a b = SExpr.nil := by
  by_cases h : a == b <;> simp [Logic.equal, h]

/-- The boolean-TP corollary fact as a disjunction. -/
theorem tp_boolean_t_or_nil (v : SExpr) {X : SExpr}
    (h : cond (Logic.toBool (Logic.equal v SExpr.t)) X (Logic.equal v SExpr.nil)
         = SExpr.t) :
    v = SExpr.t ∨ v = SExpr.nil := by
  by_cases hv : v = SExpr.t
  · exact Or.inl hv
  · refine Or.inr ?_
    by_cases h2 : v = SExpr.nil
    · exact h2
    · have h1 : (v == SExpr.t) = false := beq_eq_false_iff_ne.mpr hv
      have h2' : (v == SExpr.nil) = false := beq_eq_false_iff_ne.mpr h2
      simp [Logic.equal, Logic.toBool, h1, h2', SExpr.t] at h

/-- An if with two-valued branches is two-valued. -/
theorem cond_t_or_nil {x y : SExpr} (b : Bool)
    (hx : x = SExpr.t ∨ x = SExpr.nil) (hy : y = SExpr.t ∨ y = SExpr.nil) :
    cond b x y = SExpr.t ∨ cond b x y = SExpr.nil := by
  cases b
  · simpa using hy
  · simpa using hx

/-- The `if1/boolean` closer from a two-valuedness disjunction. -/
theorem cond_toBool_of_t_or_nil {v : SExpr}
    (h : v = SExpr.t ∨ v = SExpr.nil) :
    cond (Logic.toBool v) SExpr.t SExpr.nil = v := by
  rcases h with h | h <;> simp [h, Logic.toBool, SExpr.t]

theorem logic_lt_t_or_nil (a b : SExpr) :
    Logic.lt a b = SExpr.t ∨ Logic.lt a b = SExpr.nil := by
  simp only [Logic.lt]
  split <;> simp

theorem t_t_or_nil : SExpr.t = SExpr.t ∨ SExpr.t = SExpr.nil := Or.inl rfl
theorem nil_t_or_nil : SExpr.nil = SExpr.t ∨ SExpr.nil = SExpr.nil := Or.inr rfl

/-- `lexorder` is BOOLEAN-VALUED: every branch returns `.t` or `.nil` (it is
    ACL2's total-order predicate). By `fun_induction` on `lexorder`'s own case
    structure: each leaf is a literal `.t`/`.nil` or an `if _ then .t else .nil`
    (closed after `split`); the cons recursion is closed by the IH. -/
theorem lexorder_boolean (a b : SExpr) :
    lexorder a b = SExpr.t ∨ lexorder a b = SExpr.nil := by
  fun_induction lexorder a b <;>
    first
      | assumption
      | exact Or.inl rfl
      | exact Or.inr rfl

/-- Two-valuedness of a `lexorder` test: `cond (toBool (lexorder a b)) t nil`
    is just `lexorder a b` — the `if1/boolean` closer for a LEXORDER-valued
    test (the builtin twin of `cond_toBool_of_tp_boolean`, no TP needed since
    `lexorder` is provably boolean). -/
theorem cond_toBool_lexorder (a b : SExpr) :
    cond (Logic.toBool (lexorder a b)) SExpr.t SExpr.nil = lexorder a b := by
  rcases lexorder_boolean a b with h | h <;> simp [h, Logic.toBool, SExpr.t]

/-- ACL2's built-in LEXORDER-ANTI-SYMMETRIC in the TRUTHY shape the DP leaf
    hypotheses take after `Logic.not` unfolds (`≠ nil` rather than `= t`;
    bridged by `lexorder_boolean`). Part of the DP order theory: tau closes
    clauses with contradictory `lexorder` literal sets using its built-in
    lexorder theorems, so the carve-out's decision procedure carries the same
    facts, kernel-proved (S1, 2026-07-23). -/
theorem lexorder_antisymm_ne {a b : SExpr}
    (h1 : lexorder a b ≠ SExpr.nil) (h2 : lexorder b a ≠ SExpr.nil) : a = b :=
  lexorder_antisymm
    ((lexorder_boolean a b).resolve_right h1)
    ((lexorder_boolean b a).resolve_right h2)

/-- ACL2's built-in LEXORDER-TOTAL in CONDITIONAL form (no disjunction, so
    `simp_all` can consume it as a rewrite): a nil verdict one way forces `t`
    the other way. DP order theory, as `lexorder_antisymm_ne`. -/
theorem lexorder_total_ne {a b : SExpr}
    (h : lexorder a b = SExpr.nil) : lexorder b a = SExpr.t := by
  rcases lexorder_total a b with ht | ht
  · rw [h] at ht; exact absurd ht (by simp [SExpr.t])
  · exact ht

/-- `Logic.equal` is symmetric at the value level — if-interp's COMMUTATIVE
    assumption matching (`if-interp-assumed-value2`), re-derived by the
    branch-split composer for `assumed`-verdict tests. -/
theorem logic_equal_comm (a b : SExpr) : Logic.equal a b = Logic.equal b a := by
  by_cases h : a = b
  · subst h; rfl
  · have h1 : (a == b) = false := beq_eq_false_iff_ne.mpr h
    have h2 : (b == a) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
    simp [Logic.equal, h1, h2]

/-- CONDITIONAL branch congruence for a lazy `if` with an UNRESOLVED test (the
    if-finish recipe, R1 conditional-congruence): each branch is rewritten
    under the test's corresponding assumption — the then-chain may consume the
    test's truth (ACL2's assume-true-false), the else-chain its falsity. -/
theorem evalOpt_congr_if_branches_cond (w : World) (env : Env)
    (c thn els thn' els' : SExpr) (vc : SExpr)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some vc)
    (hthen : vc ≠ SExpr.nil →
      ∃ N, ∀ f ≥ N, evalOpt f w env thn = evalOpt f w env thn')
    (helse : vc = SExpr.nil →
      ∃ N, ∀ f ≥ N, evalOpt f w env els = evalOpt f w env els') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons thn (.cons els .nil))))
      = evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons thn' (.cons els' .nil)))) := by
  obtain ⟨Nc, hc⟩ := hc
  by_cases hv : vc = SExpr.nil
  · obtain ⟨Ne, he⟩ := helse hv
    refine ⟨max Nc Ne + 1, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [evalOpt_if_false g w env c thn els (hv ▸ hc g (by omega)),
        evalOpt_if_false g w env c thn' els' (hv ▸ hc g (by omega))]
    exact he g (by omega)
  · obtain ⟨Nt, ht⟩ := hthen hv
    refine ⟨max Nc Nt + 1, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [evalOpt_if_true g w env c thn els vc (hc g (by omega)) (toBool_true_of_ne_nil hv),
        evalOpt_if_true g w env c thn' els' vc (hc g (by omega)) (toBool_true_of_ne_nil hv)]
    exact ht g (by omega)

/-- A truthy `not` pins its argument to nil. -/
theorem arg_nil_of_not_truthy {v : SExpr} (h : Logic.not v ≠ SExpr.nil) :
    v = SExpr.nil := by
  cases v <;> simp_all [Logic.not, Logic.toBool]

/-- Two value characterizations of the SAME evaluation pin the same value. -/
theorem val_unique {a : Nat → Option SExpr} {u v : SExpr}
    (hu : ∃ N, ∀ f ≥ N, a f = some u) (hv : ∃ N, ∀ f ≥ N, a f = some v) : u = v := by
  obtain ⟨n1, h1⟩ := hu; obtain ⟨n2, h2⟩ := hv
  exact Option.some.inj ((h1 (n1+n2) (by omega)).symm.trans (h2 (n1+n2) (by omega)))

/-! ## Type-prescription discharge (the TP prover; lifter sprint 2026-07-06)

The value-PREDICATE-carrying analogue of the totality walk: prove
`∃ v, P v ∧ <conv to v>` FORWARD through the body (quote leaves by ground
decision, if-branches under the verdict, self-calls by the strong IH), then
pin ANY convergence value of a call by determinism (`val_unique`) plus
argument strictness. `P` is the EMITTED `:TYPE-PRESCRIPTION` corollary,
value-lifted — the prover consumes ACL2's type facts; it never infers types
(CLAUDE.md). Forward-only: no evaluator inversion beyond argument
strictness. -/

/-- Strengthened convergence: `t` converges (fuel-stably) to a value
    satisfying `P`. -/
def ConvToP (w : World) (env : Env) (t : SExpr) (P : SExpr → Prop) : Prop :=
  ∃ v, P v ∧ ∃ N, ∀ f ≥ N, evalOpt f w env t = some v

/-- ACL2 two-valuedness of the test verdict: not truthy means exactly nil. -/
theorem nil_of_toBool_false {v : SExpr} (h : Logic.toBool v = false) :
    v = SExpr.nil := by
  cases v <;> simp [Logic.toBool] at h ⊢

theorem convP_quote (w : World) (env : Env) (v : SExpr) (P : SExpr → Prop)
    (hP : P v) :
    ConvToP w env
      (.cons (.atom (.symbol { name := "QUOTE" })) (.cons v .nil)) P :=
  ⟨v, hP, re_val_quote w env v⟩

/-- `if` under a CHARACTERIZED test verdict: the taken branch's predicate
    carries to the whole `if`. -/
theorem convP_if_split (w : World) (env : Env) (c t e vc : SExpr)
    (P : SExpr → Prop)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some vc)
    (ht : Logic.toBool vc = true → ConvToP w env t P)
    (he : Logic.toBool vc = false → ConvToP w env e P) :
    ConvToP w env
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons c (.cons t (.cons e .nil)))) P := by
  cases hb : Logic.toBool vc with
  | true =>
    obtain ⟨v, hP, hv⟩ := ht hb
    exact ⟨v, hP, fuel_conv_of_eq (re_if_true w env c t e vc v hc hb hv) hv⟩
  | false =>
    obtain ⟨v, hP, hv⟩ := he hb
    exact ⟨v, hP,
      fuel_conv_of_eq (re_if_false w env c t e v
        (nil_of_toBool_false hb ▸ hc) hv) hv⟩

/-- `convP_if_split` over an EXISTENTIAL test verdict (an opaque user-fn
    test, converged by the totality walk) — the TP analogue of
    `conv_if_split_ex`. -/
theorem convP_if_split_ex (w : World) (env : Env) (c t e : SExpr)
    (P : SExpr → Prop)
    (hc : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env c = some v)
    (ht : ∀ vc, ConvTo w env c vc → Logic.toBool vc = true →
      ConvToP w env t P)
    (he : ∀ vc, ConvTo w env c vc → Logic.toBool vc = false →
      ConvToP w env e P) :
    ConvToP w env
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons c (.cons t (.cons e .nil)))) P := by
  obtain ⟨N, vc, hvc⟩ := hc
  exact convP_if_split w env c t e vc P ⟨N, hvc⟩
    (ht vc ⟨N, hvc⟩) (he vc ⟨N, hvc⟩)

/-- The VALUE-DETERMINED `if`: when both branch VALUES are given by total
    Lean terms, the whole `if` converges to the Lean `ite` of the test
    verdict. The exec-corr walk's if move (two-stage lift, D1/D2 of
    docs/plans/2026-07-06_two-stage-lift.md): each branch PROOF is
    conditional on its verdict (the untaken branch is never demanded — the
    recursive branch's IH needs the ruling test), but both values exist
    unconditionally because the exec function is total. -/
theorem conv_if_lift (w : World) (env : Env) (c t e vc vt ve : SExpr)
    (hc : ConvTo w env c vc)
    (ht : Logic.toBool vc = true → ConvTo w env t vt)
    (he : Logic.toBool vc = false → ConvTo w env e ve) :
    ConvTo w env
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons c (.cons t (.cons e .nil))))
      (if Logic.toBool vc = true then vt else ve) := by
  cases hb : Logic.toBool vc with
  | true =>
    rw [if_pos rfl]
    exact conv_if_true w env c t e vc vt hc hb (ht hb)
  | false =>
    rw [if_neg Bool.false_ne_true]
    obtain ⟨Nc, hc'⟩ := nil_of_toBool_false hb ▸ hc
    obtain ⟨Ne, he'⟩ := he hb
    refine ⟨max Nc Ne + 1, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [evalOpt_if_false g w env c t e (hc' g (by omega))]
    exact he' g (by omega)

/-- A defined 2-ary call inherits the body's predicate (self-calls inside
    the TP walk: `hbody` is the IH at the argument values). -/
theorem convP_defn_2 (w : World) (env : Env) (s : Symbol)
    (arg1 arg2 av1 av2 : SExpr) (formal1 formal2 : Symbol) (body : SExpr)
    (P : SExpr → Prop)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2], body))
    (h1 : ∃ N, ∀ f ≥ N, evalOpt f w env arg1 = some av1)
    (h2 : ∃ N, ∀ f ≥ N, evalOpt f w env arg2 = some av2)
    (hbody : ConvToP w (bindArgs [formal1, formal2] [av1, av2]) body P) :
    ConvToP w env
      (.cons (.atom (.symbol s)) (.cons arg1 (.cons arg2 .nil))) P := by
  obtain ⟨v, hP, hv⟩ := hbody
  exact ⟨v, hP, conv_defn_2 w env s arg1 arg2 av1 av2 formal1 formal2 body v
    h_ns h_def h1 h2 hv⟩

/-- A defined 1-ary call inherits the body's predicate. -/
theorem convP_defn_1 (w : World) (env : Env) (s : Symbol)
    (arg av : SExpr) (formal : Symbol) (body : SExpr) (P : SExpr → Prop)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal], body))
    (h1 : ∃ N, ∀ f ≥ N, evalOpt f w env arg = some av)
    (hbody : ConvToP w (bindArgs [formal] [av]) body P) :
    ConvToP w env (.cons (.atom (.symbol s)) (.cons arg .nil)) P := by
  obtain ⟨v, hP, hv⟩ := hbody
  exact ⟨v, hP, conv_defn_1 w env s arg av formal body v h_ns h_def h1 hv⟩

/-- 2-ary argument STRICTNESS at one fuel step: a converged non-special
    application's arguments each converged. -/
theorem evalOpt_app2_args (f : Nat) (w : World) (env : Env)
    (s : Symbol) (a1 a2 v : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h : evalOpt (f + 1) w env
      (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 .nil))) = some v) :
    (∃ u, evalOpt f w env a1 = some u) ∧
    (∃ u, evalOpt f w env a2 = some u) := by
  rw [show evalOpt (f + 1) w env
        (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 .nil)))
        = evalOptStep (evalOpt f) w env
            (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 .nil))) from rfl] at h
  unfold evalOptStep at h
  simp only [Symbol.isNamed, SExpr.toList?] at h
  obtain ⟨hq, hi, hl, hls⟩ := h_ns
  simp only [Symbol.isNamed] at hq hi hl hls
  simp only [hq, hi, hl, hls, Bool.or_eq_true, Bool.false_eq_true, or_self,
             ↓reduceIte] at h
  cases hu1 : evalOpt f w env a1 with
  | none => simp [List.mapM, List.mapM.loop, hu1] at h
  | some u1 =>
    cases hu2 : evalOpt f w env a2 with
    | none => simp [List.mapM, List.mapM.loop, hu1, hu2] at h
    | some u2 => exact ⟨⟨u1, rfl⟩, ⟨u2, rfl⟩⟩

/-- Fix a per-fuel existential value by fuel monotonicity. -/
theorem conv_fix {w : World} {e : Env} {t : SExpr}
    (h : ∃ N, ∀ f ≥ N, ∃ u, evalOpt f w e t = some u) :
    ∃ N, ∃ u, ∀ f ≥ N, evalOpt f w e t = some u := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨u, hu⟩ := hN N (le_refl N)
  exact ⟨N, u, fun f hf => evalOpt_ge_fuel N f w e t u hu hf⟩

/-- 2-ary argument strictness, convergence form. -/
theorem conv_args2_of_conv_app (w : World) (env : Env) (s : Symbol)
    (a1 a2 v : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 .nil))) = some v) :
    (∃ N, ∃ u, ∀ f ≥ N, evalOpt f w env a1 = some u) ∧
    (∃ N, ∃ u, ∀ f ≥ N, evalOpt f w env a2 = some u) := by
  obtain ⟨N, hN⟩ := h
  constructor
  · exact conv_fix ⟨N, fun f hf =>
      (evalOpt_app2_args f w env s a1 a2 v h_ns (hN (f + 1) (by omega))).1⟩
  · exact conv_fix ⟨N, fun f hf =>
      (evalOpt_app2_args f w env s a1 a2 v h_ns (hN (f + 1) (by omega))).2⟩

/-- The TP-HYPOTHESIS assembly, 2-ary: from the predicate-carrying body walk,
    ANY value a call converges to satisfies `P` — argument strictness recovers
    the argument values, the walk pins ONE convergent value with `P`, and
    determinism (`val_unique`) identifies them (the `dis_memb_tp` route,
    mechanized). The conclusion is EXACTLY the driver's `tp:` hypothesis shape
    (`mkTpHypType`) with `P v := <lifted corollary> = t`. -/
theorem tp_hyp_2_of_body (w : World) (s : Symbol) (formal1 formal2 : Symbol)
    (body : SExpr) (P : SExpr → Prop)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2], body))
    (hbody : ∀ av1 av2 : SExpr,
      ConvToP w (bindArgs [formal1, formal2] [av1, av2]) body P) :
    ∀ (env' : Env) (a0 a1 v : SExpr),
      (∃ N, ∀ f ≥ N, evalOpt f w env'
        (.cons (.atom (.symbol s)) (.cons a0 (.cons a1 .nil))) = some v) →
      P v := by
  intro env' a0 a1 v h
  obtain ⟨⟨N0, u0, h0⟩, ⟨N1, u1, h1⟩⟩ :=
    conv_args2_of_conv_app w env' s a0 a1 v h_ns h
  obtain ⟨u, hPu, hu⟩ := hbody u0 u1
  have happ := conv_defn_2 w env' s a0 a1 u0 u1 formal1 formal2 body u
    h_ns h_def ⟨N0, h0⟩ ⟨N1, h1⟩ hu
  exact (val_unique h happ) ▸ hPu

/-- The TP-hypothesis assembly, 1-ary. -/
theorem tp_hyp_1_of_body (w : World) (s : Symbol) (formal : Symbol)
    (body : SExpr) (P : SExpr → Prop)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal], body))
    (hbody : ∀ av : SExpr, ConvToP w (bindArgs [formal] [av]) body P) :
    ∀ (env' : Env) (a0 v : SExpr),
      (∃ N, ∀ f ≥ N, evalOpt f w env'
        (.cons (.atom (.symbol s)) (.cons a0 .nil)) = some v) →
      P v := by
  intro env' a0 v h
  obtain ⟨N0, u0, h0⟩ := conv_fix (conv_arg1_of_conv_app w env' s a0 v h_ns h)
  obtain ⟨u, hPu, hu⟩ := hbody u0
  have happ := conv_defn_1 w env' s a0 u0 formal body u h_ns h_def ⟨N0, h0⟩ hu
  exact (val_unique h happ) ▸ hPu

/-- The TP body induction, measure on the FIRST formal: strong induction on
    its count, the second argument inner-∀ (the `memb_body_bool` spine,
    predicate-generic). -/
theorem tp_2_rec (formal1 formal2 : Symbol) (body : SExpr) (w : World)
    (P : SExpr → Prop)
    (step : ∀ av1 : SExpr,
      (∀ bv : SExpr, bv.consCount < av1.consCount → ∀ cv : SExpr,
        ConvToP w (bindArgs [formal1, formal2] [bv, cv]) body P) →
      ∀ av2 : SExpr,
        ConvToP w (bindArgs [formal1, formal2] [av1, av2]) body P) :
    ∀ av1 av2 : SExpr,
      ConvToP w (bindArgs [formal1, formal2] [av1, av2]) body P :=
  consCount_strong_induction
    (fun av1 => ∀ av2, ConvToP w (bindArgs [formal1, formal2] [av1, av2]) body P)
    step

/-- The TP body induction, measure on the SECOND formal. -/
theorem tp_2_rec_snd (formal1 formal2 : Symbol) (body : SExpr) (w : World)
    (P : SExpr → Prop)
    (step : ∀ av2 : SExpr,
      (∀ cv : SExpr, cv.consCount < av2.consCount → ∀ bv : SExpr,
        ConvToP w (bindArgs [formal1, formal2] [bv, cv]) body P) →
      ∀ av1 : SExpr,
        ConvToP w (bindArgs [formal1, formal2] [av1, av2]) body P) :
    ∀ av1 av2 : SExpr,
      ConvToP w (bindArgs [formal1, formal2] [av1, av2]) body P :=
  fun av1 av2 =>
    consCount_strong_induction
      (fun av2 => ∀ av1, ConvToP w (bindArgs [formal1, formal2] [av1, av2]) body P)
      step av2 av1

/-- The TP body induction, 1-ary. -/
theorem tp_1_rec (formal : Symbol) (body : SExpr) (w : World)
    (P : SExpr → Prop)
    (step : ∀ av : SExpr,
      (∀ bv : SExpr, bv.consCount < av.consCount →
        ConvToP w (bindArgs [formal] [bv]) body P) →
      ConvToP w (bindArgs [formal] [av]) body P) :
    ∀ av : SExpr, ConvToP w (bindArgs [formal] [av]) body P :=
  consCount_strong_induction
    (fun av => ConvToP w (bindArgs [formal] [av]) body P) step

/-- Transport non-nil-ness along a value equation. -/
theorem ne_nil_of_eq {v w : SExpr} (h : v = w) (hw : w ≠ SExpr.nil) :
    v ≠ SExpr.nil := h ▸ hw

/-- A truthy argument makes `not` nil. -/
theorem not_nil_of_truthy {v : SExpr} (h : v ≠ SExpr.nil) :
    Logic.not v = SExpr.nil := by
  cases v <;> simp_all [Logic.not, Logic.toBool]

/-- The converse two-valued decode: a truthy `Logic.not` pins its argument to
    `nil` (the multi-literal induction walk's negative-literal peel). -/
theorem nil_of_logic_not_ne_nil {v : SExpr} (h : Logic.not v ≠ SExpr.nil) :
    v = SExpr.nil := by
  by_cases hv : v = SExpr.nil
  · exact hv
  · exact absurd (not_nil_of_truthy hv) h

/-- `Logic.implies` IS the value of its ground-zero unfold body
    `(if p (if q 't 'nil) 't)` under the `cond` value lift — the recipe fact
    for the `:DEFINITION implies` rune (`implies` is an `evalOpt` builtin, not
    a world definition; adding it to the world would shadow the builtin). -/
theorem logic_implies_cond (p q : SExpr) :
    Logic.implies p q
      = (bif Logic.toBool p then (bif Logic.toBool q then SExpr.t else SExpr.nil)
         else SExpr.t) := by
  simp only [Logic.implies, Bool.cond_eq_ite]

/-- `Logic.iff` IS the value of its ground-zero unfold body
    `(if p (if q 't 'nil) (if q 'nil 't))` under the `cond` value lift — the
    recipe fact for the `:DEFINITION iff` rune (`iff` is an `evalOpt` builtin,
    not a world definition; the preprocess boot-strap non-rec arm adopts this
    body — `emit/expand-abbreviations/nonrec-body`, G1 iff rung). -/
theorem logic_iff_cond (p q : SExpr) :
    Logic.iff p q
      = (bif Logic.toBool p then (bif Logic.toBool q then SExpr.t else SExpr.nil)
         else (bif Logic.toBool q then SExpr.nil else SExpr.t)) := by
  simp only [Logic.iff, Bool.cond_eq_ite]

end ACL2.Replay
