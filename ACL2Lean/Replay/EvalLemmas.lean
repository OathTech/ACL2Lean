/-
  Proof rules for ACL2 proof replay.

  Each theorem corresponds to a proof tree node type. These are the
  building blocks: the proof-producing checker applies one theorem
  per proof tree node, composing them to prove the target theorem.

  Each PROVED theorem is proved once and reused for all ACL2 theorems.
  No inference, no search — purely deterministic replay.

  Every lemma here is sorry-free. (The old generic `replaceSubterm` / `pcEq` /
  `EvalCtx` / `evalOpt_ctx_pcEq` "T1 congruence" cluster and the `substVar`
  value-substitution layer were deleted — they were dead code from an earlier
  value-computation framing, superseded by the arity-specific congruence lemmas
  and the `substTerm` term-substitution layer.)

  ⚠ SCHEMATIC DISCIPLINE (the bar these lemmas must meet): the eventual replay
  driver is a fixed function from a proof-tree node `(rune, lhs, rhs, subst)` to
  a Lean proof term. So each node must be replayed by a FIXED per-rune procedure
  applying that rune's rule (definition unfold via `substTerm`; with-lemma via
  the imported lemma's value-equality; recognizer/if/equal-self via step lemmas)
  lifted by congruence — NOT by computing concrete values and matching them, and
  NOT by invoking a "functionality" fact the rune does not supply. Lemmas/uses
  that compute-and-match values are non-schematic and must be reworked; see the
  ⚠ NON-SCHEMATIC tags in Imported/SimpleWorld.lean.
-/
import ACL2Lean.EvalOpt
import ACL2Lean.Count
import ACL2Lean.LexorderOrder
import Mathlib.Tactic

namespace ACL2.Replay

open ACL2

/-! ## Layer 0: Pure infrastructure (no evalOpt) -/

/-- T9: Compose two fuel-existential properties. -/
theorem fuel_join {P Q : Nat → Prop}
    (h1 : ∃ N, ∀ f ≥ N, P f) (h2 : ∃ N, ∀ f ≥ N, Q f) :
    ∃ N, ∀ f ≥ N, P f ∧ Q f := by
  obtain ⟨n1, h1⟩ := h1
  obtain ⟨n2, h2⟩ := h2
  exact ⟨max n1 n2, fun f hf => ⟨h1 f (by omega), h2 f (by omega)⟩⟩

/-- T16: Chain two fuel-existential equalities by transitivity. -/
theorem fuel_chain_eq {α : Type} {a b c : Nat → α}
    (h1 : ∃ N, ∀ f ≥ N, a f = b f) (h2 : ∃ N, ∀ f ≥ N, b f = c f) :
    ∃ N, ∀ f ≥ N, a f = c f := by
  obtain ⟨n1, h1⟩ := h1
  obtain ⟨n2, h2⟩ := h2
  exact ⟨max n1 n2, fun f hf => (h1 f (by omega)).trans (h2 f (by omega))⟩

/-- Symmetry of a fuel-existential equality (for orienting `fuel_chain_eq`
    links, e.g. the rule-application recipe's rhs bridge). -/
theorem fuel_eq_symm {α : Type} {a b : Nat → α}
    (h : ∃ N, ∀ f ≥ N, a f = b f) : ∃ N, ∀ f ≥ N, b f = a f := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, fun f hf => (h f hf).symm⟩

/-- T13: CONSP of a cons cell is T. -/
theorem consp_cons (a b : SExpr) : Logic.consp (.cons a b) = SExpr.t := by
  simp [Logic.consp]

/-- T17: acl2-numberp elimination — if the value is a number per ACL2's test,
    then it's structurally .atom (.number n). -/
theorem acl2_numberp_elim (v : SExpr)
    (h : (match v with | .atom (.number _) => SExpr.t | _ => SExpr.nil) = SExpr.t) :
    ∃ n : Number, v = .atom (.number n) := by
  match v with
  | .atom (.number n) => exact ⟨n, rfl⟩
  | .nil => simp [SExpr.t] at h
  | .atom (.symbol _) => simp [SExpr.t] at h
  | .atom (.string _) => simp [SExpr.t] at h
  | .atom (.keyword _) => simp [SExpr.t] at h
  | .atom (.char _) => simp [SExpr.t] at h
  | .cons _ _ => simp [SExpr.t] at h

/-! ## Layer 1: evalOpt atomic steps -/

/-- T7a: Quote evaluates to the quoted value. -/
theorem evalOpt_quote (f : Nat) (w : World) (env : Env) (v : SExpr) :
    evalOpt (f + 1) w env
      (.cons (.atom (.symbol { name := "QUOTE" })) (.cons v .nil))
    = some v := by
  simp [evalOpt, evalOptStep, Symbol.isNamed]

/-- T7b: Variable lookup (bound). -/
theorem evalOpt_var (f : Nat) (w : World) (env : Env) (s : Symbol) (v : SExpr)
    (h : env.get? s = some v) :
    evalOpt (f + 1) w env (.atom (.symbol s)) = some v := by
  simp [evalOpt, evalOptStep, h]

/-- T18: Variable lookup (unbound, not t). -/
theorem evalOpt_var_unbound (f : Nat) (w : World) (env : Env) (s : Symbol)
    (h : env.get? s = none) (h_not_t : s.isNamed "T" = false) :
    evalOpt (f + 1) w env (.atom (.symbol s)) = some .nil := by
  simp [evalOpt, evalOptStep, h, h_not_t]

/-- T5a: IF with truthy test takes the then-branch. -/
theorem evalOpt_if_true (f : Nat) (w : World) (env : Env)
    (c t e : SExpr) (cv : SExpr)
    (hc : evalOpt f w env c = some cv)
    (ht : Logic.toBool cv = true) :
    evalOpt (f + 1) w env
      (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil))))
    = evalOpt f w env t := by
  show evalOptStep (evalOpt f) w env _ = _
  unfold evalOptStep
  simp only [Symbol.isNamed, SExpr.toList?]
  show (evalOpt f w env c).bind (fun cv => if Logic.toBool cv then
    evalOpt f w env t else evalOpt f w env e) = evalOpt f w env t
  rw [hc]; simp only [Option.bind]; rw [if_pos ht]

/-- T5b: IF with nil test takes the else-branch. -/
theorem evalOpt_if_false (f : Nat) (w : World) (env : Env)
    (c t e : SExpr)
    (hc : evalOpt f w env c = some .nil) :
    evalOpt (f + 1) w env
      (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil))))
    = evalOpt f w env e := by
  show evalOptStep (evalOpt f) w env _ = _
  unfold evalOptStep
  simp only [Symbol.isNamed, SExpr.toList?]
  show (evalOpt f w env c).bind (fun cv => if Logic.toBool cv then
    evalOpt f w env t else evalOpt f w env e) = evalOpt f w env e
  rw [hc]; simp only [Option.bind, Logic.toBool]; rfl

/-- T6: Builtin function call (function not in world.defs). -/
theorem evalOpt_builtin_1 (f : Nat) (w : World) (env : Env)
    (s : Symbol) (arg : SExpr) (av : SExpr)
    (h_not_special : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
                     s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_not_def : w.defs.get? s = none)
    (h_arg : evalOpt f w env arg = some av) :
    evalOpt (f + 1) w env (.cons (.atom (.symbol s)) (.cons arg .nil))
    = callBuiltin s.name [av] := by
  show evalOptStep (evalOpt f) w env _ = _
  unfold evalOptStep
  simp only [Symbol.isNamed, SExpr.toList?]
  obtain ⟨hq, hi, hl, hls⟩ := h_not_special
  simp only [Symbol.isNamed] at hq hi hl hls
  simp only [hq, hi, hl, hls, Bool.or_eq_true, Bool.false_eq_true, or_self, ↓reduceIte]
  -- Now in the function call branch
  show (do
    let argVals ← [arg].mapM (evalOpt f w env ·)
    match w.defs.get? s with
    | some (formals, body) =>
      if formals.length = argVals.length then evalOpt f w (bindArgs formals argVals) body
      else none
    | none => callBuiltin s.name argVals) = _
  simp only [List.mapM, List.mapM.loop, h_arg, List.reverse, List.reverseAux,
             Option.pure_def, h_not_def]
  rfl

/-- T6b: Builtin 2-arg function call (for EQUAL, BINARY-+, etc.). -/
theorem evalOpt_builtin_2 (f : Nat) (w : World) (env : Env)
    (s : Symbol) (arg1 arg2 : SExpr) (av1 av2 : SExpr)
    (h_not_special : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
                     s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_not_def : w.defs.get? s = none)
    (h_arg1 : evalOpt f w env arg1 = some av1)
    (h_arg2 : evalOpt f w env arg2 = some av2) :
    evalOpt (f + 1) w env (.cons (.atom (.symbol s)) (.cons arg1 (.cons arg2 .nil)))
    = callBuiltin s.name [av1, av2] := by
  show evalOptStep (evalOpt f) w env _ = _
  unfold evalOptStep
  simp only [Symbol.isNamed, SExpr.toList?]
  obtain ⟨hq, hi, hl, hls⟩ := h_not_special
  simp only [Symbol.isNamed] at hq hi hl hls
  simp only [hq, hi, hl, hls, Bool.or_eq_true, Bool.false_eq_true, or_self, ↓reduceIte]
  show (do
    let argVals ← [arg1, arg2].mapM (evalOpt f w env ·)
    match w.defs.get? s with
    | some (formals, body) =>
      if formals.length = argVals.length then evalOpt f w (bindArgs formals argVals) body
      else none
    | none => callBuiltin s.name argVals) = _
  simp only [List.mapM, List.mapM.loop, h_arg1, h_arg2, List.reverse, List.reverseAux,
             Option.pure_def, h_not_def]
  rfl

/-- T6c: ARGUMENT STRICTNESS (1-arg application, INVERSION): a non-special
    1-arg application that converges at fuel `f+1` evaluated its argument at
    fuel `f` (call-by-value — the argument is forced before the defn/builtin
    dispatch). Consumed by the type-prescription hypothesis adapters: the
    driver's `htp` antecedent asserts only that `(fn a0)` converges, and the
    hand dischargers need `a0`'s convergence. -/
theorem evalOpt_app1_arg (f : Nat) (w : World) (env : Env)
    (s : Symbol) (arg v : SExpr)
    (h_not_special : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
                     s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h : evalOpt (f + 1) w env (.cons (.atom (.symbol s)) (.cons arg .nil)) = some v) :
    ∃ u, evalOpt f w env arg = some u := by
  cases hu : evalOpt f w env arg with
  | some u => exact ⟨u, rfl⟩
  | none =>
    exfalso
    rw [show evalOpt (f + 1) w env (.cons (.atom (.symbol s)) (.cons arg .nil))
          = evalOptStep (evalOpt f) w env (.cons (.atom (.symbol s)) (.cons arg .nil)) from rfl] at h
    unfold evalOptStep at h
    simp only [Symbol.isNamed, SExpr.toList?] at h
    obtain ⟨hq, hi, hl, hls⟩ := h_not_special
    simp only [Symbol.isNamed] at hq hi hl hls
    simp only [hq, hi, hl, hls, Bool.or_eq_true, Bool.false_eq_true, or_self,
               ↓reduceIte] at h
    simp [List.mapM, List.mapM.loop, hu] at h

/-- `evalOpt_app1_arg`, lifted to eventual convergence: if the application
    converges (to a fixed value), the argument converges at every sufficiently
    large fuel (value possibly per-fuel — `conv_fix`/`dis_*` re-fix it). -/
theorem conv_arg1_of_conv_app (w : World) (env : Env) (s : Symbol) (arg v : SExpr)
    (h_not_special : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
                     s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env (.cons (.atom (.symbol s)) (.cons arg .nil)) = some v) :
    ∃ N, ∀ f ≥ N, ∃ u, evalOpt f w env arg = some u := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun f hf => evalOpt_app1_arg f w env s arg v h_not_special
    (hN (f + 1) (by omega))⟩

/-- T7c: Number literal evaluates to itself. -/
theorem evalOpt_number (f : Nat) (w : World) (env : Env) (n : Number) :
    evalOpt (f + 1) w env (.atom (.number n)) = some (.atom (.number n)) := by
  simp [evalOpt, evalOptStep]

/-- T7d: Nil evaluates to nil. -/
theorem evalOpt_nil (f : Nat) (w : World) (env : Env) :
    evalOpt (f + 1) w env .nil = some .nil := by
  simp [evalOpt, evalOptStep]

/-- T4a: Definition expansion for a 1-arg user-defined function. -/
theorem evalOpt_defn_1 (f : Nat) (w : World) (env : Env)
    (s : Symbol) (arg : SExpr) (av : SExpr)
    (formal : Symbol) (body : SExpr)
    (h_not_special : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
                     s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal], body))
    (h_arg : evalOpt f w env arg = some av) :
    evalOpt (f + 1) w env (.cons (.atom (.symbol s)) (.cons arg .nil))
    = evalOpt f w (bindArgs [formal] [av]) body := by
  show evalOptStep (evalOpt f) w env _ = _
  unfold evalOptStep
  simp only [Symbol.isNamed, SExpr.toList?]
  obtain ⟨hq, hi, hl, hls⟩ := h_not_special
  simp only [Symbol.isNamed] at hq hi hl hls
  simp only [hq, hi, hl, hls, Bool.or_eq_true, Bool.false_eq_true, or_self, ↓reduceIte]
  show (do
    let argVals ← [arg].mapM (evalOpt f w env ·)
    match w.defs.get? s with
    | some (formals, body) =>
      if formals.length = argVals.length then evalOpt f w (bindArgs formals argVals) body
      else none
    | none => callBuiltin s.name argVals) = _
  simp only [List.mapM, List.mapM.loop, h_arg, List.reverse, List.reverseAux,
             Option.pure_def, h_def]
  rfl

/-- T4b: Definition expansion for a 2-arg user-defined function. -/
theorem evalOpt_defn_2 (f : Nat) (w : World) (env : Env)
    (s : Symbol) (arg1 arg2 : SExpr) (av1 av2 : SExpr)
    (formal1 formal2 : Symbol) (body : SExpr)
    (h_not_special : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
                     s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2], body))
    (h_arg1 : evalOpt f w env arg1 = some av1)
    (h_arg2 : evalOpt f w env arg2 = some av2) :
    evalOpt (f + 1) w env (.cons (.atom (.symbol s)) (.cons arg1 (.cons arg2 .nil)))
    = evalOpt f w (bindArgs [formal1, formal2] [av1, av2]) body := by
  show evalOptStep (evalOpt f) w env _ = _
  unfold evalOptStep
  simp only [Symbol.isNamed, SExpr.toList?]
  obtain ⟨hq, hi, hl, hls⟩ := h_not_special
  simp only [Symbol.isNamed] at hq hi hl hls
  simp only [hq, hi, hl, hls, Bool.or_eq_true, Bool.false_eq_true, or_self, ↓reduceIte]
  show (do
    let argVals ← [arg1, arg2].mapM (evalOpt f w env ·)
    match w.defs.get? s with
    | some (formals, body) =>
      if formals.length = argVals.length then evalOpt f w (bindArgs formals argVals) body
      else none
    | none => callBuiltin s.name argVals) = _
  simp only [List.mapM, List.mapM.loop, h_arg1, h_arg2, List.reverse, List.reverseAux,
             Option.pure_def, h_def]
  rfl

/-- T4c: Definition expansion for a 3-arg user-defined function. -/
theorem evalOpt_defn_3 (f : Nat) (w : World) (env : Env)
    (s : Symbol) (arg1 arg2 arg3 : SExpr) (av1 av2 av3 : SExpr)
    (formal1 formal2 formal3 : Symbol) (body : SExpr)
    (h_not_special : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
                     s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2, formal3], body))
    (h_arg1 : evalOpt f w env arg1 = some av1)
    (h_arg2 : evalOpt f w env arg2 = some av2)
    (h_arg3 : evalOpt f w env arg3 = some av3) :
    evalOpt (f + 1) w env
      (.cons (.atom (.symbol s)) (.cons arg1 (.cons arg2 (.cons arg3 .nil))))
    = evalOpt f w (bindArgs [formal1, formal2, formal3] [av1, av2, av3]) body := by
  show evalOptStep (evalOpt f) w env _ = _
  unfold evalOptStep
  simp only [Symbol.isNamed, SExpr.toList?]
  obtain ⟨hq, hi, hl, hls⟩ := h_not_special
  simp only [Symbol.isNamed] at hq hi hl hls
  simp only [hq, hi, hl, hls, Bool.or_eq_true, Bool.false_eq_true, or_self, ↓reduceIte]
  show (do
    let argVals ← [arg1, arg2, arg3].mapM (evalOpt f w env ·)
    match w.defs.get? s with
    | some (formals, body) =>
      if formals.length = argVals.length then evalOpt f w (bindArgs formals argVals) body
      else none
    | none => callBuiltin s.name argVals) = _
  simp only [List.mapM, List.mapM.loop, h_arg1, h_arg2, h_arg3, List.reverse,
             List.reverseAux, Option.pure_def, h_def]
  rfl

/-! ## Layer 1b: Arity-specific congruence (faithful T1 replacement)

  ACL2's rewriting lifts a subterm rewrite through the surrounding term by
  *congruence*: if a sub-expression `a` rewrites to `a'`, then `(fn … a …)`
  rewrites to `(fn … a' …)`. We replay this with one congruence lemma per
  application shape (unary / binary-left / binary-right). Each is provable
  directly from `evalOptStep`: a non-special application's value depends on
  its argument expression only through that argument's evaluation, so equal
  argument-evaluations give equal application-evaluations — UNCONDITIONALLY
  (no convergence side-condition). This is the deterministic, sorry-free
  congruence the driver uses to lift a rule's value-equality through the
  surrounding term (replacing the deleted generic-context machinery). -/

/-- One-step unary congruence: `(fn a)` and `(fn a')` agree at `f+1`
    whenever `a` and `a'` agree at `f`. -/
theorem evalOpt_congr_unary_step (f : Nat) (w : World) (env : Env)
    (fn : Symbol) (a a' : SExpr)
    (h_ns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
            fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (h : evalOpt f w env a = evalOpt f w env a') :
    evalOpt (f + 1) w env (.cons (.atom (.symbol fn)) (.cons a .nil))
    = evalOpt (f + 1) w env (.cons (.atom (.symbol fn)) (.cons a' .nil)) := by
  show evalOptStep (evalOpt f) w env _ = evalOptStep (evalOpt f) w env _
  unfold evalOptStep
  simp only [Symbol.isNamed, SExpr.toList?]
  obtain ⟨hq, hi, hl, hls⟩ := h_ns
  simp only [Symbol.isNamed] at hq hi hl hls
  simp only [hq, hi, hl, hls, Bool.or_eq_true, Bool.false_eq_true, or_self, ↓reduceIte]
  show (do
    let argVals ← [a].mapM (evalOpt f w env ·)
    match w.defs.get? fn with
    | some (formals, body) =>
      if formals.length = argVals.length then evalOpt f w (bindArgs formals argVals) body
      else none
    | none => callBuiltin fn.name argVals) = (do
    let argVals ← [a'].mapM (evalOpt f w env ·)
    match w.defs.get? fn with
    | some (formals, body) =>
      if formals.length = argVals.length then evalOpt f w (bindArgs formals argVals) body
      else none
    | none => callBuiltin fn.name argVals)
  simp only [List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind, h]

/-- One-step binary left-congruence: `(fn a b)` and `(fn a' b)` agree at `f+1`
    whenever `a` and `a'` agree at `f`. -/
theorem evalOpt_congr_binary_left_step (f : Nat) (w : World) (env : Env)
    (fn : Symbol) (a a' b : SExpr)
    (h_ns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
            fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (h : evalOpt f w env a = evalOpt f w env a') :
    evalOpt (f + 1) w env (.cons (.atom (.symbol fn)) (.cons a (.cons b .nil)))
    = evalOpt (f + 1) w env (.cons (.atom (.symbol fn)) (.cons a' (.cons b .nil))) := by
  show evalOptStep (evalOpt f) w env _ = evalOptStep (evalOpt f) w env _
  unfold evalOptStep
  simp only [Symbol.isNamed, SExpr.toList?]
  obtain ⟨hq, hi, hl, hls⟩ := h_ns
  simp only [Symbol.isNamed] at hq hi hl hls
  simp only [hq, hi, hl, hls, Bool.or_eq_true, Bool.false_eq_true, or_self, ↓reduceIte]
  show (do
    let argVals ← [a, b].mapM (evalOpt f w env ·)
    match w.defs.get? fn with
    | some (formals, body) =>
      if formals.length = argVals.length then evalOpt f w (bindArgs formals argVals) body
      else none
    | none => callBuiltin fn.name argVals) = (do
    let argVals ← [a', b].mapM (evalOpt f w env ·)
    match w.defs.get? fn with
    | some (formals, body) =>
      if formals.length = argVals.length then evalOpt f w (bindArgs formals argVals) body
      else none
    | none => callBuiltin fn.name argVals)
  simp only [List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind, h]

/-- One-step binary right-congruence: `(fn a b)` and `(fn a b')` agree at `f+1`
    whenever `b` and `b'` agree at `f`. -/
theorem evalOpt_congr_binary_right_step (f : Nat) (w : World) (env : Env)
    (fn : Symbol) (a b b' : SExpr)
    (h_ns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
            fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (h : evalOpt f w env b = evalOpt f w env b') :
    evalOpt (f + 1) w env (.cons (.atom (.symbol fn)) (.cons a (.cons b .nil)))
    = evalOpt (f + 1) w env (.cons (.atom (.symbol fn)) (.cons a (.cons b' .nil))) := by
  show evalOptStep (evalOpt f) w env _ = evalOptStep (evalOpt f) w env _
  unfold evalOptStep
  simp only [Symbol.isNamed, SExpr.toList?]
  obtain ⟨hq, hi, hl, hls⟩ := h_ns
  simp only [Symbol.isNamed] at hq hi hl hls
  simp only [hq, hi, hl, hls, Bool.or_eq_true, Bool.false_eq_true, or_self, ↓reduceIte]
  show (do
    let argVals ← [a, b].mapM (evalOpt f w env ·)
    match w.defs.get? fn with
    | some (formals, body) =>
      if formals.length = argVals.length then evalOpt f w (bindArgs formals argVals) body
      else none
    | none => callBuiltin fn.name argVals) = (do
    let argVals ← [a, b'].mapM (evalOpt f w env ·)
    match w.defs.get? fn with
    | some (formals, body) =>
      if formals.length = argVals.length then evalOpt f w (bindArgs formals argVals) body
      else none
    | none => callBuiltin fn.name argVals)
  simp only [List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind, h]

/-- Fuel-existential unary congruence (for chaining with `fuel_chain_eq`). -/
theorem evalOpt_congr_unary (w : World) (env : Env)
    (fn : Symbol) (a a' : SExpr)
    (h_ns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
            fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env a = evalOpt f w env a') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol fn)) (.cons a .nil))
      = evalOpt f w env (.cons (.atom (.symbol fn)) (.cons a' .nil)) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 1, fun f hf => ?_⟩
  match f with
  | f + 1 => exact evalOpt_congr_unary_step f w env fn a a' h_ns (hN f (by omega))

/-- Fuel-existential binary left-congruence. -/
theorem evalOpt_congr_binary_left (w : World) (env : Env)
    (fn : Symbol) (a a' b : SExpr)
    (h_ns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
            fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env a = evalOpt f w env a') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol fn)) (.cons a (.cons b .nil)))
      = evalOpt f w env (.cons (.atom (.symbol fn)) (.cons a' (.cons b .nil))) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 1, fun f hf => ?_⟩
  match f with
  | f + 1 => exact evalOpt_congr_binary_left_step f w env fn a a' b h_ns (hN f (by omega))

/-- Fuel-existential binary right-congruence. -/
theorem evalOpt_congr_binary_right (w : World) (env : Env)
    (fn : Symbol) (a b b' : SExpr)
    (h_ns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
            fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env b = evalOpt f w env b') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol fn)) (.cons a (.cons b .nil)))
      = evalOpt f w env (.cons (.atom (.symbol fn)) (.cons a (.cons b' .nil))) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 1, fun f hf => ?_⟩
  match f with
  | f + 1 => exact evalOpt_congr_binary_right_step f w env fn a b b' h_ns (hN f (by omega))

/-- One-step STRICT ternary congruence, arg 1. `h_ns` excludes `IF` (the lazy
    arity-3 special form), so the strict argument-evaluation path applies. -/
theorem evalOpt_congr_ternary1_step (f : Nat) (w : World) (env : Env)
    (fn : Symbol) (a a' b c : SExpr)
    (h_ns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
            fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (h : evalOpt f w env a = evalOpt f w env a') :
    evalOpt (f + 1) w env (.cons (.atom (.symbol fn)) (.cons a (.cons b (.cons c .nil))))
    = evalOpt (f + 1) w env (.cons (.atom (.symbol fn)) (.cons a' (.cons b (.cons c .nil)))) := by
  show evalOptStep (evalOpt f) w env _ = evalOptStep (evalOpt f) w env _
  unfold evalOptStep
  simp only [Symbol.isNamed, SExpr.toList?]
  obtain ⟨hq, hi, hl, hls⟩ := h_ns
  simp only [Symbol.isNamed] at hq hi hl hls
  simp only [hq, hi, hl, hls, Bool.or_eq_true, Bool.false_eq_true, or_self, ↓reduceIte]
  show (do
    let argVals ← [a, b, c].mapM (evalOpt f w env ·)
    match w.defs.get? fn with
    | some (formals, body) =>
      if formals.length = argVals.length then evalOpt f w (bindArgs formals argVals) body
      else none
    | none => callBuiltin fn.name argVals) = (do
    let argVals ← [a', b, c].mapM (evalOpt f w env ·)
    match w.defs.get? fn with
    | some (formals, body) =>
      if formals.length = argVals.length then evalOpt f w (bindArgs formals argVals) body
      else none
    | none => callBuiltin fn.name argVals)
  simp only [List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind, h]

/-- One-step STRICT ternary congruence, arg 2. -/
theorem evalOpt_congr_ternary2_step (f : Nat) (w : World) (env : Env)
    (fn : Symbol) (a b b' c : SExpr)
    (h_ns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
            fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (h : evalOpt f w env b = evalOpt f w env b') :
    evalOpt (f + 1) w env (.cons (.atom (.symbol fn)) (.cons a (.cons b (.cons c .nil))))
    = evalOpt (f + 1) w env (.cons (.atom (.symbol fn)) (.cons a (.cons b' (.cons c .nil)))) := by
  show evalOptStep (evalOpt f) w env _ = evalOptStep (evalOpt f) w env _
  unfold evalOptStep
  simp only [Symbol.isNamed, SExpr.toList?]
  obtain ⟨hq, hi, hl, hls⟩ := h_ns
  simp only [Symbol.isNamed] at hq hi hl hls
  simp only [hq, hi, hl, hls, Bool.or_eq_true, Bool.false_eq_true, or_self, ↓reduceIte]
  show (do
    let argVals ← [a, b, c].mapM (evalOpt f w env ·)
    match w.defs.get? fn with
    | some (formals, body) =>
      if formals.length = argVals.length then evalOpt f w (bindArgs formals argVals) body
      else none
    | none => callBuiltin fn.name argVals) = (do
    let argVals ← [a, b', c].mapM (evalOpt f w env ·)
    match w.defs.get? fn with
    | some (formals, body) =>
      if formals.length = argVals.length then evalOpt f w (bindArgs formals argVals) body
      else none
    | none => callBuiltin fn.name argVals)
  simp only [List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind, h]

/-- One-step STRICT ternary congruence, arg 3. -/
theorem evalOpt_congr_ternary3_step (f : Nat) (w : World) (env : Env)
    (fn : Symbol) (a b c c' : SExpr)
    (h_ns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
            fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (h : evalOpt f w env c = evalOpt f w env c') :
    evalOpt (f + 1) w env (.cons (.atom (.symbol fn)) (.cons a (.cons b (.cons c .nil))))
    = evalOpt (f + 1) w env (.cons (.atom (.symbol fn)) (.cons a (.cons b (.cons c' .nil)))) := by
  show evalOptStep (evalOpt f) w env _ = evalOptStep (evalOpt f) w env _
  unfold evalOptStep
  simp only [Symbol.isNamed, SExpr.toList?]
  obtain ⟨hq, hi, hl, hls⟩ := h_ns
  simp only [Symbol.isNamed] at hq hi hl hls
  simp only [hq, hi, hl, hls, Bool.or_eq_true, Bool.false_eq_true, or_self, ↓reduceIte]
  show (do
    let argVals ← [a, b, c].mapM (evalOpt f w env ·)
    match w.defs.get? fn with
    | some (formals, body) =>
      if formals.length = argVals.length then evalOpt f w (bindArgs formals argVals) body
      else none
    | none => callBuiltin fn.name argVals) = (do
    let argVals ← [a, b, c'].mapM (evalOpt f w env ·)
    match w.defs.get? fn with
    | some (formals, body) =>
      if formals.length = argVals.length then evalOpt f w (bindArgs formals argVals) body
      else none
    | none => callBuiltin fn.name argVals)
  simp only [List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind, h]

/-- Fuel-existential strict ternary congruence, arg 1 (non-IF arity-3 heads). -/
theorem evalOpt_congr_ternary1 (w : World) (env : Env)
    (fn : Symbol) (a a' b c : SExpr)
    (h_ns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
            fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env a = evalOpt f w env a') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol fn)) (.cons a (.cons b (.cons c .nil))))
      = evalOpt f w env (.cons (.atom (.symbol fn)) (.cons a' (.cons b (.cons c .nil)))) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 1, fun f hf => ?_⟩
  match f with
  | f + 1 => exact evalOpt_congr_ternary1_step f w env fn a a' b c h_ns (hN f (by omega))

/-- Fuel-existential strict ternary congruence, arg 2. -/
theorem evalOpt_congr_ternary2 (w : World) (env : Env)
    (fn : Symbol) (a b b' c : SExpr)
    (h_ns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
            fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env b = evalOpt f w env b') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol fn)) (.cons a (.cons b (.cons c .nil))))
      = evalOpt f w env (.cons (.atom (.symbol fn)) (.cons a (.cons b' (.cons c .nil)))) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 1, fun f hf => ?_⟩
  match f with
  | f + 1 => exact evalOpt_congr_ternary2_step f w env fn a b b' c h_ns (hN f (by omega))

/-- Fuel-existential strict ternary congruence, arg 3. -/
theorem evalOpt_congr_ternary3 (w : World) (env : Env)
    (fn : Symbol) (a b c c' : SExpr)
    (h_ns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
            fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env c = evalOpt f w env c') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol fn)) (.cons a (.cons b (.cons c .nil))))
      = evalOpt f w env (.cons (.atom (.symbol fn)) (.cons a (.cons b (.cons c' .nil)))) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 1, fun f hf => ?_⟩
  match f with
  | f + 1 => exact evalOpt_congr_ternary3_step f w env fn a b c c' h_ns (hN f (by omega))

/-! ## Free-variable congruence (relate a function body's `bindArgs` env to the
    caller env on the term's free variables)

  Ported from the prior hand-proof branch (sorry-free there); the call-case
  `show` is adapted to the current `callBuiltin : … → Option SExpr` shape. Used by
  the step case to relate `evalOpt … (bindArgs …) body` (after a definition
  unfold) back to `evalOpt … e body` — both read the env only at the body's free
  variables, which agree. -/

/-! Free variables of a term that `evalOpt` may read. Head symbols and `quote`
    bodies are not reads. (Over-approximates inside LET; combined with `WellScoped`.)

    INVARIANT (unconditional — S2 audit F1, 2026-07-25): `freeVars` OVER-
    approximates the ambient-env reads of EVERY term, `WellScoped` or not. Several
    driver gates (`replayExecGround`'s closedness check, the TP `liftable`
    filter, the DP variable collection) read `freeVars` standalone, with no
    `WellScoped` companion — an under-approximation there mis-states facts. So the
    lambda arm keeps the body's residual (formal-filtered) free variables:
    on a `WellScoped`-certified application the residual is `[]` and the arm
    degenerates to the actuals (see `freeVars_lam_closed`). -/
mutual
def freeVars : SExpr → List Symbol
  | .atom (.symbol s) => [s]
  | .cons (.atom (.symbol q)) rest => if q.isNamed "QUOTE" then [] else freeVarsSpine rest
  -- LAMBDA application (the translated `let`, S2 2026-07-24): the ACTUALS
  -- are read from the ambient env, plus any body variable NOT bound by the
  -- binder's formals (none, when `WellScoped` holds; a malformed formals list
  -- filters nothing — over-approximation is the safe direction). This arm
  -- also matches a cons head that is not a LAMBDA; there `evalOpt` is
  -- `none` in every env, so any over-approximation is sound.
  | .cons (.cons (.atom (.symbol _)) (.cons formalsE (.cons lamBody .nil))) argsExpr =>
      (match lamFormals? formalsE with
       | some fs => (freeVars lamBody).filter (fun s => !fs.contains s)
       | none => freeVars lamBody) ++ freeVarsSpine argsExpr
  | _ => []
def freeVarsSpine : SExpr → List Symbol
  | .cons a rest => freeVars a ++ freeVarsSpine rest
  | _ => []
end

/-! A term whose evaluation reads the ambient env only at `freeVars`, and in
    which `substTerm` may therefore substitute without capture: no surface
    LET/LET*, no bare LAMBDA in term position, and every LAMBDA application
    well-formed with a body closed under its own formals. (Renamed from the
    pre-S2 `NoLet` once the predicate began ADMITTING a binding form —
    end-of-arc cleanup, 2026-07-25.) -/
mutual
def WellScoped : SExpr → Bool
  | .cons (.atom (.symbol q)) rest =>
      -- a BARE `(LAMBDA formals body)` in term position is rejected too
      -- (S2 audit F2, 2026-07-25): it is not an evaluable term, and blessing
      -- it would let `substTerm` rewrite into its FORMALS list. Only the
      -- APPLIED form (the cons-headed arm below) is a translated `let`.
      if q.isNamed "LET" || q.isNamed "LET*" || q.isNamed "LAMBDA" then false
      else if q.isNamed "QUOTE" then true else WellScopedSpine rest
  -- a LAMBDA application IS a translated `let` (S2 2026-07-24). Admitted
  -- exactly when ACL2's own translate invariant holds — well-formed formals
  -- and a body whose free variables are all formals — which is what makes
  -- the binder invisible to the two lemmas below: `substTerm` rewrites only
  -- the actuals, and the free-variable congruence needs the body to read
  -- nothing but the formals (bound identically under either env).
  | .cons (.cons (.atom (.symbol lam)) (.cons formalsE (.cons lamBody .nil))) argsExpr =>
      lam.isNamed "LAMBDA"
        && (match lamFormals? formalsE with
            | some formals => (freeVars lamBody).all (fun s => formals.contains s)
            | none => false)
        && WellScoped lamBody && WellScopedSpine argsExpr
  -- any other cons head is not an application `evalOpt` can run
  | .cons (.cons _ _) _ => false
  | _ => true
def WellScopedSpine : SExpr → Bool
  | .cons a rest => WellScoped a && WellScopedSpine rest
  | _ => true
end

/-- `mapM` agrees when the functions agree on every list element. -/
theorem mapM_congr_mem {g1 g2 : SExpr → Option SExpr} :
    ∀ {l : List SExpr}, (∀ a ∈ l, g1 a = g2 a) → l.mapM g1 = l.mapM g2
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons, h x (List.mem_cons_self ..),
      mapM_congr_mem (fun a ha => h a (List.mem_cons_of_mem _ ha))]

/-- The spine's free vars are the union of its elements' free vars. -/
theorem freeVarsSpine_eq : ∀ {argsExpr : SExpr} {args : List SExpr},
    argsExpr.toList? = some args → freeVarsSpine argsExpr = args.flatMap freeVars
  | .nil, _, h => by simp_all [SExpr.toList?, freeVarsSpine]
  | .atom _, _, h => by simp_all [SExpr.toList?]
  | .cons hd tl, args, h => by
      simp only [SExpr.toList?] at h
      match htl : tl.toList? with
      | some rest =>
        simp only [htl, bind, Option.bind, Option.some.injEq] at h
        subst_vars
        simp [freeVarsSpine, List.flatMap_cons, freeVarsSpine_eq htl]
      | none => simp [htl, bind, Option.bind] at h

/-- An element of an argument spine's `toList?` has its free vars within the
    spine's free vars. -/
theorem freeVars_subset_spine {a : SExpr} {s : Symbol} {argsExpr : SExpr} {args : List SExpr}
    (h : argsExpr.toList? = some args) (ha : a ∈ args) (hs : s ∈ freeVars a) :
    s ∈ freeVarsSpine argsExpr := by
  rw [freeVarsSpine_eq h]; exact List.mem_flatMap.mpr ⟨a, ha, hs⟩

/-- If a spine is LET-free, so is each of its `toList?` elements. -/
theorem WellScoped_of_mem_spine : ∀ {argsExpr : SExpr} {args : List SExpr},
    argsExpr.toList? = some args → WellScopedSpine argsExpr = true → ∀ a ∈ args, WellScoped a = true
  | .nil, _, h, _ => by simp_all [SExpr.toList?]
  | .atom _, _, h, _ => by simp_all [SExpr.toList?]
  | .cons hd tl, args, h, hnl => by
      simp only [SExpr.toList?] at h
      match htl : tl.toList? with
      | some rest =>
        simp only [htl, bind, Option.bind, Option.some.injEq] at h
        subst_vars
        simp only [WellScopedSpine, Bool.and_eq_true] at hnl
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha'
        · exact hnl.1
        · exact WellScoped_of_mem_spine htl hnl.2 a ha'
      | none => simp [htl, bind, Option.bind] at h

/-! ### Lambda-application (translated `let`) shape lemmas

  The four induction lemmas below all reach the cons-headed case; `WellScoped`
  admits exactly one shape there (a well-formed LAMBDA whose body is closed
  under its formals), so the case analysis is factored out once. -/

/-- `WellScoped` admits a cons head only in the translated-lambda shape. -/
theorem WellScoped_cons_cons : ∀ {a b argsExpr : SExpr},
    WellScoped (.cons (.cons a b) argsExpr) = true →
    ∃ (lam : Symbol) (formalsE lamBody : SExpr),
      a = .atom (.symbol lam) ∧ b = .cons formalsE (.cons lamBody .nil)
  | .nil, _, _, h => absurd h (by simp [WellScoped])
  | .atom (.number _), _, _, h => absurd h (by simp [WellScoped])
  | .atom (.string _), _, _, h => absurd h (by simp [WellScoped])
  | .atom (.keyword _), _, _, h => absurd h (by simp [WellScoped])
  | .atom (.char _), _, _, h => absurd h (by simp [WellScoped])
  | .cons _ _, _, _, h => absurd h (by simp [WellScoped])
  | .atom (.symbol _), .nil, _, h => absurd h (by simp [WellScoped])
  | .atom (.symbol _), .atom _, _, h => absurd h (by simp [WellScoped])
  | .atom (.symbol _), .cons _ .nil, _, h => absurd h (by simp [WellScoped])
  | .atom (.symbol _), .cons _ (.atom _), _, h => absurd h (by simp [WellScoped])
  | .atom (.symbol _), .cons _ (.cons _ (.atom _)), _, h => absurd h (by simp [WellScoped])
  | .atom (.symbol _), .cons _ (.cons _ (.cons _ _)), _, h => absurd h (by simp [WellScoped])
  | .atom (.symbol _), .cons _ (.cons _ .nil), _, _ => ⟨_, _, _, rfl, rfl⟩

/-- The four facts `WellScoped` certifies about a translated-lambda application:
    the head really is `LAMBDA`, its formals are well-formed, the body reads
    only those formals and is itself regular, and the actuals are regular. -/
theorem WellScoped_lam_parts {lam : Symbol} {formalsE lamBody argsExpr : SExpr}
    (h : WellScoped (.cons (.cons (.atom (.symbol lam))
          (.cons formalsE (.cons lamBody .nil))) argsExpr) = true) :
    lam.isNamed "LAMBDA" = true ∧
    (∃ formals, lamFormals? formalsE = some formals ∧ ∀ s ∈ freeVars lamBody, s ∈ formals) ∧
    WellScoped lamBody = true ∧ WellScopedSpine argsExpr = true := by
  rw [WellScoped] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, ?_, h3, h4⟩
  cases hf : lamFormals? formalsE with
  | none => rw [hf] at h2; exact absurd h2 (by simp)
  | some formals =>
    rw [hf] at h2
    exact ⟨formals, rfl, fun s hs => by
      have := (List.all_eq_true.mp h2) s hs
      simpa using this⟩

/-- Split a symbol-headed `WellScoped` fact (non-QUOTE head): the head is none of
    the rejected binder names, and the argument spine is regular. -/
theorem WellScoped_sym_parts {q : Symbol} {rest : SExpr}
    (h : WellScoped (.cons (.atom (.symbol q)) rest) = true)
    (hq : q.isNamed "QUOTE" = false) :
    (q.isNamed "LET" || q.isNamed "LET*") = false ∧ q.isNamed "LAMBDA" = false ∧
    WellScopedSpine rest = true := by
  rw [WellScoped] at h
  by_cases hb : (q.isNamed "LET" || q.isNamed "LET*" || q.isNamed "LAMBDA") = true
  · rw [if_pos hb] at h; exact absurd h (by simp)
  · have hb' : (q.isNamed "LET" = false ∧ q.isNamed "LET*" = false) ∧
        q.isNamed "LAMBDA" = false := by
      simpa [Bool.or_eq_true, not_or] using hb
    rw [if_neg hb, if_neg (by simp [hq])] at h
    exact ⟨by simp [hb'.1.1, hb'.1.2], hb'.2, h⟩

/-- `freeVars` of a CLOSED lambda application (the shape `WellScoped` certifies):
    the body's residual free variables filter to nothing, leaving the ACTUALS. -/
theorem freeVars_lam_closed {lam : Symbol} {formalsE lamBody argsExpr : SExpr}
    {formals : List Symbol}
    (hform : lamFormals? formalsE = some formals)
    (hclosed : ∀ s ∈ freeVars lamBody, s ∈ formals) :
    freeVars (.cons (.cons (.atom (.symbol lam))
      (.cons formalsE (.cons lamBody .nil))) argsExpr) = freeVarsSpine argsExpr := by
  show (match lamFormals? formalsE with
        | some fs => (freeVars lamBody).filter (fun s => !fs.contains s)
        | none => freeVars lamBody) ++ freeVarsSpine argsExpr = freeVarsSpine argsExpr
  rw [hform]
  have hnil : (freeVars lamBody).filter (fun s => !formals.contains s) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s hs
    simpa using hclosed s hs
  simp only [hnil, List.nil_append]

/-- Two envs that agree at `s` evaluate the variable `s` identically. -/
theorem evalOpt_symbol_of_get (f : Nat) (w : World) (e1 e2 : Env) (s : Symbol)
    (h : e1.get? s = e2.get? s) :
    evalOpt (f + 1) w e1 (.atom (.symbol s)) = evalOpt (f + 1) w e2 (.atom (.symbol s)) := by
  simp only [evalOpt, evalOptStep, h]

/-- Two envs extended by the SAME formals↦values agree at every formal,
    whatever their bases — the scoping fact that makes a closed lambda body
    base-env-independent. -/
theorem bindArgsOver_get_of_mem (s : Symbol) :
    ∀ (formals : List Symbol) (vals : List SExpr), formals.length = vals.length →
      s ∈ formals → ∀ (e1 e2 : Env),
        (bindArgsOver e1 formals vals).get? s = (bindArgsOver e2 formals vals).get? s
  | [], _, _, hs, _, _ => absurd hs (by simp)
  | _ :: _, [], hlen, _, _, _ => by simp at hlen
  | f :: fs, v :: vs, hlen, hs, e1, e2 => by
      show ((bindArgsOver e1 fs vs).insert f v).get? s
         = ((bindArgsOver e2 fs vs).insert f v).get? s
      rw [Env.get?_insert, Env.get?_insert]
      by_cases h : s = f
      · simp [h]
      · have hne : (s == f) = false := by simpa using h
        simp only [hne, Bool.false_eq_true, if_false]
        exact bindArgsOver_get_of_mem s fs vs (by simpa using hlen)
          (by rcases List.mem_cons.mp hs with rfl | h' <;> [exact absurd rfl h; exact h']) e1 e2

/-- FREE-VARIABLE CONGRUENCE: `evalOpt` reads the env only at a term's free
    variables, so two envs agreeing there evaluate the (LET-free) term equally. -/
theorem evalOpt_freevar_congr (w : World) :
    ∀ (n : Nat) (e1 e2 : Env) (term : SExpr), WellScoped term = true →
      (∀ s ∈ freeVars term,
        evalOpt 1 w e1 (.atom (.symbol s)) = evalOpt 1 w e2 (.atom (.symbol s))) →
      evalOpt n w e1 term = evalOpt n w e2 term := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _; rfl
  | succ n ih =>
    intro e1 e2 term hnl hfv
    match term with
    | .nil => rfl
    | .atom (.number _) => rfl
    | .atom (.string _) => rfl
    | .atom (.keyword _) => rfl
    | .atom (.char _) => rfl
    | .atom (.symbol s) => exact hfv s (by simp [freeVars])
    | .cons (.atom (.number _)) _ => rfl
    | .cons (.atom (.string _)) _ => rfl
    | .cons (.atom (.keyword _)) _ => rfl
    | .cons (.atom (.char _)) _ => rfl
    | .cons .nil _ => rfl
    | .cons (.cons _ _) argsExpr =>
      -- the translated `let`: the ACTUALS are read from the ambient envs (IH),
      -- the body only from the formals both extensions bind identically
      obtain ⟨lam, formalsE, lamBody, rfl, rfl⟩ := WellScoped_cons_cons hnl
      obtain ⟨hlam, ⟨lformals, hform, hclosed⟩, hbnl, hspine⟩ := WellScoped_lam_parts hnl
      show evalOptStep (evalOpt n) w e1 _ = evalOptStep (evalOpt n) w e2 _
      simp only [evalOptStep_cons_lam, hlam, if_true, hform]
      cases hae : argsExpr.toList? with
      | none => rfl
      | some args =>
        dsimp only
        have hkey : ∀ a ∈ args, evalOpt n w e1 a = evalOpt n w e2 a := fun a ha =>
          ih e1 e2 a (WellScoped_of_mem_spine hae hspine a ha)
            (fun s' hs' => hfv s' (by
              rw [freeVars_lam_closed hform hclosed]
              exact freeVars_subset_spine hae ha hs'))
        rw [mapM_congr_mem hkey]
        cases hav : args.mapM (fun a => evalOpt n w e2 a) with
        | none => rfl
        | some argVals =>
          show (if lformals.length = argVals.length
                  then evalOpt n w (bindArgsOver e1 lformals argVals) lamBody else none)
             = (if lformals.length = argVals.length
                  then evalOpt n w (bindArgsOver e2 lformals argVals) lamBody else none)
          by_cases hlen : lformals.length = argVals.length
          · simp only [hlen, if_true]
            exact ih _ _ lamBody hbnl (fun s hs =>
              evalOpt_symbol_of_get 0 w _ _ s
                (bindArgsOver_get_of_mem s lformals argVals hlen (hclosed s hs) _ _))
          · simp only [if_neg hlen]
    | .cons (.atom (.symbol s)) argsExpr =>
      show evalOptStep (evalOpt n) w e1 (.cons (.atom (.symbol s)) argsExpr)
         = evalOptStep (evalOpt n) w e2 (.cons (.atom (.symbol s)) argsExpr)
      simp only [evalOptStep_cons_symbol]
      cases hq : s.isNamed "QUOTE" with
      | true => simp only [↓reduceIte]
      | false =>
        have hkey : ∀ args, argsExpr.toList? = some args →
            ∀ a ∈ args, evalOpt n w e1 a = evalOpt n w e2 a := by
          intro args htl a ha
          have hnls : WellScopedSpine argsExpr = true := (WellScoped_sym_parts hnl hq).2.2
          exact ih e1 e2 a (WellScoped_of_mem_spine htl hnls a ha)
            (fun s' hs' => hfv s' (by simp only [freeVars, hq]; exact freeVars_subset_spine htl ha hs'))
        cases hif : s.isNamed "IF" with
        | true =>
          simp only [↓reduceIte]
          match htl : argsExpr.toList? with
          | some [c, t, e] =>
            show (evalOpt n w e1 c).bind
                   (fun cv => if Logic.toBool cv = true then evalOpt n w e1 t else evalOpt n w e1 e)
               = (evalOpt n w e2 c).bind
                   (fun cv => if Logic.toBool cv = true then evalOpt n w e2 t else evalOpt n w e2 e)
            rw [hkey _ htl c (by simp)]
            cases hc : evalOpt n w e2 c with
            | none => rfl
            | some cv =>
              show (if Logic.toBool cv = true then evalOpt n w e1 t else evalOpt n w e1 e)
                 = (if Logic.toBool cv = true then evalOpt n w e2 t else evalOpt n w e2 e)
              by_cases hb : Logic.toBool cv = true
              · rw [if_pos hb, if_pos hb]; exact hkey _ htl t (by simp)
              · rw [if_neg hb, if_neg hb]; exact hkey _ htl e (by simp)
          | none => rfl
          | some [] => rfl
          | some [_] => rfl
          | some [_, _] => rfl
          | some (_ :: _ :: _ :: _ :: _) => rfl
        | false =>
          cases hlet : (s.isNamed "LET" || s.isNamed "LET*") with
          | true => exact absurd (WellScoped_sym_parts hnl hq).1 (by simp [hlet])
          | false =>
            simp only [Bool.false_eq_true, if_false]
            match htl : argsExpr.toList? with
            | some args =>
              show (args.mapM (fun a => evalOpt n w e1 a)).bind
                     (fun argVals => match w.defs.get? s with
                       | some (formals, body) =>
                         if formals.length = argVals.length then
                           evalOpt n w (bindArgs formals argVals) body else none
                       | none => callBuiltin s.name argVals)
                 = (args.mapM (fun a => evalOpt n w e2 a)).bind
                     (fun argVals => match w.defs.get? s with
                       | some (formals, body) =>
                         if formals.length = argVals.length then
                           evalOpt n w (bindArgs formals argVals) body else none
                       | none => callBuiltin s.name argVals)
              rw [mapM_congr_mem (hkey args htl)]
            | none => rfl

/-! ## Convergence combinators (build "term converges to value v" facts)

  In the value-evaluation model, a rewrite node's fact `evalOpt … A = evalOpt … B`
  is discharged by showing A and B converge to equal values. These combinators
  build the convergence facts compositionally from the atomic step lemmas. -/

/-- Two terms that converge to equal values are fuel-eventually equal. -/
theorem fuel_eq_of_conv {a b : Nat → Option SExpr} {u v : SExpr}
    (ha : ∃ N, ∀ f ≥ N, a f = some u) (hb : ∃ N, ∀ f ≥ N, b f = some v)
    (huv : u = v) : ∃ N, ∀ f ≥ N, a f = b f := by
  obtain ⟨na, ha⟩ := ha; obtain ⟨nb, hb⟩ := hb
  exact ⟨max na nb, fun f hf => by rw [ha f (by omega), hb f (by omega), huv]⟩

/-- A 1-arg builtin application converges to `callBuiltin`'s result on the
    converged argument. -/
theorem conv_builtin1 (w : World) (env : Env) (s : Symbol) (a : SExpr) (av rv : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_not_def : w.defs.get? s = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some av)
    (hr : callBuiltin s.name [av] = some rv) :
    ∃ N, ∀ f ≥ N, evalOpt f w env (.cons (.atom (.symbol s)) (.cons a .nil)) = some rv := by
  obtain ⟨na, ha⟩ := ha
  refine ⟨na + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [evalOpt_builtin_1 g w env s a av h_ns h_not_def (ha g (by omega)), hr]

/-- A 2-arg builtin application converges to `callBuiltin`'s result on the
    converged arguments. -/
theorem conv_builtin2 (w : World) (env : Env) (s : Symbol) (a b : SExpr) (av bv rv : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_not_def : w.defs.get? s = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some bv)
    (hr : callBuiltin s.name [av, bv] = some rv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol s)) (.cons a (.cons b .nil))) = some rv := by
  obtain ⟨na, ha⟩ := ha; obtain ⟨nb, hb⟩ := hb
  refine ⟨max na nb + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [evalOpt_builtin_2 g w env s a b av bv h_ns h_not_def (ha g (by omega)) (hb g (by omega)), hr]

/-- IF with a converging truthy test converges to the then-branch's value. -/
theorem conv_if_true (w : World) (env : Env) (c t el cv v : SExpr)
    (htest : ∃ N, ∀ f ≥ N, evalOpt f w env c = some cv) (hcv : Logic.toBool cv = true)
    (hthen : ∃ N, ∀ f ≥ N, evalOpt f w env t = some v) :
    ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons el .nil)))) = some v := by
  obtain ⟨Nc, hc⟩ := htest; obtain ⟨Nt, ht⟩ := hthen
  refine ⟨max Nc Nt + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [evalOpt_if_true g w env c t el cv (hc g (by omega)) hcv]
  exact ht g (by omega)

/-- A 1-arg user-defined call converges to the body's value (in `bindArgs`). -/
theorem conv_defn_1 (w : World) (env : Env) (s : Symbol) (arg av : SExpr)
    (formal : Symbol) (body v : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal], body))
    (harg : ∃ N, ∀ f ≥ N, evalOpt f w env arg = some av)
    (hbody : ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [formal] [av]) body = some v) :
    ∃ N, ∀ f ≥ N, evalOpt f w env (.cons (.atom (.symbol s)) (.cons arg .nil)) = some v := by
  obtain ⟨Na, ha⟩ := harg; obtain ⟨Nb, hb⟩ := hbody
  refine ⟨max Na Nb + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [evalOpt_defn_1 g w env s arg av formal body h_ns h_def (ha g (by omega))]
  exact hb g (by omega)

/-- A 2-arg user-defined call converges to the body's value (in `bindArgs`). -/
theorem conv_defn_2 (w : World) (env : Env) (s : Symbol)
    (arg1 arg2 av1 av2 : SExpr) (formal1 formal2 : Symbol) (body v : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2], body))
    (h1 : ∃ N, ∀ f ≥ N, evalOpt f w env arg1 = some av1)
    (h2 : ∃ N, ∀ f ≥ N, evalOpt f w env arg2 = some av2)
    (hbody : ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [formal1, formal2] [av1, av2]) body = some v) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol s)) (.cons arg1 (.cons arg2 .nil))) = some v := by
  obtain ⟨N1, hN1⟩ := h1; obtain ⟨N2, hN2⟩ := h2; obtain ⟨Nb, hb⟩ := hbody
  refine ⟨max (max N1 N2) Nb + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [evalOpt_defn_2 g w env s arg1 arg2 av1 av2 formal1 formal2 body h_ns h_def
        (hN1 g (by omega)) (hN2 g (by omega))]
  exact hb g (by omega)

/-- A 3-arg user-defined call converges to the body's value (in `bindArgs`). -/
theorem conv_defn_3 (w : World) (env : Env) (s : Symbol)
    (arg1 arg2 arg3 av1 av2 av3 : SExpr) (formal1 formal2 formal3 : Symbol) (body v : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2, formal3], body))
    (h1 : ∃ N, ∀ f ≥ N, evalOpt f w env arg1 = some av1)
    (h2 : ∃ N, ∀ f ≥ N, evalOpt f w env arg2 = some av2)
    (h3 : ∃ N, ∀ f ≥ N, evalOpt f w env arg3 = some av3)
    (hbody : ∃ N, ∀ f ≥ N,
      evalOpt f w (bindArgs [formal1, formal2, formal3] [av1, av2, av3]) body = some v) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol s)) (.cons arg1 (.cons arg2 (.cons arg3 .nil)))) = some v := by
  obtain ⟨N1, hN1⟩ := h1; obtain ⟨N2, hN2⟩ := h2; obtain ⟨N3, hN3⟩ := h3
  obtain ⟨Nb, hb⟩ := hbody
  refine ⟨max (max (max N1 N2) N3) Nb + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [evalOpt_defn_3 g w env s arg1 arg2 arg3 av1 av2 av3 formal1 formal2 formal3 body
        h_ns h_def (hN1 g (by omega)) (hN2 g (by omega)) (hN3 g (by omega))]
  exact hb g (by omega)

/-! ## Term substitution (definition-unfold / IH replay)

  Ported sorry-free from the prior hand-proof branch; dispatch-agnostic (they
  factor through mapM/argument congruence), so unchanged by callBuiltin->Option.
  substTerm is first-order formal->arg-term substitution (intrinsic :DEFINITION
  replay); evalOpt_substTerm_eq / evalOpt_substTerm_quote / evalOpt_bindArgsOver_bindArgs
  are the substitution lemma the driver needs for definition unfolds and the IH. -/

/-- Positional lookup of a symbol in parallel formals/args lists; first match. -/
def lookupSubst (s : Symbol) : List Symbol → List SExpr → Option SExpr
  | f :: fs, a :: as => if s == f then some a else lookupSubst s fs as
  | _, _ => none

/-- Wrap a value as a self-evaluating `(quote v)` term. -/
def quoteVal (v : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" })) (.cons v .nil)

mutual
/-- Substitute each formal by its corresponding arg term throughout `term`.
    Quote-opaque; rewrites bare variable positions and function-call spines. -/
def substTerm (formals : List Symbol) (args : List SExpr) : SExpr → SExpr
  | .atom (.symbol s) => (lookupSubst s formals args).getD (.atom (.symbol s))
  | .cons (.atom (.symbol q)) rest =>
      if q.isNamed "QUOTE" then .cons (.atom (.symbol q)) rest
      else .cons (.atom (.symbol q)) (substSpine formals args rest)
  -- LAMBDA application (S2 2026-07-24): substitute the ACTUALS only. The
  -- binder is left alone — under `WellScoped` the body's free variables are all
  -- formals, so no outer variable occurs there to substitute (and rewriting
  -- one would capture).
  | .cons (.cons a b) argsExpr => .cons (.cons a b) (substSpine formals args argsExpr)
  | t => t
/-- Map `substTerm` across an argument spine. -/
def substSpine (formals : List Symbol) (args : List SExpr) : SExpr → SExpr
  | .cons a rest => .cons (substTerm formals args a) (substSpine formals args rest)
  | t => t
end


/-- Looking up a quote-mapped arg list = quoting the plain lookup. -/
theorem lookupSubst_map_quoteVal (s : Symbol) :
    ∀ (formals : List Symbol) (vals : List SExpr),
      lookupSubst s formals (vals.map quoteVal)
        = (lookupSubst s formals vals).map quoteVal
  | [], _ => rfl
  | _ :: _, [] => rfl
  | f :: fs, v :: vs => by
      simp only [List.map_cons, lookupSubst]
      cases h : s == f with
      | true => simp
      | false => simp [lookupSubst_map_quoteVal s fs vs]

/-- `bindArgs` is `bindArgsOver` over the empty environment. -/
theorem bindArgs_eq_bindArgsOver_empty :
    ∀ (formals : List Symbol) (vals : List SExpr),
      bindArgs formals vals = bindArgsOver (∅ : Env) formals vals
  | [], _ => rfl
  | _ :: _, [] => rfl
  | f :: fs, v :: vs => by
      show (bindArgs fs vs).insert f v = (bindArgsOver (∅ : Env) fs vs).insert f v
      rw [bindArgs_eq_bindArgsOver_empty fs vs]

/-- Looking up a symbol in `bindArgsOver` = the substitution lookup, falling back to
    the base env. -/
theorem bindArgsOver_get (env : Env) (s : Symbol) :
    ∀ (formals : List Symbol) (vals : List SExpr),
      (bindArgsOver env formals vals).get? s
        = match lookupSubst s formals vals with
          | some v => some v
          | none => env.get? s
  | [], _ => rfl
  | _ :: _, [] => rfl
  | f :: fs, v :: vs => by
      show ((bindArgsOver env fs vs).insert f v).get? s = _
      rw [Env.get?_insert, bindArgsOver_get env s fs vs]
      simp only [lookupSubst]
      by_cases h : s = f
      · subst h; simp
      · have h1 : (s == f) = false := by simp [h]
        simp only [h1, Bool.false_eq_true, if_false]

/-- `substSpine` commutes with `toList?` (mapping `substTerm` over the list). -/
theorem substSpine_toList (formals : List Symbol) (args : List SExpr) :
    ∀ (spine : SExpr),
      (substSpine formals args spine).toList?
        = (spine.toList?).map (List.map (substTerm formals args))
  | .nil => rfl
  | .atom _ => rfl
  | .cons hd tl => by
      simp only [substSpine, SExpr.toList?, substSpine_toList formals args tl]
      cases htl : tl.toList? with
      | none => rfl
      | some rest => rfl

/-- SUBSTITUTION (quoted values): substituting each formal by `(quote vᵢ)` in a
    LET-free body, evaluated in `env`, equals evaluating the body in the env
    extended with the formals bound to the `vᵢ`. Fixed fuel — no convergence
    needed, since quoted values evaluate immediately. The bridge from this to
    `bindArgs` is `evalOpt_freevar_congr` (when the body is closed under the
    formals). -/
theorem evalOpt_substTerm_quote (w : World) (formals : List Symbol) (vals : List SExpr) :
    ∀ (m : Nat) (env : Env) (body : SExpr), WellScoped body = true →
      evalOpt m w env (substTerm formals (vals.map quoteVal) body)
        = evalOpt m w (bindArgsOver env formals vals) body := by
  intro m
  induction m with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro env body hnl
    match body with
    | .nil => rfl
    | .atom (.number _) => rfl
    | .atom (.string _) => rfl
    | .atom (.keyword _) => rfl
    | .atom (.char _) => rfl
    | .atom (.symbol s) =>
      show evalOpt (n + 1) w env
            ((lookupSubst s formals (vals.map quoteVal)).getD (.atom (.symbol s)))
         = evalOpt (n + 1) w (bindArgsOver env formals vals) (.atom (.symbol s))
      rw [lookupSubst_map_quoteVal]
      cases hl : lookupSubst s formals vals with
      | some vi =>
        simp only [Option.map_some, Option.getD_some, quoteVal]
        rw [evalOpt_quote n w env vi]
        have hg : (bindArgsOver env formals vals).get? s = some vi := by
          have he := bindArgsOver_get env s formals vals; rw [hl] at he; exact he
        rw [evalOpt_var n w (bindArgsOver env formals vals) s vi hg]
      | none =>
        simp only [Option.map_none, Option.getD_none]
        have hg : env.get? s = (bindArgsOver env formals vals).get? s := by
          have he := bindArgsOver_get env s formals vals; rw [hl] at he; exact he.symm
        exact evalOpt_symbol_of_get n w env (bindArgsOver env formals vals) s hg
    | .cons (.atom (.number _)) _ => rfl
    | .cons (.atom (.string _)) _ => rfl
    | .cons (.atom (.keyword _)) _ => rfl
    | .cons (.atom (.char _)) _ => rfl
    | .cons .nil _ => rfl
    | .cons (.cons _ _) argsExpr =>
      -- the translated `let`: substitution rewrites the ACTUALS (IH), and the
      -- body — closed under the lambda's own formals — is insensitive to the
      -- base env the two sides differ in (free-variable congruence)
      obtain ⟨lam, formalsE, lamBody, rfl, rfl⟩ := WellScoped_cons_cons hnl
      obtain ⟨hlam, ⟨lformals, hform, hclosed⟩, hbnl, hspine⟩ := WellScoped_lam_parts hnl
      show evalOptStep (evalOpt n) w env
             (.cons (.cons (.atom (.symbol lam)) (.cons formalsE (.cons lamBody .nil)))
               (substSpine formals (vals.map quoteVal) argsExpr))
         = evalOptStep (evalOpt n) w (bindArgsOver env formals vals) _
      simp only [evalOptStep_cons_lam, hlam, if_true, hform, substSpine_toList]
      cases hae : argsExpr.toList? with
      | none => simp only [Option.map_none]
      | some args =>
        simp only [Option.map_some]
        have hkey : ∀ a ∈ args,
            evalOpt n w env (substTerm formals (vals.map quoteVal) a)
              = evalOpt n w (bindArgsOver env formals vals) a := fun a ha =>
          ih env a (WellScoped_of_mem_spine hae hspine a ha)
        rw [List.mapM_map]
        simp only [Function.comp_def]
        rw [mapM_congr_mem hkey]
        cases hav : args.mapM (fun a => evalOpt n w (bindArgsOver env formals vals) a) with
        | none => rfl
        | some argVals =>
          show (if lformals.length = argVals.length
                  then evalOpt n w (bindArgsOver env lformals argVals) lamBody else none)
             = (if lformals.length = argVals.length
                  then evalOpt n w (bindArgsOver (bindArgsOver env formals vals) lformals argVals)
                         lamBody else none)
          by_cases hlen : lformals.length = argVals.length
          · simp only [hlen, if_true]
            exact evalOpt_freevar_congr w n _ _ lamBody hbnl (fun s hs =>
              evalOpt_symbol_of_get 0 w _ _ s
                (bindArgsOver_get_of_mem s lformals argVals hlen (hclosed s hs) _ _))
          · simp only [if_neg hlen]
    | .cons (.atom (.symbol q)) rest =>
      by_cases hq : q.isNamed "QUOTE" = true
      · rw [show substTerm formals (vals.map quoteVal) (.cons (.atom (.symbol q)) rest)
              = .cons (.atom (.symbol q)) rest from by simp only [substTerm, hq, if_true]]
        show evalOptStep (evalOpt n) w env (.cons (.atom (.symbol q)) rest)
           = evalOptStep (evalOpt n) w (bindArgsOver env formals vals) (.cons (.atom (.symbol q)) rest)
        simp only [evalOptStep_cons_symbol, hq, ↓reduceIte]
      · have hqf : q.isNamed "QUOTE" = false := by
          simp only [Bool.not_eq_true] at hq; exact hq
        rw [show substTerm formals (vals.map quoteVal) (.cons (.atom (.symbol q)) rest)
              = .cons (.atom (.symbol q)) (substSpine formals (vals.map quoteVal) rest)
            from by simp only [substTerm, hqf, Bool.false_eq_true, if_false]]
        show evalOptStep (evalOpt n) w env
              (.cons (.atom (.symbol q)) (substSpine formals (vals.map quoteVal) rest))
           = evalOptStep (evalOpt n) w (bindArgsOver env formals vals)
              (.cons (.atom (.symbol q)) rest)
        simp only [evalOptStep_cons_symbol, hqf, Bool.false_eq_true, if_false]
        -- Per-element bridge: substituted arg in `env` = original arg in `bindArgsOver`.
        have hnls : WellScopedSpine rest = true := (WellScoped_sym_parts hnl hqf).2.2
        have ihkey : ∀ a ∈ (rest.toList?).getD [],
            evalOpt n w env (substTerm formals (vals.map quoteVal) a)
              = evalOpt n w (bindArgsOver env formals vals) a := by
          intro a ha
          cases htl : rest.toList? with
          | none => simp [htl] at ha
          | some l =>
            simp only [htl, Option.getD_some] at ha
            exact ih env a (WellScoped_of_mem_spine htl hnls a ha)
        rw [substSpine_toList]
        by_cases hif : q.isNamed "IF" = true
        · simp only [hif, ↓reduceIte]
          match htl : rest.toList? with
          | some [c, t, e] =>
            show (evalOpt n w env (substTerm formals (vals.map quoteVal) c)).bind
                   (fun cv => if Logic.toBool cv = true
                     then evalOpt n w env (substTerm formals (vals.map quoteVal) t)
                     else evalOpt n w env (substTerm formals (vals.map quoteVal) e))
               = (evalOpt n w (bindArgsOver env formals vals) c).bind
                   (fun cv => if Logic.toBool cv = true
                     then evalOpt n w (bindArgsOver env formals vals) t
                     else evalOpt n w (bindArgsOver env formals vals) e)
            simp only [ihkey c (by simp [htl]), ihkey t (by simp [htl]), ihkey e (by simp [htl])]
          | none => rfl
          | some [] => rfl
          | some [_] => rfl
          | some [_, _] => rfl
          | some (_ :: _ :: _ :: _ :: _) => rfl
        · have hiff : q.isNamed "IF" = false := by
            simp only [Bool.not_eq_true] at hif; exact hif
          by_cases hlet : (q.isNamed "LET" || q.isNamed "LET*") = true
          · exact absurd (WellScoped_sym_parts hnl hqf).1 (by simp [hlet])
          · have hletf : (q.isNamed "LET" || q.isNamed "LET*") = false := by
              simp only [Bool.not_eq_true] at hlet; exact hlet
            simp only [hiff, hletf, Bool.false_eq_true, if_false]
            match htl : rest.toList? with
            | some l =>
              simp only [Option.map_some]
              rw [show List.mapM (fun a => evalOpt n w env a)
                      (List.map (substTerm formals (List.map quoteVal vals)) l)
                    = List.mapM (fun a => evalOpt n w (bindArgsOver env formals vals) a) l from by
                  rw [List.mapM_map]
                  exact mapM_congr_mem
                    (fun a ha => ihkey a (by simp only [htl, Option.getD_some]; exact ha))]
            | none => rfl

/-- SUBSTITUTION congruence: substituting two argument lists that agree at every
    fuel (per substituted variable) gives equal evaluations of a LET-free body.
    Fixed fuel. The all-fuel hypothesis holds e.g. when corresponding args are
    interchangeable terms (variables bound to the same value, or a term and the
    `(quote v)` of its value) — the regime that arises replaying a `:DEFINITION`
    unfold whose argument terms are already in the goal's context. -/
theorem evalOpt_substTerm_eq (w : World) (env : Env) (formals : List Symbol)
    (args args' : List SExpr)
    (hpw : ∀ (s : Symbol) (g : Nat),
      evalOpt g w env ((lookupSubst s formals args).getD (.atom (.symbol s)))
        = evalOpt g w env ((lookupSubst s formals args').getD (.atom (.symbol s)))) :
    ∀ (f : Nat) (body : SExpr), WellScoped body = true →
      evalOpt f w env (substTerm formals args body)
        = evalOpt f w env (substTerm formals args' body) := by
  intro f
  induction f with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro body hnl
    match body with
    | .nil => rfl
    | .atom (.number _) => rfl
    | .atom (.string _) => rfl
    | .atom (.keyword _) => rfl
    | .atom (.char _) => rfl
    | .atom (.symbol s) => exact hpw s (n + 1)
    | .cons (.atom (.number _)) _ => rfl
    | .cons (.atom (.string _)) _ => rfl
    | .cons (.atom (.keyword _)) _ => rfl
    | .cons (.atom (.char _)) _ => rfl
    | .cons .nil _ => rfl
    | .cons (.cons _ _) argsExpr =>
      -- the translated `let`: only the ACTUALS are substituted, and both
      -- sides then evaluate the SAME body in the SAME extended env
      obtain ⟨lam, formalsE, lamBody, rfl, rfl⟩ := WellScoped_cons_cons hnl
      obtain ⟨hlam, ⟨lformals, hform, _⟩, _, hspine⟩ := WellScoped_lam_parts hnl
      show evalOptStep (evalOpt n) w env
             (.cons (.cons (.atom (.symbol lam)) (.cons formalsE (.cons lamBody .nil)))
               (substSpine formals args argsExpr))
         = evalOptStep (evalOpt n) w env
             (.cons (.cons (.atom (.symbol lam)) (.cons formalsE (.cons lamBody .nil)))
               (substSpine formals args' argsExpr))
      simp only [evalOptStep_cons_lam, hlam, if_true, hform, substSpine_toList]
      cases hae : argsExpr.toList? with
      | none => simp only [Option.map_none]
      | some l =>
        simp only [Option.map_some]
        rw [List.mapM_map, List.mapM_map]
        simp only [Function.comp_def]
        rw [mapM_congr_mem (fun a ha => ih a (WellScoped_of_mem_spine hae hspine a ha))]
    | .cons (.atom (.symbol q)) rest =>
      by_cases hq : q.isNamed "QUOTE" = true
      · rw [show substTerm formals args (.cons (.atom (.symbol q)) rest)
              = .cons (.atom (.symbol q)) rest from by simp only [substTerm, hq, if_true],
            show substTerm formals args' (.cons (.atom (.symbol q)) rest)
              = .cons (.atom (.symbol q)) rest from by simp only [substTerm, hq, if_true]]
      · have hqf : q.isNamed "QUOTE" = false := by
          simp only [Bool.not_eq_true] at hq; exact hq
        rw [show substTerm formals args (.cons (.atom (.symbol q)) rest)
              = .cons (.atom (.symbol q)) (substSpine formals args rest)
            from by simp only [substTerm, hqf, Bool.false_eq_true, if_false],
            show substTerm formals args' (.cons (.atom (.symbol q)) rest)
              = .cons (.atom (.symbol q)) (substSpine formals args' rest)
            from by simp only [substTerm, hqf, Bool.false_eq_true, if_false]]
        show evalOptStep (evalOpt n) w env
              (.cons (.atom (.symbol q)) (substSpine formals args rest))
           = evalOptStep (evalOpt n) w env
              (.cons (.atom (.symbol q)) (substSpine formals args' rest))
        simp only [evalOptStep_cons_symbol, hqf, Bool.false_eq_true, if_false]
        have hnls : WellScopedSpine rest = true := (WellScoped_sym_parts hnl hqf).2.2
        have ihkey : ∀ a ∈ (rest.toList?).getD [],
            evalOpt n w env (substTerm formals args a)
              = evalOpt n w env (substTerm formals args' a) := by
          intro a ha
          cases htl : rest.toList? with
          | none => simp [htl] at ha
          | some l =>
            simp only [htl, Option.getD_some] at ha
            exact ih a (WellScoped_of_mem_spine htl hnls a ha)
        rw [substSpine_toList, substSpine_toList]
        by_cases hif : q.isNamed "IF" = true
        · simp only [hif, ↓reduceIte]
          match htl : rest.toList? with
          | some [c, t, e] =>
            show (evalOpt n w env (substTerm formals args c)).bind
                   (fun cv => if Logic.toBool cv = true
                     then evalOpt n w env (substTerm formals args t)
                     else evalOpt n w env (substTerm formals args e))
               = (evalOpt n w env (substTerm formals args' c)).bind
                   (fun cv => if Logic.toBool cv = true
                     then evalOpt n w env (substTerm formals args' t)
                     else evalOpt n w env (substTerm formals args' e))
            simp only [ihkey c (by simp [htl]), ihkey t (by simp [htl]), ihkey e (by simp [htl])]
          | none => rfl
          | some [] => rfl
          | some [_] => rfl
          | some [_, _] => rfl
          | some (_ :: _ :: _ :: _ :: _) => rfl
        · have hiff : q.isNamed "IF" = false := by
            simp only [Bool.not_eq_true] at hif; exact hif
          by_cases hlet : (q.isNamed "LET" || q.isNamed "LET*") = true
          · exact absurd (WellScoped_sym_parts hnl hqf).1 (by simp [hlet])
          · have hletf : (q.isNamed "LET" || q.isNamed "LET*") = false := by
              simp only [Bool.not_eq_true] at hlet; exact hlet
            simp only [hiff, hletf, Bool.false_eq_true, if_false]
            match htl : rest.toList? with
            | some l =>
              simp only [Option.map_some]
              rw [show List.mapM (fun a => evalOpt n w env a)
                      (List.map (substTerm formals args) l)
                    = List.mapM (fun a => evalOpt n w env a)
                      (List.map (substTerm formals args') l) from by
                  rw [List.mapM_map, List.mapM_map]
                  exact mapM_congr_mem
                    (fun a ha => ihkey a (by simp only [htl, Option.getD_some]; exact ha))]
            | none => rfl

/-! ### Eventual substitution congruence (for compound-argument `:DEFINITION`)

  `evalOpt_substTerm_eq` needs the substituted args to agree with `args'` at ALL
  fuel — true only for fuel-1 args (variables, `(cdr x)`). For a compound arg
  (e.g. `(cons (car x) (my-app (cdr x) y))`) agreement is only EVENTUAL, so the
  driver needs this eventual version (fuel bound = agreement-bound + body depth).
  Proved by induction on a `sizeOf` bound over the body. -/

/-- Finite-`max` of per-element fuel bounds. -/
theorem exists_bound_forall_mem {α : Type} (l : List α)
    (P : α → Nat → Prop) (h : ∀ a ∈ l, ∃ N, ∀ f ≥ N, P a f) :
    ∃ N, ∀ f ≥ N, ∀ a ∈ l, P a f := by
  induction l with
  | nil => exact ⟨0, fun f _ a ha => by simp at ha⟩
  | cons x xs ih =>
    obtain ⟨Nx, hx⟩ := h x (List.mem_cons_self ..)
    obtain ⟨Nxs, hxs⟩ := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    refine ⟨max Nx Nxs, fun f hf a ha => ?_⟩
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact hx f (by omega)
    · exact hxs f (by omega) a ha'

/-- A `toList?` element is structurally smaller than the spine. -/
theorem sizeOf_mem_toList : ∀ {rest a : SExpr},
    a ∈ (rest.toList?).getD [] → sizeOf a < sizeOf rest
  | .nil, a, ha => by simp [SExpr.toList?] at ha
  | .atom _, a, ha => by simp [SExpr.toList?] at ha
  | .cons hd tl, a, ha => by
    simp only [SExpr.toList?] at ha
    match htl : tl.toList? with
    | none => simp [htl] at ha
    | some l =>
      simp only [htl] at ha
      rcases List.mem_cons.mp ha with rfl | ha'
      · have : 0 < sizeOf tl := by cases tl <;> simp_all
        simp only [SExpr.cons.sizeOf_spec]; omega
      · have hsub : a ∈ (tl.toList?).getD [] := by rw [htl]; exact ha'
        have := sizeOf_mem_toList hsub
        simp only [SExpr.cons.sizeOf_spec]; omega

/-- EVENTUAL substitution congruence: if the substituted args agree with `args'`
    EVENTUALLY (per substituted variable, for fuel ≥ Nag), then for a LET-free
    body the two substituted bodies evaluate equally for fuel ≥ Nag + body-depth.
    (The all-fuel `evalOpt_substTerm_eq` is the `Nag = 0` special case.) -/
theorem evalOpt_substTerm_conv (w : World) (env : Env) (formals : List Symbol)
    (args args' : List SExpr) (Nag : Nat)
    (hag : ∀ (s : Symbol) (g : Nat), g ≥ Nag →
      evalOpt g w env ((lookupSubst s formals args).getD (.atom (.symbol s)))
        = evalOpt g w env ((lookupSubst s formals args').getD (.atom (.symbol s)))) :
    ∀ (n : Nat) (body : SExpr), sizeOf body ≤ n → WellScoped body = true →
      ∃ N, ∀ f ≥ N, evalOpt f w env (substTerm formals args body)
        = evalOpt f w env (substTerm formals args' body) := by
  intro n
  induction n with
  | zero => intro body hb _; exact absurd hb (by cases body <;> simp)
  | succ n ih =>
    intro body hb hnl
    match body with
    | .nil => exact ⟨0, fun f _ => rfl⟩
    | .atom (.number _) => exact ⟨0, fun f _ => rfl⟩
    | .atom (.string _) => exact ⟨0, fun f _ => rfl⟩
    | .atom (.keyword _) => exact ⟨0, fun f _ => rfl⟩
    | .atom (.char _) => exact ⟨0, fun f _ => rfl⟩
    | .atom (.symbol s) => exact ⟨Nag, fun f hf => hag s f hf⟩
    | .cons (.atom (.number _)) _ => exact ⟨0, fun f _ => rfl⟩
    | .cons (.atom (.string _)) _ => exact ⟨0, fun f _ => rfl⟩
    | .cons (.atom (.keyword _)) _ => exact ⟨0, fun f _ => rfl⟩
    | .cons (.atom (.char _)) _ => exact ⟨0, fun f _ => rfl⟩
    | .cons .nil _ => exact ⟨0, fun f _ => rfl⟩
    | .cons (.cons _ _) argsExpr =>
      -- the translated `let`: the ACTUALS agree eventually (each is
      -- structurally smaller); the body and its extended env are then
      -- syntactically identical on both sides
      obtain ⟨lam, formalsE, lamBody, rfl, rfl⟩ := WellScoped_cons_cons hnl
      obtain ⟨hlam, ⟨lformals, hform, _⟩, _, hspine⟩ := WellScoped_lam_parts hnl
      obtain ⟨Ns, hs⟩ : ∃ Ns, ∀ f ≥ Ns, ∀ a ∈ (argsExpr.toList?).getD [],
          evalOpt f w env (substTerm formals args a)
            = evalOpt f w env (substTerm formals args' a) := by
        apply exists_bound_forall_mem
        intro a ha
        have hsz : sizeOf a ≤ n := by
          have h1 := sizeOf_mem_toList ha
          simp only [SExpr.cons.sizeOf_spec] at hb; omega
        have hnl_a : WellScoped a = true := by
          match htl : argsExpr.toList? with
          | some l => exact WellScoped_of_mem_spine htl hspine a (by rw [htl] at ha; simpa using ha)
          | none => rw [htl] at ha; simp at ha
        exact ih a hsz hnl_a
      refine ⟨Ns + 1, fun f hf => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
      have ihkey := hs m (by omega)
      show evalOptStep (evalOpt m) w env
             (.cons (.cons (.atom (.symbol lam)) (.cons formalsE (.cons lamBody .nil)))
               (substSpine formals args argsExpr))
         = evalOptStep (evalOpt m) w env
             (.cons (.cons (.atom (.symbol lam)) (.cons formalsE (.cons lamBody .nil)))
               (substSpine formals args' argsExpr))
      simp only [evalOptStep_cons_lam, hlam, if_true, hform, substSpine_toList]
      cases hae : argsExpr.toList? with
      | none => simp only [Option.map_none]
      | some l =>
        simp only [Option.map_some]
        rw [List.mapM_map, List.mapM_map]
        simp only [Function.comp_def]
        rw [mapM_congr_mem (fun a ha => ihkey a (by simp only [hae, Option.getD_some]; exact ha))]
    | .cons (.atom (.symbol q)) rest =>
      by_cases hq : q.isNamed "QUOTE" = true
      · exact ⟨0, fun f _ => by simp only [substTerm, hq, ↓reduceIte]⟩
      · have hqf : q.isNamed "QUOTE" = false := by
          simp only [Bool.not_eq_true] at hq; exact hq
        have hnls : WellScopedSpine rest = true := (WellScoped_sym_parts hnl hqf).2.2
        -- each spine element agrees eventually (it is structurally smaller)
        obtain ⟨Ns, hs⟩ : ∃ Ns, ∀ f ≥ Ns, ∀ a ∈ (rest.toList?).getD [],
            evalOpt f w env (substTerm formals args a)
              = evalOpt f w env (substTerm formals args' a) := by
          apply exists_bound_forall_mem
          intro a ha
          have hsz : sizeOf a ≤ n := by
            have h1 := sizeOf_mem_toList ha
            simp only [SExpr.cons.sizeOf_spec] at hb; omega
          have hnl_a : WellScoped a = true := by
            match htl : rest.toList? with
            | some l => exact WellScoped_of_mem_spine htl hnls a (by rw [htl] at ha; simpa using ha)
            | none => rw [htl] at ha; simp at ha
          exact ih a hsz hnl_a
        refine ⟨Ns + 1, fun f hf => ?_⟩
        obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
        have ihkey := hs m (by omega)
        rw [show substTerm formals args (.cons (.atom (.symbol q)) rest)
              = .cons (.atom (.symbol q)) (substSpine formals args rest)
            from by simp only [substTerm, hqf, Bool.false_eq_true, if_false],
            show substTerm formals args' (.cons (.atom (.symbol q)) rest)
              = .cons (.atom (.symbol q)) (substSpine formals args' rest)
            from by simp only [substTerm, hqf, Bool.false_eq_true, if_false]]
        show evalOptStep (evalOpt m) w env
              (.cons (.atom (.symbol q)) (substSpine formals args rest))
           = evalOptStep (evalOpt m) w env
              (.cons (.atom (.symbol q)) (substSpine formals args' rest))
        simp only [evalOptStep_cons_symbol, hqf, Bool.false_eq_true, if_false]
        rw [substSpine_toList, substSpine_toList]
        by_cases hif : q.isNamed "IF" = true
        · simp only [hif, ↓reduceIte]
          match htl : rest.toList? with
          | some [c, t, e] =>
            show (evalOpt m w env (substTerm formals args c)).bind
                   (fun cv => if Logic.toBool cv = true
                     then evalOpt m w env (substTerm formals args t)
                     else evalOpt m w env (substTerm formals args e))
               = (evalOpt m w env (substTerm formals args' c)).bind
                   (fun cv => if Logic.toBool cv = true
                     then evalOpt m w env (substTerm formals args' t)
                     else evalOpt m w env (substTerm formals args' e))
            simp only [ihkey c (by simp [htl]), ihkey t (by simp [htl]), ihkey e (by simp [htl])]
          | none => rfl
          | some [] => rfl
          | some [_] => rfl
          | some [_, _] => rfl
          | some (_ :: _ :: _ :: _ :: _) => rfl
        · have hiff : q.isNamed "IF" = false := by
            simp only [Bool.not_eq_true] at hif; exact hif
          by_cases hlet : (q.isNamed "LET" || q.isNamed "LET*") = true
          · exact absurd (WellScoped_sym_parts hnl hqf).1 (by simp [hlet])
          · have hletf : (q.isNamed "LET" || q.isNamed "LET*") = false := by
              simp only [Bool.not_eq_true] at hlet; exact hlet
            simp only [hiff, hletf, Bool.false_eq_true, if_false]
            match htl : rest.toList? with
            | some l =>
              simp only [Option.map_some]
              rw [show List.mapM (fun a => evalOpt m w env a)
                      (List.map (substTerm formals args) l)
                    = List.mapM (fun a => evalOpt m w env a)
                      (List.map (substTerm formals args') l) from by
                  rw [List.mapM_map, List.mapM_map]
                  exact mapM_congr_mem
                    (fun a ha => ihkey a (by simp only [htl, Option.getD_some]; exact ha))]
            | none => rfl

/-- A formal present in `formals` (with a matching-length value list) has a
    substitution binding. -/
theorem lookupSubst_some_of_mem (s : Symbol) :
    ∀ (formals : List Symbol) (vals : List SExpr), s ∈ formals → formals.length = vals.length →
      ∃ v, lookupSubst s formals vals = some v
  | [], _, hmem, _ => by simp at hmem
  | _ :: _, [], _, hlen => by simp at hlen
  | f :: fs, v :: vs, hmem, hlen => by
      simp only [lookupSubst]
      by_cases h : s == f
      · exact ⟨v, by simp [h]⟩
      · simp only [h, Bool.false_eq_true, if_false]
        have hsf : s ∈ fs := by
          rcases List.mem_cons.mp hmem with rfl | h' <;> simp_all
        exact lookupSubst_some_of_mem s fs vs hsf (by simpa using hlen)

/-- The per-variable hypothesis `evalOpt_substTerm_eq` needs, derived from each
    arg agreeing with the quoted value of its position at every fuel. -/
theorem lookupSubst_eval_congr (w : World) (env : Env) :
    ∀ (formals : List Symbol) (args vals : List SExpr), args.length = vals.length →
      (∀ a v, (a, v) ∈ args.zip vals → ∀ g, evalOpt g w env a = evalOpt g w env (quoteVal v)) →
      ∀ (s : Symbol) (g : Nat),
        evalOpt g w env ((lookupSubst s formals args).getD (.atom (.symbol s)))
          = evalOpt g w env
              ((lookupSubst s formals (vals.map quoteVal)).getD (.atom (.symbol s)))
  | [], _, _, _, _, _, _ => by simp [lookupSubst]
  | _ :: _, [], [], _, _, _, _ => by simp [lookupSubst]
  | f :: fs, a :: as, v :: vs, hlen, hz, s, g => by
      rw [lookupSubst_map_quoteVal]
      simp only [lookupSubst]
      by_cases h : s == f
      · simp only [h, if_true, Option.map_some]
        exact hz a v (by simp [List.zip_cons_cons]) g
      · simp only [h, Bool.false_eq_true, if_false, ← lookupSubst_map_quoteVal]
        exact lookupSubst_eval_congr w env fs as vs (by simpa using hlen)
          (fun a' v' hmem => hz a' v' (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hmem))
          s g
  | _ :: _, [], _ :: _, hlen, _, _, _ => by simp at hlen
  | _ :: _, _ :: _, [], hlen, _, _, _ => by simp at hlen

/-- Evaluating a closed (under `formals`) LET-free body in `bindArgsOver env` is the
    same as in `bindArgs` — the base env is invisible past the formals. -/
theorem evalOpt_bindArgsOver_bindArgs (w : World) (env : Env) (formals : List Symbol)
    (vals : List SExpr) (hlen : formals.length = vals.length) (g : Nat) (body : SExpr)
    (hnl : WellScoped body = true) (hcl : ∀ s ∈ freeVars body, s ∈ formals) :
    evalOpt g w (bindArgsOver env formals vals) body = evalOpt g w (bindArgs formals vals) body := by
  rw [bindArgs_eq_bindArgsOver_empty]
  refine evalOpt_freevar_congr w g (bindArgsOver env formals vals) (bindArgsOver ∅ formals vals) body hnl
    (fun s hs => ?_)
  obtain ⟨v, hv⟩ := lookupSubst_some_of_mem s formals vals (hcl s hs) hlen
  have h1 := bindArgsOver_get env s formals vals
  have h2 := bindArgsOver_get (∅ : Env) s formals vals
  rw [hv] at h1 h2
  exact evalOpt_symbol_of_get 0 w _ _ s (h1.trans h2.symm)

/-- Compound-argument `:DEFINITION` unfold (1-arg): the schematic replay of a
    `definition:fn` node whose argument is an arbitrary (possibly compound) term.
    `eval(fn arg) = eval(substTerm [formal] [arg] body)` eventually — both sides
    converge to the body's value in `bindArgs`. No functionality: `arg` converges
    to SOME value `av` (totality), the body converges in `bindArgs` (totality of
    the body's calls), and the substitution lemma bridges the substituted body to
    the `bindArgs` evaluation. -/
theorem evalOpt_unfold1_conv (w : World) (env : Env) (fn formal : Symbol)
    (body arg av v : SExpr)
    (hns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
           fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (hdef : w.defs.get? fn = some ([formal], body))
    (hclosed : ∀ s ∈ freeVars body, s ∈ [formal]) (hws : WellScoped body = true)
    (harg : ∃ N, ∀ f ≥ N, evalOpt f w env arg = some av)
    (hbody : ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [formal] [av]) body = some v) :
    ∃ N, ∀ f ≥ N, evalOpt f w env (.cons (.atom (.symbol fn)) (.cons arg .nil))
      = evalOpt f w env (substTerm [formal] [arg] body) := by
  -- LHS ⇒ v  (definition unfold, call-by-value, body converges in bindArgs)
  have hlhs : ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol fn)) (.cons arg .nil)) = some v :=
    conv_defn_1 w env fn arg av formal body v hns hdef harg hbody
  -- RHS ⇒ v : substTerm [formal][arg] body ≈ substTerm [formal][quoteVal av] body
  --          = body in (bindArgsOver = bindArgs) ⇒ v
  obtain ⟨Narg, harg'⟩ := harg
  obtain ⟨Ncong, hcong⟩ := evalOpt_substTerm_conv w env [formal] (List.map quoteVal [av]) [arg]
    (max Narg 1)
    (by
      intro s g hg
      by_cases hsf : s = formal
      · subst hsf
        simp only [List.map_cons, List.map_nil, lookupSubst, beq_self_eq_true,
                   ↓reduceIte, Option.getD_some, quoteVal]
        obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
        rw [evalOpt_quote k w env av, harg' (k + 1) (by omega)]
      · simp only [List.map_cons, List.map_nil, lookupSubst,
                   show (s == formal) = false from by simpa using hsf, Bool.false_eq_true,
                   ↓reduceIte, Option.getD_none])
    (sizeOf body) body (Nat.le_refl _) hws
  have hrhs : ∃ N, ∀ f ≥ N, evalOpt f w env (substTerm [formal] [arg] body) = some v := by
    obtain ⟨Nb, hb⟩ := hbody
    refine ⟨max Ncong Nb, fun f hf => ?_⟩
    rw [← hcong f (by omega), evalOpt_substTerm_quote w [formal] [av] f env body hws,
        evalOpt_bindArgsOver_bindArgs w env [formal] [av] rfl f body hws hclosed]
    exact hb f (by omega)
  obtain ⟨Nl, hl⟩ := hlhs; obtain ⟨Nr, hr⟩ := hrhs
  exact ⟨max Nl Nr, fun f hf => by rw [hl f (by omega), hr f (by omega)]⟩

/-- Compound-argument `:DEFINITION` unfold (2-arg): the 2-formal analogue of
    `evalOpt_unfold1_conv`. `eval(fn arg1 arg2) = eval(substTerm [f1,f2] [arg1,arg2] body)`
    eventually, when both args converge. Requires the formals distinct. -/
theorem evalOpt_unfold2_conv (w : World) (env : Env) (fn formal1 formal2 : Symbol)
    (body arg1 arg2 av1 av2 v : SExpr)
    (hns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
           fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (hdef : w.defs.get? fn = some ([formal1, formal2], body))
    (hclosed : ∀ s ∈ freeVars body, s ∈ [formal1, formal2]) (hws : WellScoped body = true)
    (harg1 : ∃ N, ∀ f ≥ N, evalOpt f w env arg1 = some av1)
    (harg2 : ∃ N, ∀ f ≥ N, evalOpt f w env arg2 = some av2)
    (hbody : ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [formal1, formal2] [av1, av2]) body = some v) :
    ∃ N, ∀ f ≥ N, evalOpt f w env (.cons (.atom (.symbol fn)) (.cons arg1 (.cons arg2 .nil)))
      = evalOpt f w env (substTerm [formal1, formal2] [arg1, arg2] body) := by
  have hlhs : ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol fn)) (.cons arg1 (.cons arg2 .nil))) = some v :=
    conv_defn_2 w env fn arg1 arg2 av1 av2 formal1 formal2 body v hns hdef harg1 harg2 hbody
  obtain ⟨Narg1, harg1'⟩ := harg1
  obtain ⟨Narg2, harg2'⟩ := harg2
  obtain ⟨Ncong, hcong⟩ := evalOpt_substTerm_conv w env [formal1, formal2]
    (List.map quoteVal [av1, av2]) [arg1, arg2] (max (max Narg1 Narg2) 1)
    (by
      intro s g hg
      by_cases h1 : s = formal1
      · simp only [List.map_cons, List.map_nil, lookupSubst,
                   show (s == formal1) = true from by simp [h1],
                   ↓reduceIte, Option.getD_some, quoteVal]
        obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
        rw [evalOpt_quote k w env av1, harg1' (k + 1) (by omega)]
      · by_cases h2 : s = formal2
        · simp only [List.map_cons, List.map_nil, lookupSubst,
                     show (s == formal1) = false from by simpa using h1,
                     show (s == formal2) = true from by simp [h2],
                     Bool.false_eq_true, ↓reduceIte, Option.getD_some, quoteVal]
          obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
          rw [evalOpt_quote k w env av2, harg2' (k + 1) (by omega)]
        · simp only [List.map_cons, List.map_nil, lookupSubst,
                     show (s == formal1) = false from by simpa using h1,
                     show (s == formal2) = false from by simpa using h2,
                     Bool.false_eq_true, ↓reduceIte, Option.getD_none])
    (sizeOf body) body (Nat.le_refl _) hws
  have hrhs : ∃ N, ∀ f ≥ N,
      evalOpt f w env (substTerm [formal1, formal2] [arg1, arg2] body) = some v := by
    obtain ⟨Nb, hb⟩ := hbody
    refine ⟨max Ncong Nb, fun f hf => ?_⟩
    rw [← hcong f (by omega), evalOpt_substTerm_quote w [formal1, formal2] [av1, av2] f env body hws,
        evalOpt_bindArgsOver_bindArgs w env [formal1, formal2] [av1, av2] rfl f body hws hclosed]
    exact hb f (by omega)
  obtain ⟨Nl, hl⟩ := hlhs; obtain ⟨Nr, hr⟩ := hrhs
  exact ⟨max Nl Nr, fun f hf => by rw [hl f (by omega), hr f (by omega)]⟩

/-- Compound-argument `:DEFINITION` unfold (3-arg): the 3-formal analogue of
    `evalOpt_unfold2_conv`, when all three args converge. -/
theorem evalOpt_unfold3_conv (w : World) (env : Env) (fn formal1 formal2 formal3 : Symbol)
    (body arg1 arg2 arg3 av1 av2 av3 v : SExpr)
    (hns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
           fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (hdef : w.defs.get? fn = some ([formal1, formal2, formal3], body))
    (hclosed : ∀ s ∈ freeVars body, s ∈ [formal1, formal2, formal3])
    (hws : WellScoped body = true)
    (harg1 : ∃ N, ∀ f ≥ N, evalOpt f w env arg1 = some av1)
    (harg2 : ∃ N, ∀ f ≥ N, evalOpt f w env arg2 = some av2)
    (harg3 : ∃ N, ∀ f ≥ N, evalOpt f w env arg3 = some av3)
    (hbody : ∃ N, ∀ f ≥ N,
      evalOpt f w (bindArgs [formal1, formal2, formal3] [av1, av2, av3]) body = some v) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol fn)) (.cons arg1 (.cons arg2 (.cons arg3 .nil))))
      = evalOpt f w env (substTerm [formal1, formal2, formal3] [arg1, arg2, arg3] body) := by
  have hlhs : ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol fn)) (.cons arg1 (.cons arg2 (.cons arg3 .nil)))) = some v :=
    conv_defn_3 w env fn arg1 arg2 arg3 av1 av2 av3 formal1 formal2 formal3 body v
      hns hdef harg1 harg2 harg3 hbody
  obtain ⟨Narg1, harg1'⟩ := harg1
  obtain ⟨Narg2, harg2'⟩ := harg2
  obtain ⟨Narg3, harg3'⟩ := harg3
  obtain ⟨Ncong, hcong⟩ := evalOpt_substTerm_conv w env [formal1, formal2, formal3]
    (List.map quoteVal [av1, av2, av3]) [arg1, arg2, arg3] (max (max (max Narg1 Narg2) Narg3) 1)
    (by
      intro s g hg
      by_cases h1 : s = formal1
      · simp only [List.map_cons, List.map_nil, lookupSubst,
                   show (s == formal1) = true from by simp [h1],
                   ↓reduceIte, Option.getD_some, quoteVal]
        obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
        rw [evalOpt_quote k w env av1, harg1' (k + 1) (by omega)]
      · by_cases h2 : s = formal2
        · simp only [List.map_cons, List.map_nil, lookupSubst,
                     show (s == formal1) = false from by simpa using h1,
                     show (s == formal2) = true from by simp [h2],
                     Bool.false_eq_true, ↓reduceIte, Option.getD_some, quoteVal]
          obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
          rw [evalOpt_quote k w env av2, harg2' (k + 1) (by omega)]
        · by_cases h3 : s = formal3
          · simp only [List.map_cons, List.map_nil, lookupSubst,
                       show (s == formal1) = false from by simpa using h1,
                       show (s == formal2) = false from by simpa using h2,
                       show (s == formal3) = true from by simp [h3],
                       Bool.false_eq_true, ↓reduceIte, Option.getD_some, quoteVal]
            obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
            rw [evalOpt_quote k w env av3, harg3' (k + 1) (by omega)]
          · simp only [List.map_cons, List.map_nil, lookupSubst,
                       show (s == formal1) = false from by simpa using h1,
                       show (s == formal2) = false from by simpa using h2,
                       show (s == formal3) = false from by simpa using h3,
                       Bool.false_eq_true, ↓reduceIte, Option.getD_none])
    (sizeOf body) body (Nat.le_refl _) hws
  have hrhs : ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (substTerm [formal1, formal2, formal3] [arg1, arg2, arg3] body) = some v := by
    obtain ⟨Nb, hb⟩ := hbody
    refine ⟨max Ncong Nb, fun f hf => ?_⟩
    rw [← hcong f (by omega),
        evalOpt_substTerm_quote w [formal1, formal2, formal3] [av1, av2, av3] f env body hws,
        evalOpt_bindArgsOver_bindArgs w env [formal1, formal2, formal3] [av1, av2, av3]
          rfl f body hws hclosed]
    exact hb f (by omega)
  obtain ⟨Nl, hl⟩ := hlhs; obtain ⟨Nr, hr⟩ := hrhs
  exact ⟨max Nl Nr, fun f hf => by rw [hl f (by omega), hr f (by omega)]⟩

/-- The (1-formal) SUBSTITUTION LEMMA: evaluating `substTerm [s] [arg] body` in
    `env` agrees (eventually) with evaluating `body` in `env` extended by `s ↦ av`,
    whenever `arg` converges to `av`. Composes the args-agreement congruence
    (`evalOpt_substTerm_conv`, with `arg` vs `quoteVal av`) and the quoted-value
    bridge (`evalOpt_substTerm_quote`). Unlike `evalOpt_unfold1_conv` it does NOT
    require `body` closed under `[s]` — the base `env` survives for the other free
    variables. This is how the driver converts an induction hypothesis (stated over
    the induction variable) into the goal-env terms it must rewrite. -/
theorem evalOpt_substTerm_subst1 (w : World) (env : Env) (s : Symbol)
    (arg av body : SExpr) (hnl : WellScoped body = true)
    (harg : ∃ N, ∀ f ≥ N, evalOpt f w env arg = some av) :
    ∃ N, ∀ f ≥ N, evalOpt f w env (substTerm [s] [arg] body)
      = evalOpt f w (bindArgsOver env [s] [av]) body := by
  obtain ⟨Narg, harg'⟩ := harg
  obtain ⟨Ncong, hcong⟩ := evalOpt_substTerm_conv w env [s] (List.map quoteVal [av]) [arg]
    (max Narg 1)
    (by
      intro s' g hg
      by_cases hsf : s' = s
      · subst hsf
        simp only [List.map_cons, List.map_nil, lookupSubst, beq_self_eq_true,
                   ↓reduceIte, Option.getD_some, quoteVal]
        obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
        rw [evalOpt_quote k w env av, harg' (k + 1) (by omega)]
      · simp only [List.map_cons, List.map_nil, lookupSubst,
                   show (s' == s) = false from by simpa using hsf, Bool.false_eq_true,
                   ↓reduceIte, Option.getD_none])
    (sizeOf body) body (Nat.le_refl _) hnl
  refine ⟨Ncong, fun f hf => ?_⟩
  rw [← hcong f hf, evalOpt_substTerm_quote w [s] [av] f env body hnl]

/-- Eventual version of `lookupSubst_eval_congr` (G5/v2): each arg CONVERGES
    to its value, so the substituted-variable lookups agree for all fuel past
    one threshold (the max of the per-arg thresholds). -/
theorem lookupSubst_eval_congr_conv (w : World) (env : Env) :
    ∀ (formals : List Symbol) (args vals : List SExpr), args.length = vals.length →
      (∀ p ∈ args.zip vals, ∃ N, ∀ f ≥ N, evalOpt f w env p.1 = some p.2) →
      ∃ Nag, ∀ (s : Symbol) (g : Nat), g ≥ Nag →
        evalOpt g w env ((lookupSubst s formals args).getD (.atom (.symbol s)))
          = evalOpt g w env
              ((lookupSubst s formals (vals.map quoteVal)).getD (.atom (.symbol s)))
  | [], _, _, _, _ => ⟨0, fun s g _ => by simp [lookupSubst]⟩
  | _ :: _, [], [], _, _ => ⟨0, fun s g _ => by simp [lookupSubst]⟩
  | f :: fs, a :: as, v :: vs, hlen, hz => by
      obtain ⟨Na, ha⟩ := hz (a, v) (by simp [List.zip_cons_cons])
      obtain ⟨Nfs, hfs⟩ := lookupSubst_eval_congr_conv w env fs as vs (by simpa using hlen)
        (fun p hmem => hz p (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hmem))
      refine ⟨max (Na + 1) Nfs, fun s g hg => ?_⟩
      rw [lookupSubst_map_quoteVal]
      simp only [lookupSubst]
      by_cases h : s == f
      · simp only [h, if_true, Option.map_some, Option.getD_some, quoteVal]
        obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
        rw [evalOpt_quote k w env v, ha (k + 1) (by omega)]
      · simp only [h, Bool.false_eq_true, if_false, ← lookupSubst_map_quoteVal]
        exact hfs s g (by omega)
  | _ :: _, [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, _ :: _, [], hlen, _ => by simp at hlen

/-- The N-formal SIMULTANEOUS SUBSTITUTION LEMMA (G5/v2 induction scaffold):
    evaluating `substTerm formals args body` in `env` agrees eventually with
    evaluating `body` in `env` extended by the formals bound to the args'
    VALUES — values computed in the ORIGINAL env, so sequential insertion of
    the precomputed values IS simultaneous-substitution semantics (ACL2's IH
    alists, e.g. perm-cons's `x := (cdr x), y := (rm (car x) y)`).
    `evalOpt_substTerm_subst1` is the singleton case. -/
theorem evalOpt_substTerm_substN (w : World) (env : Env)
    (formals : List Symbol) (args vals : List SExpr) (body : SExpr)
    (hnl : WellScoped body = true) (hlen : args.length = vals.length)
    (hargs : ∀ p ∈ args.zip vals,
      ∃ N, ∀ f ≥ N, evalOpt f w env p.1 = some p.2) :
    ∃ N, ∀ f ≥ N, evalOpt f w env (substTerm formals args body)
      = evalOpt f w (bindArgsOver env formals vals) body := by
  obtain ⟨Nag, hag⟩ := lookupSubst_eval_congr_conv w env formals args vals hlen hargs
  obtain ⟨Ncong, hcong⟩ := evalOpt_substTerm_conv w env formals (vals.map quoteVal) args
    Nag (fun s g hg => (hag s g hg).symm) (sizeOf body) body (Nat.le_refl _) hnl
  refine ⟨Ncong, fun f hf => ?_⟩
  rw [← hcong f hf, evalOpt_substTerm_quote w formals vals f env body hnl]

/-! ### The LAMBDA-BODY boundary (translated `let`; S2 2026-07-24)

  ACL2's rewriter descends into a lambda application by rewriting the ACTUALS
  in place and then rewriting the BODY under `formals ↦ actuals` — the
  `(LAMBDA-BODY . fn)` path frame, whose recorded redex is the body with the
  formals already replaced. `evalOpt_lam_beta_conv` is exactly that step. -/

/-- Per-argument convergence lifts to the argument spine's `mapM`. -/
theorem mapM_conv_of_zip (w : World) (env : Env) :
    ∀ (actuals vals : List SExpr), actuals.length = vals.length →
      (∀ p ∈ actuals.zip vals, ∃ N, ∀ f ≥ N, evalOpt f w env p.1 = some p.2) →
      ∃ N, ∀ f ≥ N, actuals.mapM (fun a => evalOpt f w env a) = some vals
  | [], [], _, _ => ⟨0, fun _ _ => rfl⟩
  | a :: as, v :: vs, hlen, hz => by
      obtain ⟨Na, ha⟩ := hz (a, v) (by simp [List.zip_cons_cons])
      obtain ⟨Nr, hr⟩ := mapM_conv_of_zip w env as vs (by simpa using hlen)
        (fun p hp => hz p (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hp))
      refine ⟨max Na Nr, fun f hf => ?_⟩
      have h1 : evalOpt f w env a = some v := ha f (by omega)
      simp [List.mapM_cons, h1, hr f (by omega)]
  | _ :: _, [], hlen, _ => by simp at hlen
  | [], _ :: _, hlen, _ => by simp at hlen

/-- A translated `let` converges to its body's value in the extended env. -/
theorem conv_lam (w : World) (env : Env) (lam : Symbol)
    (formalsE lamBody argsExpr : SExpr)
    (lformals : List Symbol) (actuals vals : List SExpr) (v : SExpr)
    (hlam : lam.isNamed "LAMBDA" = true)
    (hform : lamFormals? formalsE = some lformals)
    (hargs : argsExpr.toList? = some actuals)
    (hlenA : actuals.length = vals.length)
    (hlen : lformals.length = vals.length)
    (hconv : ∀ p ∈ actuals.zip vals, ∃ N, ∀ f ≥ N, evalOpt f w env p.1 = some p.2)
    (hbody : ∃ N, ∀ f ≥ N, evalOpt f w (bindArgsOver env lformals vals) lamBody = some v) :
    ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.cons (.atom (.symbol lam)) (.cons formalsE (.cons lamBody .nil))) argsExpr)
      = some v := by
  obtain ⟨Nm, hm⟩ := mapM_conv_of_zip w env actuals vals hlenA hconv
  obtain ⟨Nb, hb⟩ := hbody
  refine ⟨max Nm Nb + 1, fun f hf => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
  show evalOptStep (evalOpt m) w env _ = some v
  simp only [evalOptStep_cons_lam, hlam, if_true, hform, hargs]
  rw [hm m (by omega)]
  show (if lformals.length = vals.length
          then evalOpt m w (bindArgsOver env lformals vals) lamBody else none) = some v
  rw [if_pos hlen]
  exact hb m (by omega)

/-! Congruence in a translated `let`'s ACTUALS (the `(k LAMBDA …)` path frame:
    ACL2 rewrites a lambda application's actuals in place before descending
    into the body). No `not_special` side condition — a lambda head is never
    `QUOTE`/`IF`/`LET`. Arities 1–2 are the emitted frontier (the pinned
    corpus's `let`/`mv-let`/metafunction binders); a wider binder hard-fails
    in the path walker rather than being approximated. -/

/-- Unary lambda-application argument congruence. -/
theorem evalOpt_congr_lam1 (w : World) (env : Env) (lam : Symbol)
    (formalsE lamBody a a' : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env a = evalOpt f w env a') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.cons (.atom (.symbol lam))
        (.cons formalsE (.cons lamBody .nil))) (.cons a .nil))
      = evalOpt f w env (.cons (.cons (.atom (.symbol lam))
        (.cons formalsE (.cons lamBody .nil))) (.cons a' .nil)) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 1, fun f hf => ?_⟩
  match f with
  | m + 1 =>
    have hm := hN m (by omega)
    show evalOptStep (evalOpt m) w env _ = evalOptStep (evalOpt m) w env _
    simp only [evalOptStep_cons_lam]
    by_cases hlam : lam.isNamed "LAMBDA" = true
    · simp only [hlam, if_true]
      cases hform : lamFormals? formalsE with
      | none => rfl
      | some lformals =>
        show (do let argVals ← [a].mapM (evalOpt m w env ·)
                 if lformals.length = argVals.length
                 then evalOpt m w (bindArgsOver env lformals argVals) lamBody else none)
           = (do let argVals ← [a'].mapM (evalOpt m w env ·)
                 if lformals.length = argVals.length
                 then evalOpt m w (bindArgsOver env lformals argVals) lamBody else none)
        simp only [List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind, hm]
    · simp only [Bool.not_eq_true] at hlam
      simp only [hlam, Bool.false_eq_true, if_false]

/-- Binary lambda-application argument congruence, first actual. -/
theorem evalOpt_congr_lam2_left (w : World) (env : Env) (lam : Symbol)
    (formalsE lamBody a a' b : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env a = evalOpt f w env a') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.cons (.atom (.symbol lam))
        (.cons formalsE (.cons lamBody .nil))) (.cons a (.cons b .nil)))
      = evalOpt f w env (.cons (.cons (.atom (.symbol lam))
        (.cons formalsE (.cons lamBody .nil))) (.cons a' (.cons b .nil))) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 1, fun f hf => ?_⟩
  match f with
  | m + 1 =>
    have hm := hN m (by omega)
    show evalOptStep (evalOpt m) w env _ = evalOptStep (evalOpt m) w env _
    simp only [evalOptStep_cons_lam]
    by_cases hlam : lam.isNamed "LAMBDA" = true
    · simp only [hlam, if_true]
      cases hform : lamFormals? formalsE with
      | none => rfl
      | some lformals =>
        show (do let argVals ← [a, b].mapM (evalOpt m w env ·)
                 if lformals.length = argVals.length
                 then evalOpt m w (bindArgsOver env lformals argVals) lamBody else none)
           = (do let argVals ← [a', b].mapM (evalOpt m w env ·)
                 if lformals.length = argVals.length
                 then evalOpt m w (bindArgsOver env lformals argVals) lamBody else none)
        simp only [List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind, hm]
    · simp only [Bool.not_eq_true] at hlam
      simp only [hlam, Bool.false_eq_true, if_false]

/-- Binary lambda-application argument congruence, second actual. -/
theorem evalOpt_congr_lam2_right (w : World) (env : Env) (lam : Symbol)
    (formalsE lamBody a b b' : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env b = evalOpt f w env b') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.cons (.atom (.symbol lam))
        (.cons formalsE (.cons lamBody .nil))) (.cons a (.cons b .nil)))
      = evalOpt f w env (.cons (.cons (.atom (.symbol lam))
        (.cons formalsE (.cons lamBody .nil))) (.cons a (.cons b' .nil))) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 1, fun f hf => ?_⟩
  match f with
  | m + 1 =>
    have hm := hN m (by omega)
    show evalOptStep (evalOpt m) w env _ = evalOptStep (evalOpt m) w env _
    simp only [evalOptStep_cons_lam]
    by_cases hlam : lam.isNamed "LAMBDA" = true
    · simp only [hlam, if_true]
      cases hform : lamFormals? formalsE with
      | none => rfl
      | some lformals =>
        show (do let argVals ← [a, b].mapM (evalOpt m w env ·)
                 if lformals.length = argVals.length
                 then evalOpt m w (bindArgsOver env lformals argVals) lamBody else none)
           = (do let argVals ← [a, b'].mapM (evalOpt m w env ·)
                 if lformals.length = argVals.length
                 then evalOpt m w (bindArgsOver env lformals argVals) lamBody else none)
        simp only [List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind, hm]
    · simp only [Bool.not_eq_true] at hlam
      simp only [hlam, Bool.false_eq_true, if_false]

/-- BETA at the `LAMBDA-BODY` boundary: a translated `let` evaluates like its
    body with the actual TERMS substituted for the formals. Faithful to the
    rewriter's own move — ACL2 rewrites the body under `formals ↦ actuals`,
    and the emitted redex at that frame is the substituted body. -/
theorem evalOpt_lam_beta_conv (w : World) (env : Env) (lam : Symbol)
    (formalsE lamBody argsExpr : SExpr)
    (lformals : List Symbol) (actuals vals : List SExpr) (v : SExpr)
    (hlam : lam.isNamed "LAMBDA" = true)
    (hform : lamFormals? formalsE = some lformals)
    (hargs : argsExpr.toList? = some actuals)
    (hlenA : actuals.length = vals.length)
    (hlen : lformals.length = vals.length)
    (hnl : WellScoped lamBody = true)
    (hconv : ∀ p ∈ actuals.zip vals, ∃ N, ∀ f ≥ N, evalOpt f w env p.1 = some p.2)
    (hbody : ∃ N, ∀ f ≥ N, evalOpt f w (bindArgsOver env lformals vals) lamBody = some v) :
    ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.cons (.atom (.symbol lam)) (.cons formalsE (.cons lamBody .nil))) argsExpr)
      = evalOpt f w env (substTerm lformals actuals lamBody) := by
  obtain ⟨Nl, hl⟩ := conv_lam w env lam formalsE lamBody argsExpr lformals actuals vals v
    hlam hform hargs hlenA hlen hconv hbody
  obtain ⟨Ns, hs⟩ := evalOpt_substTerm_substN w env lformals actuals vals lamBody hnl hlenA hconv
  obtain ⟨Nb, hb⟩ := hbody
  refine ⟨max Nl (max Ns Nb), fun f hf => ?_⟩
  rw [hl f (by omega), hs f (by omega), hb f (by omega)]

/-- ∀-env-route BETA for a 1-actual translated `let` — the driver-facing form
    of `evalOpt_lam_beta_conv` (the `re_unfold1_conv` analogue: the actual's
    value and the body's value stay existential). -/
theorem re_lam_beta1_conv (w : World) (env : Env) (lam : Symbol)
    (formalsE lamBody a : SExpr) (lf : Symbol)
    (hlam : lam.isNamed "LAMBDA" = true)
    (hform : lamFormals? formalsE = some [lf])
    (hnl : WellScoped lamBody = true)
    (harg : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av)
    (hbodyAll : ∀ env', ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' lamBody = some v) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.cons (.atom (.symbol lam))
        (.cons formalsE (.cons lamBody .nil))) (.cons a .nil))
      = evalOpt f w env (substTerm [lf] [a] lamBody) := by
  obtain ⟨Na, av, ha⟩ := harg
  obtain ⟨Nb, v, hb⟩ := hbodyAll (bindArgsOver env [lf] [av])
  exact evalOpt_lam_beta_conv w env lam formalsE lamBody (.cons a .nil) [lf] [a] [av] v
    hlam hform rfl rfl rfl hnl
    (by intro p hp; simp only [List.zip_cons_cons, List.zip_nil_right,
          List.mem_singleton] at hp; subst hp; exact ⟨Na, ha⟩)
    ⟨Nb, hb⟩

/-- ∀-env-route BETA for a 2-actual translated `let` (`mv-let`, metafunction
    binders). -/
theorem re_lam_beta2_conv (w : World) (env : Env) (lam : Symbol)
    (formalsE lamBody a b : SExpr) (f1 f2 : Symbol)
    (hlam : lam.isNamed "LAMBDA" = true)
    (hform : lamFormals? formalsE = some [f1, f2])
    (hnl : WellScoped lamBody = true)
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∃ bv, ∀ f ≥ N, evalOpt f w env b = some bv)
    (hbodyAll : ∀ env', ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' lamBody = some v) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.cons (.atom (.symbol lam))
        (.cons formalsE (.cons lamBody .nil))) (.cons a (.cons b .nil)))
      = evalOpt f w env (substTerm [f1, f2] [a, b] lamBody) := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨Nb, bv, hb⟩ := hb
  obtain ⟨Nv, v, hv⟩ := hbodyAll (bindArgsOver env [f1, f2] [av, bv])
  exact evalOpt_lam_beta_conv w env lam formalsE lamBody (.cons a (.cons b .nil))
    [f1, f2] [a, b] [av, bv] v hlam hform rfl rfl rfl hnl
    (by intro p hp
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
          List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact ⟨Na, ha⟩
        · exact ⟨Nb, hb⟩)
    ⟨Nv, hv⟩

/-! VALUE-characterized BETA (the DP-lift walkers' form): a translated `let`
    converges to whatever its BETA-REDUCT converges to in the same env. The
    walkers descend into `substTerm formals actuals body` — the very term
    ACL2's rewriter records at the `LAMBDA-BODY` frame — so value and proof
    are built from one shape. -/

/-- 1-actual value-route beta. -/
theorem re_lam_beta1_val (w : World) (env : Env) (lam : Symbol)
    (formalsE lamBody a : SExpr) (lf : Symbol) (av v : SExpr)
    (hlam : lam.isNamed "LAMBDA" = true)
    (hform : lamFormals? formalsE = some [lf])
    (hnl : WellScoped lamBody = true)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some av)
    (hsub : ∃ N, ∀ f ≥ N, evalOpt f w env (substTerm [lf] [a] lamBody) = some v) :
    ∃ N, ∀ f ≥ N, evalOpt f w env (.cons (.cons (.atom (.symbol lam))
      (.cons formalsE (.cons lamBody .nil))) (.cons a .nil)) = some v := by
  have hzip : ∀ p ∈ ([a].zip [av]), ∃ N, ∀ f ≥ N, evalOpt f w env p.1 = some p.2 := by
    intro p hp
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp; exact ha
  obtain ⟨Ns, hs⟩ := evalOpt_substTerm_substN w env [lf] [a] [av] lamBody hnl rfl hzip
  obtain ⟨Nh, hh⟩ := hsub
  have hbody : ∃ N, ∀ f ≥ N, evalOpt f w (bindArgsOver env [lf] [av]) lamBody = some v := by
    refine ⟨max Ns Nh, fun f hf => ?_⟩
    rw [← hs f (by omega)]; exact hh f (by omega)
  exact conv_lam w env lam formalsE lamBody (.cons a .nil) [lf] [a] [av] v
    hlam hform rfl rfl rfl hzip hbody

/-- 2-actual value-route beta. -/
theorem re_lam_beta2_val (w : World) (env : Env) (lam : Symbol)
    (formalsE lamBody a b : SExpr) (f1 f2 : Symbol) (av bv v : SExpr)
    (hlam : lam.isNamed "LAMBDA" = true)
    (hform : lamFormals? formalsE = some [f1, f2])
    (hnl : WellScoped lamBody = true)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some bv)
    (hsub : ∃ N, ∀ f ≥ N, evalOpt f w env (substTerm [f1, f2] [a, b] lamBody) = some v) :
    ∃ N, ∀ f ≥ N, evalOpt f w env (.cons (.cons (.atom (.symbol lam))
      (.cons formalsE (.cons lamBody .nil))) (.cons a (.cons b .nil))) = some v := by
  have hzip : ∀ p ∈ ([a, b].zip [av, bv]),
      ∃ N, ∀ f ≥ N, evalOpt f w env p.1 = some p.2 := by
    intro p hp
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ha
    · exact hb
  obtain ⟨Ns, hs⟩ := evalOpt_substTerm_substN w env [f1, f2] [a, b] [av, bv] lamBody hnl rfl hzip
  obtain ⟨Nh, hh⟩ := hsub
  have hbody : ∃ N, ∀ f ≥ N,
      evalOpt f w (bindArgsOver env [f1, f2] [av, bv]) lamBody = some v := by
    refine ⟨max Ns Nh, fun f hf => ?_⟩
    rw [← hs f (by omega)]; exact hh f (by omega)
  exact conv_lam w env lam formalsE lamBody (.cons a (.cons b .nil)) [f1, f2] [a, b] [av, bv] v
    hlam hform rfl rfl rfl hzip hbody

/-- v-EXISTENTIAL beta convergence (1 actual) — the `proveConv` wrapper of
    `re_lam_beta1_val`: a translated `let` converges because its actual and
    its beta-reduct do. -/
theorem re_conv_lam1 (w : World) (env : Env) (lam : Symbol)
    (formalsE lamBody a : SExpr) (lf : Symbol)
    (hlam : lam.isNamed "LAMBDA" = true)
    (hform : lamFormals? formalsE = some [lf])
    (hnl : WellScoped lamBody = true)
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av)
    (hsub : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env (substTerm [lf] [a] lamBody) = some v) :
    ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env (.cons (.cons (.atom (.symbol lam))
      (.cons formalsE (.cons lamBody .nil))) (.cons a .nil)) = some v := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨Ns, v, hs⟩ := hsub
  obtain ⟨N, hN⟩ := re_lam_beta1_val w env lam formalsE lamBody a lf av v
    hlam hform hnl ⟨Na, ha⟩ ⟨Ns, hs⟩
  exact ⟨N, v, hN⟩

/-- v-EXISTENTIAL beta convergence (2 actuals). -/
theorem re_conv_lam2 (w : World) (env : Env) (lam : Symbol)
    (formalsE lamBody a b : SExpr) (f1 f2 : Symbol)
    (hlam : lam.isNamed "LAMBDA" = true)
    (hform : lamFormals? formalsE = some [f1, f2])
    (hnl : WellScoped lamBody = true)
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∃ bv, ∀ f ≥ N, evalOpt f w env b = some bv)
    (hsub : ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (substTerm [f1, f2] [a, b] lamBody) = some v) :
    ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env (.cons (.cons (.atom (.symbol lam))
      (.cons formalsE (.cons lamBody .nil))) (.cons a (.cons b .nil))) = some v := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨Nb, bv, hb⟩ := hb
  obtain ⟨Ns, v, hs⟩ := hsub
  obtain ⟨N, hN⟩ := re_lam_beta2_val w env lam formalsE lamBody a b f1 f2 av bv v
    hlam hform hnl ⟨Na, ha⟩ ⟨Nb, hb⟩ ⟨Ns, hs⟩
  exact ⟨N, v, hN⟩

/-! ## Layer 2: Derived rules (compose Layer 1) -/

/-- Logic.equal returns T iff arguments are BEq-equal. -/
theorem Logic.equal_t_iff (a b : SExpr) :
    Logic.equal a b = SExpr.t ↔ a = b := by
  constructor
  · intro h
    simp [Logic.equal] at h
    exact h
  · intro h; subst h; exact Logic.equal_self a

/-- A truthy `Logic.equal` pins genuine equality — the two-valued decode
    every `EvTrue` consumer of an `equal`-headed fact uses (G2: no exact-t
    pin needed; `Logic.equal` returns `t` or `nil` by definition). -/
theorem Logic.eq_of_equal_ne_nil {a b : SExpr}
    (h : Logic.equal a b ≠ SExpr.nil) : a = b := by
  by_cases hab : a == b
  · exact eq_of_beq hab
  · simp [Logic.equal, hab] at h

/-- Logic.not returns NIL iff the argument is truthy (non-nil). -/
theorem Logic.not_nil_iff (a : SExpr) :
    Logic.not a = SExpr.nil ↔ Logic.toBool a = true := by
  simp [Logic.not]

/-- normalizedName for lowercase symbols is identity (needed because
    String.map Char.toLower is @[irreducible]). -/
theorem Symbol.normalizedName_lowercase (s : Symbol)
    (h : s.name = s.name) : s.name = s.name := h.symm

-- callBuiltin for specific builtins — avoids unfolding the whole match.
-- These use the string directly, not normalizedName.
@[simp] theorem callBuiltin_equal (a b : SExpr) :
    callBuiltin "EQUAL" [a, b] = some (Logic.equal a b) := by rfl
@[simp] theorem callBuiltin_not (a : SExpr) :
    callBuiltin "NOT" [a] = some (Logic.not a) := by rfl
@[simp] theorem callBuiltin_consp (a : SExpr) :
    callBuiltin "CONSP" [a] = some (Logic.consp a) := by rfl
@[simp] theorem callBuiltin_car (a : SExpr) :
    callBuiltin "CAR" [a] = some (Logic.car a) := by rfl
@[simp] theorem callBuiltin_cdr (a : SExpr) :
    callBuiltin "CDR" [a] = some (Logic.cdr a) := by rfl
@[simp] theorem callBuiltin_plus (a b : SExpr) :
    callBuiltin "BINARY-+" [a, b] = some (Logic.plus a b) := by rfl
@[simp] theorem callBuiltin_times (a b : SExpr) :
    callBuiltin "BINARY-*" [a, b] = some (Logic.times a b) := by rfl
@[simp] theorem callBuiltin_true_listp (a : SExpr) :
    callBuiltin "TRUE-LISTP" [a] = some (Logic.trueListp a) := by
  rfl

@[simp] theorem callBuiltin_acl2_numberp (a : SExpr) :
    callBuiltin "ACL2-NUMBERP" [a] = some (Logic.acl2Numberp a) := by
  cases a with
  | atom x => cases x <;> rfl
  | nil => rfl
  | cons _ _ => rfl
@[simp] theorem callBuiltin_atom (a : SExpr) :
    callBuiltin "ATOM" [a] = some (Logic.atom a) := by rfl
@[simp] theorem callBuiltin_endp (a : SExpr) :
    callBuiltin "ENDP" [a] = some (Logic.endp a) := by rfl
@[simp] theorem callBuiltin_natp (a : SExpr) :
    callBuiltin "NATP" [a] = some (Logic.natp a) := by rfl
@[simp] theorem callBuiltin_posp (a : SExpr) :
    callBuiltin "POSP" [a] = some (Logic.posp a) := by rfl
@[simp] theorem callBuiltin_booleanp (a : SExpr) :
    callBuiltin "BOOLEANP" [a] = some (Logic.booleanp a) := by rfl
@[simp] theorem callBuiltin_symbolp (a : SExpr) :
    callBuiltin "SYMBOLP" [a] = some (Logic.symbolp a) := by rfl
@[simp] theorem callBuiltin_stringp (a : SExpr) :
    callBuiltin "STRINGP" [a] = some (Logic.stringp a) := by rfl
@[simp] theorem callBuiltin_rationalp (a : SExpr) :
    callBuiltin "RATIONALP" [a] = some (Logic.rationalp a) := by
  cases a with
  | atom x => cases x <;> rfl
  | nil => rfl
  | cons _ _ => rfl
@[simp] theorem callBuiltin_nfix (a : SExpr) :
    callBuiltin "NFIX" [a] = some (Logic.nfix a) := by rfl
@[simp] theorem callBuiltin_len (a : SExpr) :
    callBuiltin "LEN" [a] = some (Logic.len a) := by rfl
@[simp] theorem callBuiltin_fix (a : SExpr) :
    callBuiltin "FIX" [a] = some (Logic.fix a) := by rfl

/-! ## D4 — builtin DEFINITION FACTS (external-knowledge design §D4, WP2)

Each `gz_def_<fn>` lemma states that a `callBuiltin` builtin's value function
agrees, pointwise, with the VALUE COMPOSITION of ACL2's own ground-zero defun
body for that function — the `(:DEFUN <fn> … :SOURCE :GROUND-ZERO)` snapshot
emitted at capture start. The rhs is EXACTLY the shape the driver's value
walker (`dpValExpr`/`re_val_if`: `cond (toBool ·) · ·` for `if`, the `Logic`
function for a builtin application, the literal for a quote) builds from the
emitted body, so the D4 route in `replayDefinition` can apply the lemma ONLY
when the emitted snapshot instance unifies — a drifted emission fails proof
construction (the fail-closed recompute-check; the statement is never trusted
free-floating).

Bonus, not incidental (design §D4): each lemma is a kernel-checked proof that
the trusted-core primitive agrees with ACL2's own definition of the function —
a fidelity validation the differential harness can only sample. -/

/-- `(DEFUN TRUE-LISTP (X) (IF (CONSP X) (TRUE-LISTP (CDR X)) (EQ X NIL)))`
    (the snapshot body carries the translated `(EQUAL X 'NIL)`). -/
theorem gz_def_true_listp (a : SExpr) :
    Logic.trueListp a
      = cond (Logic.toBool (Logic.consp a))
          (Logic.trueListp (Logic.cdr a))
          (Logic.equal a SExpr.nil) := by
  cases a <;> rfl

/-- `(DEFUN LEN (X) (IF (CONSP X) (+ 1 (LEN (CDR X))) 0))` (the snapshot
    body carries the translated `(BINARY-+ '1 (LEN (CDR X)))`). -/
theorem gz_def_len (a : SExpr) :
    Logic.len a
      = cond (Logic.toBool (Logic.consp a))
          (Logic.plus (.atom (.number (.int 1))) (Logic.len (Logic.cdr a)))
          (.atom (.number (.int 0))) := by
  cases a with
  | cons h t =>
    -- `len` returns an int atom for every constructor of `t`, so the
    -- rational `plus` collapses to integer successor.
    obtain ⟨k, hk⟩ : ∃ k, Logic.len t = .atom (.number (.int k)) := by
      cases t <;> exact ⟨_, rfl⟩
    simp [Logic.len, Logic.plus, Logic.mkNumber, Logic.toRat, hk, Int.add_comm]
  | nil => rfl
  | atom x => rfl

/-- `(DEFUN NOT (P) (IF P NIL T))`. -/
theorem gz_def_not (a : SExpr) :
    Logic.not a = cond (Logic.toBool a) SExpr.nil SExpr.t := by
  cases a <;> rfl

/-- `(DEFUN NFIX (X) (IF (INTEGERP X) (IF (< X 0) 0 X) 0))`. -/
theorem gz_def_nfix (a : SExpr) :
    Logic.nfix a
      = cond (Logic.toBool (Logic.integerp a))
          (cond (Logic.toBool (Logic.lt a (.atom (.number (.int 0)))))
            (.atom (.number (.int 0))) a)
          (.atom (.number (.int 0))) := by
  cases a with
  | atom x =>
    cases x with
    | number n =>
      cases n with
      | int k =>
        rcases lt_or_ge k 0 with hk | hk <;>
          simp [Logic.toRat, hk, Int.not_lt.mpr, Int.not_le.mpr]
      | rational n d hc => rfl
    | _ => rfl
  | _ => rfl

/-- `(DEFUN FIX (X) (IF (ACL2-NUMBERP X) X 0))`. -/
theorem gz_def_fix (a : SExpr) :
    Logic.fix a
      = cond (Logic.toBool (Logic.acl2Numberp a)) a
          (.atom (.number (.int 0))) := by
  cases a with
  | atom x => cases x <;> rfl
  | _ => rfl

/-- `(DEFUN BOOLEANP (X) (IF (EQUAL X T) T (EQUAL X NIL)))`. -/
theorem gz_def_booleanp (a : SExpr) :
    Logic.booleanp a
      = cond (Logic.toBool (Logic.equal a SExpr.t)) SExpr.t
          (Logic.equal a SExpr.nil) := by
  by_cases ht : a == SExpr.t <;> by_cases hn : a == SExpr.nil <;>
    simp_all [Logic.booleanp, Logic.equal]

/-- `(DEFUN ENDP (X) (IF (CONSP X) NIL T))` (a `defun` in axioms.lisp;
    guard-trivial body). -/
theorem gz_def_endp (a : SExpr) :
    Logic.endp a
      = cond (Logic.toBool (Logic.consp a)) SExpr.nil SExpr.t := by
  cases a <;> rfl

/-- `(DEFUN ATOM (X) (IF (CONSP X) NIL T))` — same body shape as `ENDP`. -/
theorem gz_def_atom (a : SExpr) :
    Logic.atom a
      = cond (Logic.toBool (Logic.consp a)) SExpr.nil SExpr.t := by
  cases a <;> rfl

/-- T3: EQUAL-self — (EQUAL t t) evaluates to T when t converges. -/
theorem evalOpt_equal_self (f : Nat) (w : World) (env : Env)
    (t : SExpr) (v : SExpr)
    (hv : evalOpt f w env t = some v)
    (h_not_def : w.defs.get? ({ name := "EQUAL" } : Symbol) = none) :
    evalOpt (f + 1) w env
      (.cons (.atom (.symbol { name := "EQUAL" })) (.cons t (.cons t .nil)))
    = some SExpr.t := by
  have h_ns : ({ name := "EQUAL" } : Symbol).isNamed "QUOTE" = false ∧
              ({ name := "EQUAL" } : Symbol).isNamed "IF" = false ∧
              ({ name := "EQUAL" } : Symbol).isNamed "LET" = false ∧
              ({ name := "EQUAL" } : Symbol).isNamed "LET*" = false := by decide
  rw [evalOpt_builtin_2 f w env { name := "EQUAL" } t t v v h_ns h_not_def hv hv]
  simp [callBuiltin_equal]

/-- T2: EQUAL-T implies evaluation equality. -/
theorem eval_equal_t_implies_eq (f : Nat) (w : World) (env : Env)
    (a b : SExpr) (va vb : SExpr)
    (ha : evalOpt f w env a = some va)
    (hb : evalOpt f w env b = some vb)
    (h_not_def : w.defs.get? (({ name := "EQUAL" } : Symbol)) = none)
    (h_eq : evalOpt (f + 1) w env
      (.cons (.atom (.symbol (({ name := "EQUAL" } : Symbol)))) (.cons a (.cons b .nil)))
      = some SExpr.t) :
    va = vb := by
  have h_ns : (({ name := "EQUAL" } : Symbol)).isNamed "QUOTE" = false ∧
              (({ name := "EQUAL" } : Symbol)).isNamed "IF" = false ∧
              (({ name := "EQUAL" } : Symbol)).isNamed "LET" = false ∧
              (({ name := "EQUAL" } : Symbol)).isNamed "LET*" = false := by decide
  rw [evalOpt_builtin_2 f w env (({ name := "EQUAL" } : Symbol)) a b va vb h_ns h_not_def ha hb] at h_eq
  -- h_eq : some (callBuiltin "EQUAL" [va, vb]) = some SExpr.t
  simp only [callBuiltin_equal, Option.some.injEq] at h_eq
  exact (Logic.equal_t_iff va vb).mp h_eq

/-- T11a: NOT(e) = NIL implies e evaluates to something truthy. -/
theorem not_nil_means_truthy (f : Nat) (w : World) (env : Env)
    (t : SExpr) (tv : SExpr)
    (h_not_def : w.defs.get? (({ name := "NOT" } : Symbol)) = none)
    (ht : evalOpt f w env t = some tv)
    (h_not : evalOpt (f + 1) w env
      (.cons (.atom (.symbol (({ name := "NOT" } : Symbol)))) (.cons t .nil))
      = some SExpr.nil) :
    Logic.toBool tv = true := by
  have h_ns : (({ name := "NOT" } : Symbol)).isNamed "QUOTE" = false ∧
              (({ name := "NOT" } : Symbol)).isNamed "IF" = false ∧
              (({ name := "NOT" } : Symbol)).isNamed "LET" = false ∧
              (({ name := "NOT" } : Symbol)).isNamed "LET*" = false := by decide
  rw [evalOpt_builtin_1 f w env (({ name := "NOT" } : Symbol)) t tv h_ns h_not_def ht] at h_not
  -- h_not : some (callBuiltin "NOT" [tv]) = some SExpr.nil
  simp only [callBuiltin_not, Option.some.injEq] at h_not
  exact (Logic.not_nil_iff tv).mp h_not

/-! ## Layer 0 continued: Value-level Logic axioms (T8) -/

/-- CDR of CONS is the second argument. -/
theorem logic_cdr_cons (a b : SExpr) : Logic.cdr (.cons a b) = b := by
  simp [Logic.cdr]

/-- CAR of CONS is the first argument. -/
theorem logic_car_cons (a b : SExpr) : Logic.car (.cons a b) = a := by
  simp [Logic.car]

/-- EQUAL is reflexive. -/
theorem logic_equal_self (a : SExpr) : Logic.equal a a = SExpr.t :=
  Logic.equal_self a

/-- T8: Commutativity of plus. -/
theorem logic_plus_comm (a b : SExpr) : Logic.plus a b = Logic.plus b a := by
  simp only [Logic.plus]
  congr 1
  · omega
  · exact Nat.mul_comm _ _

/-- Plus of two integers is the integer sum (my-len/+ values are integers,
    so the proof can work at the integer level). -/
theorem logic_plus_int (a b : Int) :
    Logic.plus (.atom (.number (.int a))) (.atom (.number (.int b)))
    = .atom (.number (.int (a + b))) := by
  simp [Logic.plus, Logic.toRat, Logic.mkNumber]

/-- `(+ 0 k) = k` for an integer `k` (the unicity-of-0 fact specialized to the
    integer value `my-len` returns, via `type-prescription:my-len`). -/
theorem logic_plus_zero_int (k : Int) :
    Logic.plus (.atom (.number (.int 0))) (.atom (.number (.int k)))
    = .atom (.number (.int k)) := by
  rw [logic_plus_int, Int.zero_add]

/-! ### Unconditional rational arithmetic for `Logic.plus`

ACL2's `commutativity-of-+` and `commutativity-2-of-+` are UNCONDITIONAL rewrite
rules (`binary-+` coerces non-numbers via `fix`), so a faithful replay must hold
for all values — not just integers. We prove `Logic.plus` is associative
(hence comm-2) over arbitrary `SExpr`. Strategy: `mkNumber` is invariant under
scaling numerator+denominator (`mkNumber_scale`); composing with the reduced
form of `toRat (mkNumber ..)` (`toRat_mkNumber`) gives the *unreduced*
`plus (mkNumber n d) c` (`plus_mkNumber_left`), after which associativity is a
ring identity on numerators and a `Nat`-comm identity on denominators. -/

/-- `toRat` always yields a positive denominator (canonical `Number`: a
    ratio's denominator is ≥ 2 by the carried invariant). -/
theorem toRat_den_pos (s : SExpr) : 0 < (Logic.toRat s).2 := by
  unfold Logic.toRat
  split
  · exact Nat.one_pos
  · rename_i n d hc
    simp only [canonRat, Bool.and_eq_true, decide_eq_true_eq] at hc
    omega
  · exact Nat.one_pos

/-- `Logic.plus` in terms of the rational components (definitional). -/
theorem plus_eq (a c : SExpr) :
    Logic.plus a c = Logic.mkNumber
      ((Logic.toRat a).1 * ((Logic.toRat c).2 : Int) + (Logic.toRat c).1 * ((Logic.toRat a).2 : Int))
      ((Logic.toRat a).2 * (Logic.toRat c).2) := rfl

/-- The reduced form produced by `mkNumber` (positive denominator). -/
theorem toRat_mkNumber (n : Int) (d : Nat) (hd : 0 < d) :
    Logic.toRat (Logic.mkNumber n d)
      = (n / (Nat.gcd n.natAbs d : Int), d / Nat.gcd n.natAbs d) := by
  have hdg : 0 < d / Nat.gcd n.natAbs d :=
    Nat.div_pos (Nat.le_of_dvd hd (Nat.gcd_dvd_right _ _)) (Nat.gcd_pos_of_pos_right _ hd)
  simp only [Logic.mkNumber, Int.ofNat_eq_natCast, dif_neg (show ¬ d = 0 by omega)]
  by_cases h1 : d / Nat.gcd n.natAbs d = 1
  · simp [Logic.toRat, h1]
  · simp [Logic.toRat, h1]

/-- `mkNumber` is invariant under scaling numerator and denominator by `k > 0`. -/
theorem mkNumber_scale (n : Int) (d k : Nat) (hk : 0 < k) :
    Logic.mkNumber (n * (k : Int)) (d * k) = Logic.mkNumber n d := by
  by_cases hd : d = 0
  · subst hd; simp [Logic.mkNumber]
  · have hdk : ¬ (d * k = 0) := Nat.mul_ne_zero hd (by omega)
    have hnat : (n * (k : Int)).natAbs = n.natAbs * k := by rw [Int.natAbs_mul]; simp
    have hd2 : d * k / (Nat.gcd n.natAbs d * k) = d / Nat.gcd n.natAbs d :=
      Nat.mul_div_mul_right d (Nat.gcd n.natAbs d) hk
    have hn2 : n * (k : Int) / ((Nat.gcd n.natAbs d * k : Nat) : Int)
             = n / (Nat.gcd n.natAbs d : Int) := by
      push_cast
      exact Int.mul_ediv_mul_of_pos_left n _ (by exact_mod_cast hk)
    simp only [Logic.mkNumber, Int.ofNat_eq_natCast, dif_neg hd, dif_neg hdk, hnat,
               Nat.gcd_mul_right, hd2, hn2]

/-- The UNREDUCED form of `plus (mkNumber n d) c`: scaling collapses `mkNumber`'s
    internal gcd reduction, so the result is `mkNumber (n·cd + cn·d) (d·cd)` with
    `(cn, cd) = toRat c`. The key lemma for proving associativity. -/
theorem plus_mkNumber_left (n : Int) (d : Nat) (hd : 0 < d) (c : SExpr) :
    Logic.plus (Logic.mkNumber n d) c
      = Logic.mkNumber (n * ((Logic.toRat c).2 : Int) + (Logic.toRat c).1 * (d : Int))
                       (d * (Logic.toRat c).2) := by
  have hg : 0 < Nat.gcd n.natAbs d := Nat.gcd_pos_of_pos_right _ hd
  have hgn : (Nat.gcd n.natAbs d : Int) ∣ n := Int.ofNat_dvd_left.mpr (Nat.gcd_dvd_left _ _)
  have hgd : Nat.gcd n.natAbs d ∣ d := Nat.gcd_dvd_right _ _
  have hn : n / (Nat.gcd n.natAbs d : Int) * (Nat.gcd n.natAbs d : Int) = n :=
    Int.ediv_mul_cancel hgn
  have hdd : ((d / Nat.gcd n.natAbs d : Nat) : Int) * (Nat.gcd n.natAbs d : Int) = (d : Int) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hgd]
  rw [plus_eq, toRat_mkNumber n d hd]
  dsimp only
  rw [← mkNumber_scale
        (n / (Nat.gcd n.natAbs d : Int) * ((Logic.toRat c).2 : Int)
          + (Logic.toRat c).1 * ((d / Nat.gcd n.natAbs d : Nat) : Int))
        (d / Nat.gcd n.natAbs d * (Logic.toRat c).2) (Nat.gcd n.natAbs d) hg]
  congr 1
  · have hrw : (n / (Nat.gcd n.natAbs d : Int) * ((Logic.toRat c).2 : Int)
          + (Logic.toRat c).1 * ((d / Nat.gcd n.natAbs d : Nat) : Int)) * (Nat.gcd n.natAbs d : Int)
        = (n / (Nat.gcd n.natAbs d : Int) * (Nat.gcd n.natAbs d : Int)) * ((Logic.toRat c).2 : Int)
          + (Logic.toRat c).1 * (((d / Nat.gcd n.natAbs d : Nat) : Int) * (Nat.gcd n.natAbs d : Int)) := by
      ring
    rw [hrw, hn, hdd]
  · rw [Nat.mul_right_comm, Nat.div_mul_cancel hgd]

/-- Associativity of `Logic.plus` (unconditional). -/
theorem logic_plus_assoc (a b c : SExpr) :
    Logic.plus (Logic.plus a b) c = Logic.plus a (Logic.plus b c) := by
  have hab : 0 < (Logic.toRat a).2 * (Logic.toRat b).2 :=
    Nat.mul_pos (toRat_den_pos a) (toRat_den_pos b)
  have hbc : 0 < (Logic.toRat b).2 * (Logic.toRat c).2 :=
    Nat.mul_pos (toRat_den_pos b) (toRat_den_pos c)
  rw [plus_eq a b, plus_mkNumber_left _ _ hab, logic_plus_comm a (Logic.plus b c),
      plus_eq b c, plus_mkNumber_left _ _ hbc]
  congr 1
  · push_cast; ring
  · ring

/-- `commutativity-2-of-+` (unconditional): `(+ a (+ b c)) = (+ b (+ a c))`. -/
theorem logic_plus_comm2 (a b c : SExpr) :
    Logic.plus a (Logic.plus b c) = Logic.plus b (Logic.plus a c) := by
  rw [← logic_plus_assoc, ← logic_plus_assoc, logic_plus_comm a b]

/-! ## With-lemma replay combinators (driver dispatch entries)

  One schematic combinator per imported rewrite rule (rune). Each takes the
  rewrite-site terms and EXISTENTIAL convergence facts about their operands
  (totality / type-prescription — never a function's specific value), and
  returns the node's eval-equality, discharged by the rune's proven value-
  equality. The driver applies these to the terms; values stay opaque. There is
  deliberately NO computational inhabitant of these eval-equalities for symbolic
  terms — the rune's lemma is the only route. -/

/-- RUNE `cdr-cons`: `(cdr (cons a b)) ⇒ b`. -/
theorem re_cdr_cons (w : World) (env : Env) (a b av bv : SExpr)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some bv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "CDR" }))
        (.cons (.cons (.atom (.symbol { name := "CONS" })) (.cons a (.cons b .nil))) .nil))
      = evalOpt f w env b :=
  fuel_eq_of_conv
    (conv_builtin1 w env { name := "CDR" }
      (.cons (.atom (.symbol { name := "CONS" })) (.cons a (.cons b .nil)))
      (.cons av bv) bv (by decide) h_no_cdr
      (conv_builtin2 w env { name := "CONS" } a b av bv (.cons av bv) (by decide) h_no_cons ha hb rfl)
      (by rw [callBuiltin_cdr, logic_cdr_cons]))
    hb rfl

/-- RUNE `car-cons`: `(car (cons a b)) ⇒ a`. Operands existential. -/
theorem re_car_cons (w : World) (env : Env) (a b av bv : SExpr)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some bv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "CAR" }))
        (.cons (.cons (.atom (.symbol { name := "CONS" })) (.cons a (.cons b .nil))) .nil))
      = evalOpt f w env a :=
  fuel_eq_of_conv
    (conv_builtin1 w env { name := "CAR" }
      (.cons (.atom (.symbol { name := "CONS" })) (.cons a (.cons b .nil)))
      (.cons av bv) av (by decide) h_no_car
      (conv_builtin2 w env { name := "CONS" } a b av bv (.cons av bv) (by decide) h_no_cons ha hb rfl)
      (by rw [callBuiltin_car, logic_car_cons]))
    ha rfl

/-- RUNE `commutativity-of-+`: `(+ a b) ⇒ (+ b a)`. -/
theorem re_plus_comm (w : World) (env : Env) (a b av bv : SExpr)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some bv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "BINARY-+" })) (.cons a (.cons b .nil)))
      = evalOpt f w env (.cons (.atom (.symbol { name := "BINARY-+" })) (.cons b (.cons a .nil))) :=
  fuel_eq_of_conv
    (conv_builtin2 w env { name := "BINARY-+" } a b av bv (Logic.plus av bv)
      (by decide) h_no_plus ha hb (callBuiltin_plus _ _))
    (conv_builtin2 w env { name := "BINARY-+" } b a bv av (Logic.plus bv av)
      (by decide) h_no_plus hb ha (callBuiltin_plus _ _))
    (logic_plus_comm av bv)

/-- RUNE `commutativity-2-of-+`: `(+ a (+ b c)) ⇒ (+ b (+ a c))`. Unconditional —
    faithful to ACL2's `(defthm commutativity-2-of-+ …)`, which has no type
    hypothesis (`binary-+` coerces via `fix`). Operands converge to SOME value;
    the value-equality is `logic_plus_comm2`. -/
theorem re_plus_comm2 (w : World) (env : Env) (a b c : SExpr) (av bv cv : SExpr)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some bv)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some cv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "BINARY-+" }))
        (.cons a (.cons (.cons (.atom (.symbol { name := "BINARY-+" })) (.cons b (.cons c .nil))) .nil)))
      = evalOpt f w env (.cons (.atom (.symbol { name := "BINARY-+" }))
        (.cons b (.cons (.cons (.atom (.symbol { name := "BINARY-+" })) (.cons a (.cons c .nil))) .nil))) := by
  have hbc : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "BINARY-+" })) (.cons b (.cons c .nil)))
      = some (Logic.plus bv cv) :=
    conv_builtin2 w env { name := "BINARY-+" } b c _ _ _ (by decide) h_no_plus hb hc (callBuiltin_plus _ _)
  have hac : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "BINARY-+" })) (.cons a (.cons c .nil)))
      = some (Logic.plus av cv) :=
    conv_builtin2 w env { name := "BINARY-+" } a c _ _ _ (by decide) h_no_plus ha hc (callBuiltin_plus _ _)
  exact fuel_eq_of_conv
    (conv_builtin2 w env { name := "BINARY-+" } a _ _ _ _ (by decide) h_no_plus ha hbc (callBuiltin_plus _ _))
    (conv_builtin2 w env { name := "BINARY-+" } b _ _ _ _ (by decide) h_no_plus hb hac (callBuiltin_plus _ _))
    (logic_plus_comm2 av bv cv)

/-- RUNE `if-simplification` (true test): `(if c t e) ⇒ t` when the test converges
    to a truthy value. Term-to-term; the then-branch's value stays existential. -/
theorem re_if_true (w : World) (env : Env) (c t e cv tv : SExpr)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some cv) (hcv : Logic.toBool cv = true)
    (ht : ∃ N, ∀ f ≥ N, evalOpt f w env t = some tv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil))))
      = evalOpt f w env t :=
  fuel_eq_of_conv (conv_if_true w env c t e cv tv hc hcv ht) ht rfl

/-- RUNE `if-simplification` (false test): `(if c t e) ⇒ e` when the test
    converges to `nil`. Term-to-term; the else-branch's value stays existential. -/
theorem re_if_false (w : World) (env : Env) (c t e ev : SExpr)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some .nil)
    (he : ∃ N, ∀ f ≥ N, evalOpt f w env e = some ev) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil))))
      = evalOpt f w env e := by
  have hconv : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil)))) = some ev := by
    obtain ⟨Nc, hc'⟩ := hc; obtain ⟨Ne, he'⟩ := he
    refine ⟨max Nc Ne + 1, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [evalOpt_if_false g w env c t e (hc' g (by omega))]
    exact he' g (by omega)
  exact fuel_eq_of_conv hconv he rfl

/-- `(bindArgs [s] [v]).get? s = some v`. -/
theorem bindArgs_single_get_self (s : Symbol) (v : SExpr) :
    (bindArgs [s] [v]).get? s = some v := by
  show (({} : Env).insert s v).get? s = some v
  simp

/-- `(bindArgs [f1,f2] [v1,v2]).get? f1 = some v1`. -/
theorem bindArgs_pair_get_fst (f1 f2 : Symbol) (v1 v2 : SExpr) :
    (bindArgs [f1, f2] [v1, v2]).get? f1 = some v1 := by
  show ((({} : Env).insert f2 v2).insert f1 v1).get? f1 = some v1
  simp

/-- `(bindArgs [f1,f2] [v1,v2]).get? f2 = some v2` (distinct formals). -/
theorem bindArgs_pair_get_snd (f1 f2 : Symbol) (v1 v2 : SExpr) (hne : f1 ≠ f2) :
    (bindArgs [f1, f2] [v1, v2]).get? f2 = some v2 := by
  show ((({} : Env).insert f2 v2).insert f1 v1).get? f2 = some v2
  simp only [Env.get?_insert, beq_iff_eq]
  rw [if_neg (Ne.symm hne)]
  simp

/-- RUNE `:DEFINITION fn` on a VARIABLE argument: `(fn x) ⇒ body` (the formal is
    the call's variable, so the substitution is the identity). Term-to-term; the
    body's value `v` stays existential (totality). -/
theorem re_unfold1_var (w : World) (env : Env) (fn formal : Symbol) (av body v : SExpr)
    (hns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
           fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (hdef : w.defs.get? fn = some ([formal], body))
    (hclosed : ∀ s ∈ freeVars body, s = formal) (hws : WellScoped body = true)
    (hbind : ∀ f, evalOpt (f + 1) w env (.atom (.symbol formal)) = some av)
    (hbody : ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [formal] [av]) body = some v) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol fn)) (.cons (.atom (.symbol formal)) .nil))
      = evalOpt f w env body := by
  refine fuel_eq_of_conv
    (conv_defn_1 w env fn (.atom (.symbol formal)) av formal body v hns hdef
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact hbind g⟩ hbody)
    ?_ rfl
  obtain ⟨Nb, hb⟩ := hbody
  refine ⟨Nb, fun f hf => ?_⟩
  rw [evalOpt_freevar_congr w f env (bindArgs [formal] [av]) body hws (fun s hs => ?_)]
  · exact hb f hf
  · rw [hclosed s hs]
    exact (hbind 0).trans (evalOpt_var 0 w _ formal av (bindArgs_single_get_self formal av)).symm

/-- RUNE `:DEFINITION fn` on two VARIABLE arguments: `(fn x y) ⇒ body`. -/
theorem re_unfold2_var (w : World) (env : Env) (fn f1 f2 : Symbol) (av1 av2 body v : SExpr)
    (hne : f1 ≠ f2)
    (hns : fn.isNamed "QUOTE" = false ∧ fn.isNamed "IF" = false ∧
           fn.isNamed "LET" = false ∧ fn.isNamed "LET*" = false)
    (hdef : w.defs.get? fn = some ([f1, f2], body))
    (hclosed : ∀ s ∈ freeVars body, s = f1 ∨ s = f2) (hws : WellScoped body = true)
    (hbind1 : ∀ f, evalOpt (f + 1) w env (.atom (.symbol f1)) = some av1)
    (hbind2 : ∀ f, evalOpt (f + 1) w env (.atom (.symbol f2)) = some av2)
    (hbody : ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [f1, f2] [av1, av2]) body = some v) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol fn))
        (.cons (.atom (.symbol f1)) (.cons (.atom (.symbol f2)) .nil)))
      = evalOpt f w env body := by
  refine fuel_eq_of_conv
    (conv_defn_2 w env fn (.atom (.symbol f1)) (.atom (.symbol f2)) av1 av2 f1 f2 body v hns hdef
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact hbind1 g⟩
      ⟨1, fun f hf => by obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; exact hbind2 g⟩ hbody)
    ?_ rfl
  obtain ⟨Nb, hb⟩ := hbody
  refine ⟨Nb, fun f hf => ?_⟩
  rw [evalOpt_freevar_congr w f env (bindArgs [f1, f2] [av1, av2]) body hws (fun s hs => ?_)]
  · exact hb f hf
  · rcases hclosed s hs with h | h
    · rw [h]; exact (hbind1 0).trans
        (evalOpt_var 0 w _ f1 av1 (bindArgs_pair_get_fst f1 f2 av1 av2)).symm
    · rw [h]; exact (hbind2 0).trans
        (evalOpt_var 0 w _ f2 av2 (bindArgs_pair_get_snd f1 f2 av1 av2 hne)).symm

/-! ## Induction principles (T10) -/

/-- T10: Induction on consp/cdr structure (matching my-app's recursion).
    If P holds when consp(v) is nil, and P(cdr(v)) implies P(v) when consp(v) is non-nil,
    then P holds for all v. Proved by well-founded induction on consCount. -/
theorem acl2_induction_consp (P : SExpr → Prop)
    (base : ∀ v, Logic.consp v = .nil → P v)
    (step : ∀ v, Logic.consp v ≠ .nil → P (Logic.cdr v) → P v) :
    ∀ v, P v := by
  intro v
  -- Strong induction on consCount v
  have : ∀ n, ∀ v, v.consCount ≤ n → P v := by
    intro n
    induction n with
    | zero =>
      intro v hv
      -- consCount v ≤ 0 means v is nil or atom (not cons)
      apply base
      match v with
      | .nil => rfl
      | .atom _ => rfl
      | .cons a d => simp [SExpr.consCount] at hv
    | succ n ih =>
      intro v hv
      by_cases hc : Logic.consp v = .nil
      · exact base v hc
      · apply step v hc
        apply ih
        -- Need: consCount (Logic.cdr v) ≤ n
        match v, hc with
        | .cons a d, _ =>
          simp [Logic.cdr, SExpr.consCount] at hv ⊢
          omega
  exact this v.consCount v (Nat.le_refl _)

/-- G5/v2: STRONG induction on `consCount` — the general principle for
    multi-case schemes. The case dispatch (the emitted decision tree) and the
    per-IH measure decrease (Count lemmas under the in-scope ruling tests)
    happen inside `step`, mirroring ACL2's induction machine, instead of
    being baked into a fixed-shape lemma like `acl2_induction_consp`. -/
theorem acl2_strong_induction_count (P : SExpr → Prop)
    (step : ∀ v, (∀ u, u.consCount < v.consCount → P u) → P v) : ∀ v, P v := by
  intro v
  have : ∀ n, ∀ v, v.consCount ≤ n → P v := by
    intro n
    induction n with
    | zero =>
      intro v hv
      exact step v (fun u hu => absurd (Nat.lt_of_lt_of_le hu hv) (Nat.not_lt_zero _))
    | succ n ih =>
      intro v hv
      exact step v (fun u hu => ih u (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hu hv)))
  exact this v.consCount v (Nat.le_refl _)

/-- G5/v2: case-split on a CONVERGENT test term's value — nil or truthy. The
    env-level dispatch step of the emitted decision tree: each ruling test
    must converge (primitive walk or totality-from-admission), then the goal
    splits classically on its value. -/
theorem conv_value_split {w : World} {env : Env} {t : SExpr} {motive : Prop}
    (hconv : ∃ N v, ∀ f ≥ N, evalOpt f w env t = some v)
    (hnil : (∃ N, ∀ f ≥ N, evalOpt f w env t = some SExpr.nil) → motive)
    (htruthy : ∀ v, v ≠ SExpr.nil → (∃ N, ∀ f ≥ N, evalOpt f w env t = some v) →
      motive) : motive := by
  obtain ⟨N, v, hv⟩ := hconv
  by_cases h : v = SExpr.nil
  · exact hnil ⟨N, fun f hf => h ▸ hv f hf⟩
  · exact htruthy v h ⟨N, hv⟩

/-! ## Driver combinators for terminal nodes (fuel-existential form)

These package a terminal rune as the `∃N∀f≥N` fact the driver emits, so `replayNode`
just applies the combinator (no inline fuel plumbing). Kernel-checked once here. -/

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

/-- WELL-FOUNDED (strong) induction on `consCount` — the spine of
    admission-derived totality proofs (#37). The driver instantiates the
    motive `P av := the function converges at argument VALUE av`; the
    inductive hypothesis covers every value of strictly smaller `consCount`,
    and the admission's emitted decrease obligations justify applying it at
    each recursive call's argument value. -/
theorem consCount_strong_induction (P : SExpr → Prop)
    (step : ∀ x, (∀ y, y.consCount < x.consCount → P y) → P x) : ∀ x, P x := by
  intro x
  generalize h : x.consCount = n
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih => exact step x (fun y hy => ih y.consCount (h ▸ hy) y rfl)

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
    variable-convergence fact the mirror theorem's `∀ env` quantification needs. -/
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

/-! ## The R-parameterized rewrite judgment (G1, binding invariant L2)

ACL2's rewriter is generic over equivalence relations (geneqv); the preprocess
chain runs under IFF, so its `(if X 't 'nil) ⇒ X` simplifications are
iff-only, not value-preserving. `EvRel R` is the rewrite judgment over an
ABSTRACT value relation — `Eq` (the convergent eval-equality) and `SIff`
(ACL2's iff) are the first two instances; user equivalence relations land as
further instances with congruence lemmas indexed by
(function, position, R-in, R-out), mirroring ACL2's congruence runes. Note
the COLLAPSE rows of that table: an iff-related test or `not` argument makes
the surrounding term eval-EQUAL (the lazy `if` consults only `toBool`). -/

/-- Value-level truthiness equivalence — ACL2's `iff` on values. -/
def SIff (u v : SExpr) : Prop := (u = SExpr.nil) ↔ (v = SExpr.nil)

theorem siff_refl (u : SExpr) : SIff u u := Iff.rfl

theorem siff_trans {u v x : SExpr} (h1 : SIff u v) (h2 : SIff v x) : SIff u x :=
  Iff.trans h1 h2

/-- The R-parameterized rewrite judgment: both sides CONVERGE, values
    R-related. `EvRel Eq` strengthens the bare eval-equality chain form by
    convergence (every replay step is convergence-backed anyway). -/
def EvRel (R : SExpr → SExpr → Prop) (w : World) (env : Env) (a b : SExpr) : Prop :=
  ∃ N, ∀ f ≥ N, ∃ u v,
    evalOpt f w env a = some u ∧ evalOpt f w env b = some v ∧ R u v

theorem evrel_trans {R : SExpr → SExpr → Prop}
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    {w : World} {env : Env} {a b c : SExpr}
    (h1 : EvRel R w env a b) (h2 : EvRel R w env b c) : EvRel R w env a c := by
  obtain ⟨n1, h1⟩ := h1; obtain ⟨n2, h2⟩ := h2
  refine ⟨n1 + n2, fun f hf => ?_⟩
  obtain ⟨u, v, hau, hbv, huv⟩ := h1 f (by omega)
  obtain ⟨v', x, hbv', hcx, hvx⟩ := h2 f (by omega)
  have hvv' : v = v' := Option.some.inj (hbv.symm.trans hbv')
  exact ⟨u, x, hau, hcx, htrans huv (by rw [hvv']; exact hvx)⟩

/-- A (convergent) eval-equality chain is an `EvRel R` for reflexive R —
    the injection of today's equal-steps into an iff composite. -/
theorem evrel_of_fuel_eq {R : SExpr → SExpr → Prop} (hrefl : ∀ x, R x x)
    {w : World} {env : Env} {a b v : SExpr}
    (hab : ∃ N, ∀ f ≥ N, evalOpt f w env a = evalOpt f w env b)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some v) : EvRel R w env a b := by
  obtain ⟨n1, h1⟩ := hab; obtain ⟨n2, h2⟩ := hb
  refine ⟨n1 + n2, fun f hf => ?_⟩
  exact ⟨v, v, (h1 f (by omega)).trans (h2 f (by omega)), h2 f (by omega), hrefl v⟩

/-- The `PREPROCESS/IF-IFF` node: `(if A 't 'nil) ⇒ A` under IFF. The lhs's
    value is `t`/`nil` by A's truthiness — iff-related to A's own value but
    NOT equal to it (A may be truthy-non-t). -/
theorem evrel_siff_if_t_nil (w : World) (env : Env) (A vA : SExpr)
    (hA : ∃ N, ∀ f ≥ N, evalOpt f w env A = some vA) :
    EvRel SIff w env
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons A (.cons
          (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))
          (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
            .nil)))) A := by
  obtain ⟨N, hA⟩ := hA
  refine ⟨N + 2, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hAg := hA g (by omega)
  by_cases hv : vA = SExpr.nil
  · refine ⟨SExpr.nil, vA, ?_, hA (g + 1) (by omega), by simp [SIff, hv]⟩
    rw [evalOpt_if_false g w env A _ _ (by rw [hAg, hv])]
    obtain ⟨g2, rfl⟩ : ∃ g2, g = g2 + 1 := ⟨g - 1, by omega⟩
    simp [evalOpt, evalOptStep, Symbol.isNamed]
  · refine ⟨SExpr.t, vA, ?_, hA (g + 1) (by omega), by simp [SIff, hv, SExpr.t]⟩
    rw [evalOpt_if_true g w env A _ _ vA hAg (toBool_true_of_ne_nil hv)]
    obtain ⟨g2, rfl⟩ : ∃ g2, g = g2 + 1 := ⟨g - 1, by omega⟩
    simp [evalOpt, evalOptStep, Symbol.isNamed]

/-- Congruence (if, THEN-position, R-in → R-out = R): needs the test's and the
    OTHER branch's convergence (the untaken branch's value relates by
    reflexivity). Works uniformly for every reflexive R — one lemma serves the
    whole table column. -/
theorem evrel_if_then_congr {R : SExpr → SExpr → Prop} (hrefl : ∀ x, R x x)
    {w : World} {env : Env} {c thn thn' els vc vEls : SExpr}
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some vc)
    (hels : ∃ N, ∀ f ≥ N, evalOpt f w env els = some vEls)
    (hthn : EvRel R w env thn thn') :
    EvRel R w env
      (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons thn (.cons els .nil))))
      (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons thn' (.cons els .nil)))) := by
  obtain ⟨n1, hc⟩ := hc; obtain ⟨n2, hels⟩ := hels; obtain ⟨n3, hthn⟩ := hthn
  refine ⟨n1 + n2 + n3 + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hcg := hc g (by omega)
  by_cases hv : vc = SExpr.nil
  · refine ⟨vEls, vEls, ?_, ?_, hrefl vEls⟩
    · rw [evalOpt_if_false g w env c thn els (by rw [hcg, hv])]
      exact hels g (by omega)
    · rw [evalOpt_if_false g w env c thn' els (by rw [hcg, hv])]
      exact hels g (by omega)
  · obtain ⟨u, v, hu, hv', huv⟩ := hthn g (by omega)
    refine ⟨u, v, ?_, ?_, huv⟩
    · rw [evalOpt_if_true g w env c thn els vc hcg (toBool_true_of_ne_nil hv)]
      exact hu
    · rw [evalOpt_if_true g w env c thn' els vc hcg (toBool_true_of_ne_nil hv)]
      exact hv'

/-- Congruence (if, ELSE-position, R-in → R-out = R). -/
theorem evrel_if_else_congr {R : SExpr → SExpr → Prop} (hrefl : ∀ x, R x x)
    {w : World} {env : Env} {c thn els els' vc vThn : SExpr}
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some vc)
    (hthn : ∃ N, ∀ f ≥ N, evalOpt f w env thn = some vThn)
    (hels : EvRel R w env els els') :
    EvRel R w env
      (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons thn (.cons els .nil))))
      (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons thn (.cons els' .nil)))) := by
  obtain ⟨n1, hc⟩ := hc; obtain ⟨n2, hthn⟩ := hthn; obtain ⟨n3, hels⟩ := hels
  refine ⟨n1 + n2 + n3 + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hcg := hc g (by omega)
  by_cases hv : vc = SExpr.nil
  · obtain ⟨u, v, hu, hv', huv⟩ := hels g (by omega)
    refine ⟨u, v, ?_, ?_, huv⟩
    · rw [evalOpt_if_false g w env c thn els (by rw [hcg, hv])]; exact hu
    · rw [evalOpt_if_false g w env c thn els' (by rw [hcg, hv])]; exact hv'
  · refine ⟨vThn, vThn, ?_, ?_, hrefl vThn⟩
    · rw [evalOpt_if_true g w env c thn els vc hcg (toBool_true_of_ne_nil hv)]
      exact hthn g (by omega)
    · rw [evalOpt_if_true g w env c thn els' vc hcg (toBool_true_of_ne_nil hv)]
      exact hthn g (by omega)

/-- COLLAPSE row (if, TEST-position, SIff-in → Eq-out): iff-related tests make
    the surrounding ifs eval-EQUAL — the lazy `if` consults only `toBool`. -/
theorem evrel_if_test_siff_collapse {w : World} {env : Env} {c c' thn els : SExpr}
    (hcc' : EvRel SIff w env c c') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons thn (.cons els .nil))))
      = evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" })) (.cons c' (.cons thn (.cons els .nil)))) := by
  obtain ⟨n1, hcc'⟩ := hcc'
  refine ⟨n1 + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  obtain ⟨u, v, hu, hv, huv⟩ := hcc' g (by omega)
  by_cases hnu : u = SExpr.nil
  · rw [evalOpt_if_false g w env c thn els (by rw [hu, hnu]),
        evalOpt_if_false g w env c' thn els (by rw [hv, Iff.mp huv hnu])]
  · rw [evalOpt_if_true g w env c thn els u hu (toBool_true_of_ne_nil hnu),
        evalOpt_if_true g w env c' thn els v hv
          (toBool_true_of_ne_nil (fun hnv => hnu (Iff.mpr huv hnv)))]

/-- MODUS PONENS at the value level: a truthy `Logic.implies` with a truthy
    antecedent has a truthy consequent (the rule:<thm> discharge's
    hypothesis-consumption step). -/
theorem implies_value_mp {vA vB : SExpr}
    (h : Logic.implies vA vB ≠ SExpr.nil) (hvA : vA ≠ SExpr.nil) :
    vB ≠ SExpr.nil := by
  rw [logic_implies_cond] at h
  rw [toBool_true_of_ne_nil hvA] at h
  intro hB
  rw [hB] at h
  simp [Logic.toBool] at h

/-- An `and`-antecedent's value (`(if A B 'nil)` lifted) is truthy when both
    parts are (the two-hypothesis rule antecedent). -/
theorem and_value_ne_nil {vA vB : SExpr}
    (hvA : vA ≠ SExpr.nil) (hvB : vB ≠ SExpr.nil) :
    cond (Logic.toBool vA) vB SExpr.nil ≠ SExpr.nil := by
  rw [toBool_true_of_ne_nil hvA]
  exact hvB

/-- `Logic.implies` is boolean-valued (the chain-start head fact). -/
theorem logic_implies_boolean (p q : SExpr) :
    Logic.implies p q = SExpr.t ∨ Logic.implies p q = SExpr.nil := by
  rw [logic_implies_cond]
  cases Logic.toBool p <;> cases Logic.toBool q <;> simp

/-! ## The truthiness judgment `EvTrue` (G2)

ACL2's notion of clause/theorem truth is *the term is non-nil*; the exact-t
form is strictly stronger (they coincide only on boolean-valued terms, and
the exact-t mirror is false-as-stated for non-boolean formulas). G2 states
the CLAUSE and MIRROR judgments as `EvTrue`; exact-t facts survive at the
VALUE level and inject at the clause boundary (`evtrue_of_eq_t`). The
quantifier shape matches `EvRel` (∃N∀f∃v), so the G1 iff layer transports
`EvTrue` directly (`evtrue_of_evrel_siff`) with no boolean-valuedness side
condition. Design + decision log:
`docs/plans/2026-06-11_g2-evtrue-migration.md`. -/

/-- ACL2's clause/theorem truth: the term eventually converges to a NON-NIL
    value. -/
def EvTrue (w : World) (env : Env) (t : SExpr) : Prop :=
  ∃ N, ∀ f ≥ N, ∃ v, evalOpt f w env t = some v ∧ v ≠ SExpr.nil

/-- Exact-t injection at the clause boundary: a value-pinned `= some t` fact
    IS truthiness. Every existing exact-t producer enters the `EvTrue` layer
    through this single lemma. -/
theorem evtrue_of_eq_t {w : World} {env : Env} {a : SExpr}
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env a = some SExpr.t) : EvTrue w env a := by
  obtain ⟨N, h⟩ := h
  exact ⟨N, fun f hf => ⟨SExpr.t, h f hf, by simp [SExpr.t]⟩⟩

/-- Transport `EvTrue` BACKWARDS along an iff chain: `a` iff-rewrites to `b`
    and `b` is true, so `a` is true. Replaces the deleted G1-interim
    end-game (backward truth transport + the boolean-head strengthening) —
    truthiness is the statement now, so no strengthening is needed. -/
theorem evtrue_of_evrel_siff {w : World} {env : Env} {a b : SExpr}
    (hab : EvRel SIff w env a b) (hb : EvTrue w env b) : EvTrue w env a := by
  obtain ⟨n1, hab⟩ := hab; obtain ⟨n2, hb⟩ := hb
  refine ⟨n1 + n2, fun f hf => ?_⟩
  obtain ⟨u, v, hau, hbv, huv⟩ := hab f (by omega)
  obtain ⟨v', hbv', hnv'⟩ := hb f (by omega)
  have : v = v' := Option.some.inj (hbv.symm.trans hbv')
  exact ⟨u, hau, fun hnu => hnv' (this ▸ Iff.mp huv hnu)⟩

/-- A pinned value under `EvTrue` is non-nil (the last-literal leaf fact:
    the clause fact + the literal's value characterization give `.truthy`
    uniformly — `.exactT` is gone, D9). -/
theorem ne_nil_of_evtrue_conv {w : World} {env : Env} {a va : SExpr}
    (ht : EvTrue w env a)
    (hconv : ∃ N, ∀ f ≥ N, evalOpt f w env a = some va) : va ≠ SExpr.nil := by
  obtain ⟨n1, ht⟩ := ht; obtain ⟨n2, hconv⟩ := hconv
  obtain ⟨v, hav, hnv⟩ := ht (n1 + n2) (by omega)
  have : v = va := Option.some.inj (hav.symm.trans (hconv (n1 + n2) (by omega)))
  exact this ▸ hnv

/-- A TRUE term is iff-equivalent to `'t` (D10): the honest chain-step form
    of a verdict-only discharge node — `EvTrue lhs` composes in the SIff lane
    instead of being strengthened to an eval-equality with `'t` (which held
    only for boolean-valued clauses). -/
theorem evrel_siff_qt_of_evtrue {w : World} {env : Env} {a : SExpr}
    (ha : EvTrue w env a) :
    EvRel SIff w env a
      (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil)) := by
  obtain ⟨N, ha⟩ := ha
  refine ⟨N + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  obtain ⟨u, hau, hnu⟩ := ha (g + 1) (by omega)
  refine ⟨u, SExpr.t, hau, ?_, by simp [SIff, hnu, SExpr.t]⟩
  exact evalOpt_quote g w env SExpr.t

/-- Extract the REST of a disjunction from its `EvTrue` when the head literal
    is valued nil — the induction scaffold's per-case peel, fixed to the
    disjoin shape `(if c 't rest)`. -/
theorem evtrue_extract_else {w : World} {env : Env} {c rest : SExpr}
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some SExpr.nil)
    (hif : EvTrue w env
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons c (.cons
          (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))
          (.cons rest .nil))))) : EvTrue w env rest := by
  obtain ⟨n1, hc⟩ := hc; obtain ⟨n2, hif⟩ := hif
  refine ⟨n1 + n2 + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  obtain ⟨v, hifv, hnv⟩ := hif (g + 1) (by omega)
  rw [evalOpt_if_false g w env c _ rest (hc g (by omega))] at hifv
  exact ⟨v, evalOpt_fuel_mono g w env rest v hifv, hnv⟩

/-- A TRUE term's negation converges to nil (the step case's IH literal:
    `EvTrue ihInst` pins `(not ihInst) ⇒ nil` WITHOUT pinning the IH's own
    value — `Logic.not v = nil` for every non-nil `v`). -/
theorem conv_not_nil_of_evtrue {w : World} {env : Env} {X : SExpr}
    (h_noshadow : w.defs.get? { name := "NOT" } = none)
    (hX : EvTrue w env X) :
    ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "NOT" })) (.cons X .nil))
      = some SExpr.nil := by
  obtain ⟨N, hX⟩ := hX
  refine ⟨N + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  obtain ⟨v, hv, hnv⟩ := hX g (by omega)
  rw [evalOpt_builtin_1 g w env { name := "NOT" } X v
    (by simp [Symbol.isNamed]) h_noshadow hv]
  rw [callBuiltin_not, not_nil_of_truthy hnv]

/-- The DUAL of `conv_not_nil_of_evtrue`: a nil argument makes `(not X)`
    converge to `t` (the multi-clause bridge's neg-leaf converter). -/
theorem conv_not_t_of_conv_nil {w : World} {env : Env} {X : SExpr}
    (h_noshadow : w.defs.get? { name := "NOT" } = none)
    (hX : ∃ N, ∀ f ≥ N, evalOpt f w env X = some SExpr.nil) :
    ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "NOT" })) (.cons X .nil))
      = some SExpr.t := by
  obtain ⟨N, hX⟩ := hX
  refine ⟨N + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [evalOpt_builtin_1 g w env { name := "NOT" } X SExpr.nil
    (by simp [Symbol.isNamed]) h_noshadow (hX g (by omega))]
  rw [callBuiltin_not]
  rfl

/-- Transport `EvTrue` backwards along an EVAL-EQUALITY chain (the
    equal-steps composition entering the truthiness judgment). The two sides
    may sit at DIFFERENT envs — the IH bridge's `evalOpt_substTerm_subst1`
    relates the goal env to the IH-instantiation env. -/
theorem evtrue_of_fuel_eq {w : World} {env env' : Env} {a b : SExpr}
    (hab : ∃ N, ∀ f ≥ N, evalOpt f w env a = evalOpt f w env' b)
    (hb : EvTrue w env' b) : EvTrue w env a := by
  obtain ⟨n1, hab⟩ := hab; obtain ⟨n2, hb⟩ := hb
  refine ⟨n1 + n2, fun f hf => ?_⟩
  obtain ⟨v, hbv, hnv⟩ := hb f (by omega)
  exact ⟨v, (hab f (by omega)).trans hbv, hnv⟩

/-- Drop a FALSIFIED leading disjunct: `EvTrue (IF c 'T r)` with the test
    converging to nil is `EvTrue r` (the generalize type-restriction
    head-drop — msort arc, 2026-07-19). -/
theorem evtrue_tail_of_if_head_nil {w : World} {env : Env} {c t r : SExpr}
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some SExpr.nil)
    (h : EvTrue w env (.cons (.atom (.symbol { name := "IF" }))
          (.cons c (.cons t (.cons r .nil))))) : EvTrue w env r := by
  obtain ⟨Nc, hc⟩ := hc
  obtain ⟨Nh, hh⟩ := h
  refine ⟨Nc + Nh, fun f hf => ?_⟩
  obtain ⟨v, hv, hnv⟩ := hh (f + 1) (by omega)
  rw [evalOpt_if_false f w env c t r (hc f (by omega))] at hv
  exact ⟨v, hv, hnv⟩

/-- `not` of an exact-t value is nil (restriction-literal falsification). -/
theorem not_of_eq_t {x : SExpr} (h : x = SExpr.t) :
    Logic.not x = SExpr.nil := by subst h; rfl

/-- The converse: a pinned non-nil value IS `EvTrue` (the positive-literal
    fallback of the clausify walk — truthiness anywhere in the spine, D9). -/
theorem evtrue_of_conv_ne_nil {w : World} {env : Env} {a va : SExpr}
    (hconv : ∃ N, ∀ f ≥ N, evalOpt f w env a = some va)
    (hne : va ≠ SExpr.nil) : EvTrue w env a := by
  obtain ⟨N, hconv⟩ := hconv
  exact ⟨N, fun f hf => ⟨va, hconv f hf, hne⟩⟩

/-- The `EvTrue` spine combinator (D9): VALUE-characterized convergence of the
    test and truth of the branch selected by EITHER case of `cv` (both
    implications supplied; the proof case-splits on `cv = nil`). One lemma
    serves `replayClauseSpine`, the clausify-bridge positive walk, and the
    discharge spine; an exact-t branch enters via `evtrue_of_eq_t`. -/
theorem evtrue_dp_if_split (w : World) (env : Env) (c t e cv : SExpr)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some cv)
    (hthen : cv ≠ .nil → EvTrue w env t)
    (helse : cv = .nil → EvTrue w env e) :
    EvTrue w env
      (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil)))) := by
  obtain ⟨Nc, hc⟩ := hc
  by_cases hcv : cv = .nil
  · obtain ⟨Ne, he⟩ := helse hcv
    refine ⟨max Nc Ne + 1, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨v, hev, hnv⟩ := he g (by omega)
    exact ⟨v, by
      rw [evalOpt_if_false g w env c t e (hcv ▸ hc g (by omega))]; exact hev, hnv⟩
  · obtain ⟨Nt, ht⟩ := hthen hcv
    refine ⟨max Nc Nt + 1, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨v, htv, hnv⟩ := ht g (by omega)
    exact ⟨v, by
      rw [evalOpt_if_true g w env c t e cv (hc g (by omega))
        (toBool_true_of_ne_nil hcv)]; exact htv, hnv⟩

/-- Extract `integerp v = t` from a TRUE type-prescription corollary of the
    standard `(IF (INTEGERP v) … 'NIL)` shape (lifted: `cond (toBool (integerp v))
    X nil = t`): the recognizer is two-valued, and a false test would make the
    cond `nil ≠ t`. -/
theorem tp_cond_integerp_t (v X : SExpr)
    (h : cond (Logic.toBool (Logic.integerp v)) X SExpr.nil = SExpr.t) :
    Logic.integerp v = SExpr.t := by
  match v with
  | .atom (.number (.int _)) => rfl
  | .atom (.number (.rational _ _ _)) => simp [Logic.integerp, Logic.toBool, SExpr.t] at h
  | .atom (.symbol _) => simp [Logic.integerp, Logic.toBool, SExpr.t] at h
  | .atom (.keyword _) => simp [Logic.integerp, Logic.toBool, SExpr.t] at h
  | .atom (.char _) => simp [Logic.integerp, Logic.toBool, SExpr.t] at h
  | .atom (.string _) => simp [Logic.integerp, Logic.toBool, SExpr.t] at h
  | .nil => simp [Logic.integerp, Logic.toBool, SExpr.t] at h
  | .cons _ _ => simp [Logic.integerp, Logic.toBool, SExpr.t] at h

/-- A variable's value at an `insert`-updated env (the IH instantiation env). -/
theorem re_val_var_insert (w : World) (env : Env) (s : Symbol) (v : SExpr) :
    ∃ N, ∀ f ≥ N, evalOpt f w (env.insert s v) (.atom (.symbol s)) = some v :=
  ⟨1, fun f hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact evalOpt_var g w _ s v (by simp)⟩

/-- Two value characterizations across an eval-equality pin the SAME value (the
    spine's bridge from a literal's pre-rewrite falsity to its post-rewrite form). -/
theorem val_eq_of_eval_eq {a b : Nat → Option SExpr} {u v : SExpr}
    (hab : ∃ N, ∀ f ≥ N, a f = b f)
    (ha : ∃ N, ∀ f ≥ N, a f = some u) (hb : ∃ N, ∀ f ≥ N, b f = some v) : u = v := by
  obtain ⟨n1, h1⟩ := hab; obtain ⟨n2, h2⟩ := ha; obtain ⟨n3, h3⟩ := hb
  have := ((h2 (n1+n2+n3) (by omega)).symm.trans (h1 (n1+n2+n3) (by omega))).trans
    (h3 (n1+n2+n3) (by omega))
  exact Option.some.inj this

/-- Weaken a value-characterized convergence to the v-existential form
    (`proveConv`'s shape, consumed by `re_equal_self` etc.). -/
theorem conv_vfix_of_val {w : World} {env : Env} {a v : SExpr}
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env a = some v) :
    ∃ N, ∃ v', ∀ f ≥ N, evalOpt f w env a = some v' := by
  obtain ⟨N, h⟩ := h
  exact ⟨N, v, h⟩

/-- Extract the integer witness from a true `integerp` value fact (the TP bridge:
    the lifted type-prescription gives `Logic.integerp v = t`; recognizers like
    `acl2-numberp` need the int shape). -/
theorem logic_integerp_int (v : SExpr) (h : Logic.integerp v = SExpr.t) :
    ∃ k : Int, v = .atom (.number (.int k)) := by
  match v with
  | .atom (.number (.int k)) => exact ⟨k, rfl⟩
  | .atom (.number (.rational _ _ _)) => simp [Logic.integerp, SExpr.t] at h
  | .atom (.symbol _) => simp [Logic.integerp, SExpr.t] at h
  | .atom (.keyword _) => simp [Logic.integerp, SExpr.t] at h
  | .atom (.char _) => simp [Logic.integerp, SExpr.t] at h
  | .atom (.string _) => simp [Logic.integerp, SExpr.t] at h
  | .nil => simp [Logic.integerp, SExpr.t] at h
  | .cons _ _ => simp [Logic.integerp, SExpr.t] at h

/-- `rewrite-if`'s SWAPPED-P normalization (rewrite.lisp:17726-37):
    when the rewritten if-TEST has the negation shape `(IF c 'NIL 'T)`, ACL2
    strips it and SWAPS the branches before descending — unconditionally, and
    never recorded as a step (subsequent branch bkptrs simply refer to the
    swapped orientation). The chain walker applies this bridge
    deterministically when a path frame descends into such an if. -/
theorem re_if_neg_test_swap (w : World) (env : Env) (c a b : SExpr) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" }))
          (.cons (.cons (.atom (.symbol { name := "IF" }))
              (.cons c
                (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
                  (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                    (.cons SExpr.t .nil)) .nil))))
            (.cons a (.cons b .nil))))
      = evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons b (.cons a .nil)))) := by
  by_cases hconv : ∃ vc N, evalOpt N w env c = some vc
  · obtain ⟨vc, N, hN⟩ := hconv
    refine ⟨N + 3, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    obtain ⟨g'', rfl⟩ : ∃ g'', g' = g'' + 1 := ⟨g' - 1, by omega⟩
    have hc1 : evalOpt (g'' + 1) w env c = some vc :=
      evalOpt_ge_fuel N _ w env c vc hN (by omega)
    have hc2 : evalOpt (g'' + 2) w env c = some vc :=
      evalOpt_ge_fuel N _ w env c vc hN (by omega)
    by_cases hb : Logic.toBool vc = true
    · -- inner test truthy ⇒ inner if = 'NIL ⇒ outer takes b; RHS test truthy ⇒ b
      have hinner : evalOpt (g'' + 2) w env
          (.cons (.atom (.symbol { name := "IF" }))
            (.cons c
              (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
                (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                  (.cons SExpr.t .nil)) .nil)))) = some SExpr.nil := by

        rw [evalOpt_if_true (g'' + 1) w env c _ _ vc hc1 hb]
        exact evalOpt_quote g'' w env .nil
      rw [evalOpt_if_false (g'' + 2) w env _ a b hinner,
          evalOpt_if_true (g'' + 2) w env c b a vc hc2 hb]
    · have hvnil : vc = SExpr.nil := by
        cases vc <;> simp_all [Logic.toBool]
      subst hvnil
      -- inner test nil ⇒ inner if = 'T ⇒ outer takes a; RHS test nil ⇒ a
      have hinner : evalOpt (g'' + 2) w env
          (.cons (.atom (.symbol { name := "IF" }))
            (.cons c
              (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
                (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                  (.cons SExpr.t .nil)) .nil)))) = some SExpr.t := by
        rw [evalOpt_if_false (g'' + 1) w env c _ _ hc1]
        exact evalOpt_quote g'' w env SExpr.t
      rw [evalOpt_if_true (g'' + 2) w env _ a b SExpr.t hinner (by simp [Logic.toBool]),
          evalOpt_if_false (g'' + 2) w env c b a hc2]
  · -- `c` diverges at every fuel: both sides are `none`
    have hnone : ∀ M, evalOpt M w env c = none := by
      intro M
      rcases h : evalOpt M w env c with _ | vc
      · rfl
      · exact absurd ⟨vc, M, h⟩ hconv
    refine ⟨2, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    have hinner : evalOpt (g' + 1) w env
        (.cons (.atom (.symbol { name := "IF" }))
          (.cons c
            (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
              (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                (.cons SExpr.t .nil)) .nil)))) = none := by
      show evalOptStep (evalOpt g') w env _ = none
      unfold evalOptStep
      simp only [Symbol.isNamed, SExpr.toList?]
      show (evalOpt g' w env c).bind _ = none
      rw [hnone g']; rfl
    show evalOptStep (evalOpt (g' + 1)) w env _ = evalOptStep (evalOpt (g' + 1)) w env _
    unfold evalOptStep
    simp only [Symbol.isNamed, SExpr.toList?]
    show (evalOpt (g' + 1) w env _).bind _ = (evalOpt (g' + 1) w env c).bind _
    rw [hinner, hnone (g' + 1)]; rfl

/-- Arg-order symmetry of an EQUAL application: `Logic.equal` is symmetric and
    argument evaluation is jointly strict, so the whole application is
    orientation-independent. Bridges ACL2's `one-way-unify1` EQUAL special
    case — a rule whose lhs is `(EQUAL p q)` may match a target equality
    COMMUTED (the CAR-APPEND class). -/
theorem re_equal_comm (w : World) (env : Env) (a b : SExpr)
    (hno : w.defs.get? { name := "EQUAL" } = none) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil)))
      = evalOpt f w env
        (.cons (.atom (.symbol { name := "EQUAL" })) (.cons b (.cons a .nil))) := by
  by_cases ha : ∃ va N, evalOpt N w env a = some va
  · by_cases hb : ∃ vb N, evalOpt N w env b = some vb
    · obtain ⟨va, Na, hva⟩ := ha
      obtain ⟨vb, Nb, hvb⟩ := hb
      refine ⟨max Na Nb + 1, fun f hf => ?_⟩
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      have ha' : evalOpt g w env a = some va :=
        evalOpt_ge_fuel Na g w env a va hva (by omega)
      have hb' : evalOpt g w env b = some vb :=
        evalOpt_ge_fuel Nb g w env b vb hvb (by omega)
      rw [evalOpt_builtin_2 g w env _ a b va vb (by decide) hno ha' hb',
          evalOpt_builtin_2 g w env _ b a vb va (by decide) hno hb' ha',
          callBuiltin_equal, callBuiltin_equal, logic_equal_comm va vb]
    · -- b diverges: both sides are none (joint strictness)
      have hnone : ∀ M, evalOpt M w env b = none := by
        intro M
        rcases h : evalOpt M w env b with _ | vb
        · rfl
        · exact absurd ⟨vb, M, h⟩ hb
      refine ⟨1, fun f hf => ?_⟩
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      show evalOptStep (evalOpt g) w env _ = evalOptStep (evalOpt g) w env _
      unfold evalOptStep
      simp only [Symbol.isNamed, SExpr.toList?]
      simp [List.mapM, List.mapM.loop, hnone g]
  · -- a diverges: both sides are none (joint strictness)
    have hnone : ∀ M, evalOpt M w env a = none := by
      intro M
      rcases h : evalOpt M w env a with _ | va
      · rfl
      · exact absurd ⟨va, M, h⟩ ha
    refine ⟨1, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    show evalOptStep (evalOpt g) w env _ = evalOptStep (evalOpt g) w env _
    unfold evalOptStep
    simp only [Symbol.isNamed, SExpr.toList?]
    simp [List.mapM, List.mapM.loop, hnone g]

/-- Nat-valued twin of `Logic.len` — the DP leaf tactic's bridge from stuck
    `Logic.len` applications to omega-visible nonnegative integers (the
    `SExpr.consCount` pattern from the decrease prover). -/
def lenNat : SExpr → Nat
  | .cons _ b => lenNat b + 1
  | _ => 0

/-- `Logic.len` computes `lenNat` as an int atom. NOT `@[simp]` — consumed
    only by the DP leaf tactic's explicit simp set, so the driver's structural
    `Logic.len` values (the builtin TP pin route, `gz_def_len` unfolds) are
    untouched elsewhere. -/
theorem logic_len_eq_lenNat (x : SExpr) :
    Logic.len x = .atom (.number (.int (lenNat x))) := by
  induction x with
  | cons a b _ ihb =>
    have h : Logic.len (SExpr.cons a b)
        = .atom (.number (.int (Logic.toInt (Logic.len b) + 1))) := rfl
    rw [h, ihb]
    simp only [lenNat, Logic.toInt]
    congr 3
  | nil => simp [Logic.len, lenNat]
  | atom a => simp [Logic.len, lenNat]

/-- `Logic.len` is always an ACL2 integer — the kernel-checked counterpart of
    LEN's ground-zero `:TYPE-PRESCRIPTION` corollary
    `(IF (INTEGERP (LEN X)) (NOT (< (LEN X) '0)) 'NIL)`. The builtin TP pin
    route (`pinTermOpaques`) applies it ONLY after matching that emitted
    corollary shape, so the type fact is still consumed from ACL2's emission,
    with the proof supplied by the trusted core (LEN is a builtin —
    `Logic.len` IS its semantics here). -/
theorem logic_len_integerp (x : SExpr) : Logic.integerp (Logic.len x) = SExpr.t := by
  cases x with
  | cons a b => simp [Logic.len]
  | nil => simp [Logic.len]
  | atom a => simp [Logic.len]

/-- Value-characterized convergence of an `if` INSIDE a literal: the value is
    `cond (toBool cv) tv ev` (both branches must converge — their values are
    needed whichever way the test goes, since the DP fact reasons over all
    variable values). -/
theorem re_val_if (w : World) (env : Env) (c t e cv tv ev : SExpr)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some cv)
    (ht : ∃ N, ∀ f ≥ N, evalOpt f w env t = some tv)
    (he : ∃ N, ∀ f ≥ N, evalOpt f w env e = some ev) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil))))
      = some (cond (Logic.toBool cv) tv ev) := by
  obtain ⟨Nc, hc⟩ := hc; obtain ⟨Nt, ht⟩ := ht; obtain ⟨Ne, he⟩ := he
  refine ⟨max Nc (max Nt Ne) + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  by_cases hcv : Logic.toBool cv = true
  · rw [evalOpt_if_true g w env c t e cv (hc g (by omega)) hcv, ht g (by omega), hcv]
    rfl
  · have hnil : cv = .nil := by cases cv <;> simp_all [Logic.toBool]
    have htb : Logic.toBool cv = false := by simp [hnil, Logic.toBool]
    rw [evalOpt_if_false g w env c t e (hnil ▸ hc g (by omega)), he g (by omega), htb]
    rfl

/-- `if` convergence: all three parts converging makes the `if` converge (to the
    branch the test selects — existential, the analyzer doesn't need which). -/
theorem re_conv_if (w : World) (env : Env) (c t e : SExpr)
    (hc : ∃ N, ∃ cv, ∀ f ≥ N, evalOpt f w env c = some cv)
    (ht : ∃ N, ∃ tv, ∀ f ≥ N, evalOpt f w env t = some tv)
    (he : ∃ N, ∃ ev, ∀ f ≥ N, evalOpt f w env e = some ev) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil))))
      = some v := by
  obtain ⟨Nc, cv, hc⟩ := hc
  obtain ⟨Nt, tv, ht⟩ := ht
  obtain ⟨Ne, ev, he⟩ := he
  obtain ⟨N, h⟩ := re_val_if w env c t e cv tv ev ⟨Nc, hc⟩ ⟨Nt, ht⟩ ⟨Ne, he⟩
  exact ⟨N, cond (Logic.toBool cv) tv ev, h⟩

/-- The value identity behind rewrite-equal's built-in NIL normalization:
    `(equal nil v)` and `(if v nil t)` compute the same value. -/
theorem logic_equal_nil_eq_ite (v : SExpr) :
    Logic.equal .nil v = (bif Logic.toBool v then .nil else .t) := by
  cases v with
  | nil => rfl
  | atom a => simp [Logic.equal, Logic.toBool]
  | cons a b => simp [Logic.equal, Logic.toBool]

/-- `(if x 'nil 't)` converges to `(bif toBool vx then nil else t)` given `x`
    converges to `vx` — the value-characterized form of ACL2's `(not x)`. -/
theorem re_val_if_nil_t (w : World) (env : Env) (x vx : SExpr)
    (hx : ∃ N, ∀ f ≥ N, evalOpt f w env x = some vx) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "IF" }))
        (.cons x (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
          (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil)) .nil))))
      = some (bif Logic.toBool vx then .nil else .t) := by
  obtain ⟨N, hN⟩ := hx
  refine ⟨N + 2, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  by_cases hb : Logic.toBool vx = true
  · rw [evalOpt_if_true g w env _ _ _ vx (hN g (by omega)) hb, hb]
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    exact evalOpt_quote g' w env .nil
  · have hnil : vx = .nil := by
      cases vx with
      | nil => rfl
      | atom a => simp [Logic.toBool] at hb
      | cons a b => simp [Logic.toBool] at hb
    rw [evalOpt_if_false g w env _ _ _ (hnil ▸ hN g (by omega)),
        Bool.of_not_eq_true hb]
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    exact evalOpt_quote g' w env SExpr.t

/-- rewrite-equal's built-in NIL normalization, LEFT form (rewrite.lisp:18089,
    unconditional/syntactic): `(equal 'nil x) ≡ (if x 'nil 't)`, fuel-robust,
    given `x` converges and `equal` is unshadowed. -/
theorem re_equal_nil_norm_l (w : World) (env : Env) (x : SExpr)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (hxe : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env x = some v) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "EQUAL" }))
        (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
          (.cons x .nil)))
      = evalOpt f w env (.cons (.atom (.symbol { name := "IF" }))
        (.cons x (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
          (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil)) .nil)))) := by
  obtain ⟨N, vx, hN⟩ := hxe
  have hx : ∃ M, ∀ f ≥ M, evalOpt f w env x = some vx := ⟨N, hN⟩
  have hl := conv_builtin2 w env { name := "EQUAL" }
    (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil)) x
    .nil vx (Logic.equal .nil vx)
    (by simp [Symbol.isNamed]) h_no_equal (re_val_quote w env .nil) hx
    (callBuiltin_equal .nil vx)
  have hr := re_val_if_nil_t w env x vx hx
  exact fuel_eq_of_conv hl hr (logic_equal_nil_eq_ite vx)

/-- if-interp's call-stack fold `(equal (equal a b) 't) = (equal a b)`
    (rewrite.lisp:3791-3793) — sound because `Logic.equal` is two-valued. -/
theorem logic_equal_equal_t_r (a b : SExpr) :
    Logic.equal (Logic.equal a b) SExpr.t = Logic.equal a b := by
  by_cases h : (a == b) = true <;> simp [Logic.equal, h, SExpr.t]

/-- Mirrored: `(equal 't (equal a b)) = (equal a b)` (rewrite.lisp:3785-3789). -/
theorem logic_equal_equal_t_l (a b : SExpr) :
    Logic.equal SExpr.t (Logic.equal a b) = Logic.equal a b := by
  rw [logic_equal_comm]
  exact logic_equal_equal_t_r a b

/-- rewrite-equal's built-in EQUALITYP normalization (rewrite.lisp:18093,
    unconditional/syntactic): `(equal (equal a b) r) ≡
    (if (equal a b) (equal r 't) (if r 'nil 't))` — sound because
    `Logic.equal` is two-valued. Fuel-robust, given the parts converge. -/
theorem re_equal_equalityp_norm (w : World) (env : Env) (a b r : SExpr)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (hae : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env a = some v)
    (hbe : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env b = some v)
    (hre : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env r = some v) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "EQUAL" }))
        (.cons (.cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil)))
          (.cons r .nil)))
      = evalOpt f w env (.cons (.atom (.symbol { name := "IF" }))
        (.cons (.cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil)))
          (.cons (.cons (.atom (.symbol { name := "EQUAL" }))
              (.cons r (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                (.cons SExpr.t .nil)) .nil)))
            (.cons (.cons (.atom (.symbol { name := "IF" }))
              (.cons r (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
                (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))
                  .nil)))) .nil)))) := by
  obtain ⟨Na, va, hNa⟩ := hae
  obtain ⟨Nb, vb, hNb⟩ := hbe
  obtain ⟨Nr, vr, hNr⟩ := hre
  have hns : Symbol.isNamed { name := "EQUAL" } "QUOTE" = false ∧
             Symbol.isNamed { name := "EQUAL" } "IF" = false ∧
             Symbol.isNamed { name := "EQUAL" } "LET" = false ∧
             Symbol.isNamed { name := "EQUAL" } "LET*" = false := by
    simp [Symbol.isNamed]
  have hin : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil)))
      = some (Logic.equal va vb) :=
    conv_builtin2 w env { name := "EQUAL" } a b va vb (Logic.equal va vb)
      hns h_no_equal ⟨Na, hNa⟩ ⟨Nb, hNb⟩ (callBuiltin_equal va vb)
  have hl : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "EQUAL" }))
        (.cons (.cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil)))
          (.cons r .nil)))
      = some (Logic.equal (Logic.equal va vb) vr) :=
    conv_builtin2 w env { name := "EQUAL" } _ r (Logic.equal va vb) vr _
      hns h_no_equal hin ⟨Nr, hNr⟩ (callBuiltin_equal (Logic.equal va vb) vr)
  by_cases hcase : (va == vb) = true
  · have heqt : Logic.equal va vb = SExpr.t := by simp [Logic.equal, hcase]
    have hthen : ∃ N, ∀ f ≥ N, evalOpt f w env
        (.cons (.atom (.symbol { name := "EQUAL" }))
          (.cons r (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
            (.cons SExpr.t .nil)) .nil)))
        = some (Logic.equal vr SExpr.t) :=
      conv_builtin2 w env { name := "EQUAL" } r _ vr SExpr.t _
        hns h_no_equal ⟨Nr, hNr⟩ (re_val_quote w env SExpr.t)
        (callBuiltin_equal vr SExpr.t)
    have hr := conv_if_true w env
      (.cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil)))
      (.cons (.atom (.symbol { name := "EQUAL" }))
        (.cons r (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
          (.cons SExpr.t .nil)) .nil)))
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons r (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
          (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))
            .nil))))
      SExpr.t (Logic.equal vr SExpr.t) (heqt ▸ hin) (by decide) hthen
    refine fuel_eq_of_conv hl hr ?_
    rw [heqt, logic_equal_comm]
  · have heqn : Logic.equal va vb = SExpr.nil := by simp [Logic.equal, hcase]
    have hr' := re_val_if_nil_t w env r vr ⟨Nr, hNr⟩
    have hr : ∃ N, ∀ f ≥ N, evalOpt f w env (.cons (.atom (.symbol { name := "IF" }))
        (.cons (.cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil)))
          (.cons (.cons (.atom (.symbol { name := "EQUAL" }))
              (.cons r (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                (.cons SExpr.t .nil)) .nil)))
            (.cons (.cons (.atom (.symbol { name := "IF" }))
              (.cons r (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
                (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil))
                  .nil)))) .nil))))
        = some (bif Logic.toBool vr then .nil else .t) := by
      obtain ⟨Nc, hc⟩ := heqn ▸ hin
      obtain ⟨Ne, he⟩ := hr'
      refine ⟨max Nc Ne + 1, fun f hf => ?_⟩
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      rw [evalOpt_if_false g w env _ _ _ (hc g (by omega))]
      exact he g (by omega)
    refine fuel_eq_of_conv hl hr ?_
    rw [heqn]
    exact logic_equal_nil_eq_ite vr

/-- rewrite-equal's built-in NIL normalization, RIGHT form (rewrite.lisp:18091):
    `(equal x 'nil) ≡ (if x 'nil 't)`. -/
theorem re_equal_nil_norm_r (w : World) (env : Env) (x : SExpr)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (hxe : ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env x = some v) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "EQUAL" }))
        (.cons x (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil)) .nil)))
      = evalOpt f w env (.cons (.atom (.symbol { name := "IF" }))
        (.cons x (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
          (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil)) .nil)))) := by
  obtain ⟨N, vx, hN⟩ := hxe
  have hx : ∃ M, ∀ f ≥ M, evalOpt f w env x = some vx := ⟨N, hN⟩
  have hl := conv_builtin2 w env { name := "EQUAL" }
    x (.cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil))
    vx .nil (Logic.equal vx .nil)
    (by simp [Symbol.isNamed]) h_no_equal hx (re_val_quote w env .nil)
    (callBuiltin_equal vx .nil)
  have hr := re_val_if_nil_t w env x vx hx
  refine fuel_eq_of_conv hl hr ?_
  rw [← logic_equal_nil_eq_ite vx]
  exact logic_equal_comm vx .nil

end ACL2.Replay
