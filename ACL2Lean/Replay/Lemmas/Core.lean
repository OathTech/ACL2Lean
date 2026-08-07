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

end ACL2.Replay
