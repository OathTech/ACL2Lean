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
  | .cons _ _ => simp [SExpr.t] at h

/-! ## Layer 1: evalOpt atomic steps -/

/-- T7a: Quote evaluates to the quoted value. -/
theorem evalOpt_quote (f : Nat) (w : World) (env : Env) (v : SExpr) :
    evalOpt (f + 1) w env
      (.cons (.atom (.symbol { name := "quote" })) (.cons v .nil))
    = some v := by
  simp [evalOpt, evalOptStep, Symbol.isNamed]

/-- T7b: Variable lookup (bound). -/
theorem evalOpt_var (f : Nat) (w : World) (env : Env) (s : Symbol) (v : SExpr)
    (h : env.get? s = some v) :
    evalOpt (f + 1) w env (.atom (.symbol s)) = some v := by
  simp [evalOpt, evalOptStep, h]

/-- T18: Variable lookup (unbound, not t). -/
theorem evalOpt_var_unbound (f : Nat) (w : World) (env : Env) (s : Symbol)
    (h : env.get? s = none) (h_not_t : s.isNamed "t" = false) :
    evalOpt (f + 1) w env (.atom (.symbol s)) = some .nil := by
  simp [evalOpt, evalOptStep, h, h_not_t]

/-- T5a: IF with truthy test takes the then-branch. -/
theorem evalOpt_if_true (f : Nat) (w : World) (env : Env)
    (c t e : SExpr) (cv : SExpr)
    (hc : evalOpt f w env c = some cv)
    (ht : Logic.toBool cv = true) :
    evalOpt (f + 1) w env
      (.cons (.atom (.symbol { name := "if" })) (.cons c (.cons t (.cons e .nil))))
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
      (.cons (.atom (.symbol { name := "if" })) (.cons c (.cons t (.cons e .nil))))
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
    (h_not_special : s.isNamed "quote" = false ∧ s.isNamed "if" = false ∧
                     s.isNamed "let" = false ∧ s.isNamed "let*" = false)
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
    (h_not_special : s.isNamed "quote" = false ∧ s.isNamed "if" = false ∧
                     s.isNamed "let" = false ∧ s.isNamed "let*" = false)
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
    (h_not_special : s.isNamed "quote" = false ∧ s.isNamed "if" = false ∧
                     s.isNamed "let" = false ∧ s.isNamed "let*" = false)
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
    (h_not_special : s.isNamed "quote" = false ∧ s.isNamed "if" = false ∧
                     s.isNamed "let" = false ∧ s.isNamed "let*" = false)
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
    (h_not_special : s.isNamed "quote" = false ∧ s.isNamed "if" = false ∧
                     s.isNamed "let" = false ∧ s.isNamed "let*" = false)
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
    (h_not_special : s.isNamed "quote" = false ∧ s.isNamed "if" = false ∧
                     s.isNamed "let" = false ∧ s.isNamed "let*" = false)
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
    (h_ns : fn.isNamed "quote" = false ∧ fn.isNamed "if" = false ∧
            fn.isNamed "let" = false ∧ fn.isNamed "let*" = false)
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
    (h_ns : fn.isNamed "quote" = false ∧ fn.isNamed "if" = false ∧
            fn.isNamed "let" = false ∧ fn.isNamed "let*" = false)
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
    (h_ns : fn.isNamed "quote" = false ∧ fn.isNamed "if" = false ∧
            fn.isNamed "let" = false ∧ fn.isNamed "let*" = false)
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
    (h_ns : fn.isNamed "quote" = false ∧ fn.isNamed "if" = false ∧
            fn.isNamed "let" = false ∧ fn.isNamed "let*" = false)
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
    (h_ns : fn.isNamed "quote" = false ∧ fn.isNamed "if" = false ∧
            fn.isNamed "let" = false ∧ fn.isNamed "let*" = false)
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
    (h_ns : fn.isNamed "quote" = false ∧ fn.isNamed "if" = false ∧
            fn.isNamed "let" = false ∧ fn.isNamed "let*" = false)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env b = evalOpt f w env b') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol fn)) (.cons a (.cons b .nil)))
      = evalOpt f w env (.cons (.atom (.symbol fn)) (.cons a (.cons b' .nil))) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 1, fun f hf => ?_⟩
  match f with
  | f + 1 => exact evalOpt_congr_binary_right_step f w env fn a b b' h_ns (hN f (by omega))

/-! ## Free-variable congruence (relate a function body's `bindArgs` env to the
    caller env on the term's free variables)

  Ported from the prior hand-proof branch (sorry-free there); the call-case
  `show` is adapted to the current `callBuiltin : … → Option SExpr` shape. Used by
  the step case to relate `evalOpt … (bindArgs …) body` (after a definition
  unfold) back to `evalOpt … e body` — both read the env only at the body's free
  variables, which agree. -/

/-! Free variables of a term that `evalOpt` may read. Head symbols and `quote`
    bodies are not reads. (Over-approximates inside LET; combined with `NoLet`.) -/
mutual
def freeVars : SExpr → List Symbol
  | .atom (.symbol s) => [s]
  | .cons (.atom (.symbol q)) rest => if q.isNamed "quote" then [] else freeVarsSpine rest
  | _ => []
def freeVarsSpine : SExpr → List Symbol
  | .cons a rest => freeVars a ++ freeVarsSpine rest
  | _ => []
end

/-! A term with no LET/LET* anywhere it is evaluated. -/
mutual
def NoLet : SExpr → Bool
  | .cons (.atom (.symbol q)) rest =>
      if q.isNamed "let" || q.isNamed "let*" then false
      else if q.isNamed "quote" then true else NoLetSpine rest
  | _ => true
def NoLetSpine : SExpr → Bool
  | .cons a rest => NoLet a && NoLetSpine rest
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
theorem NoLet_of_mem_spine : ∀ {argsExpr : SExpr} {args : List SExpr},
    argsExpr.toList? = some args → NoLetSpine argsExpr = true → ∀ a ∈ args, NoLet a = true
  | .nil, _, h, _ => by simp_all [SExpr.toList?]
  | .atom _, _, h, _ => by simp_all [SExpr.toList?]
  | .cons hd tl, args, h, hnl => by
      simp only [SExpr.toList?] at h
      match htl : tl.toList? with
      | some rest =>
        simp only [htl, bind, Option.bind, Option.some.injEq] at h
        subst_vars
        simp only [NoLetSpine, Bool.and_eq_true] at hnl
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha'
        · exact hnl.1
        · exact NoLet_of_mem_spine htl hnl.2 a ha'
      | none => simp [htl, bind, Option.bind] at h

/-- FREE-VARIABLE CONGRUENCE: `evalOpt` reads the env only at a term's free
    variables, so two envs agreeing there evaluate the (LET-free) term equally. -/
theorem evalOpt_freevar_congr (w : World) :
    ∀ (n : Nat) (e1 e2 : Env) (term : SExpr), NoLet term = true →
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
    | .atom (.symbol s) => exact hfv s (by simp [freeVars])
    | .cons (.atom (.number _)) _ => rfl
    | .cons (.atom (.string _)) _ => rfl
    | .cons (.atom (.keyword _)) _ => rfl
    | .cons .nil _ => rfl
    | .cons (.cons _ _) _ => rfl
    | .cons (.atom (.symbol s)) argsExpr =>
      show evalOptStep (evalOpt n) w e1 (.cons (.atom (.symbol s)) argsExpr)
         = evalOptStep (evalOpt n) w e2 (.cons (.atom (.symbol s)) argsExpr)
      simp only [evalOptStep_cons_symbol]
      cases hq : s.isNamed "quote" with
      | true => simp only [↓reduceIte]
      | false =>
        have hkey : ∀ args, argsExpr.toList? = some args →
            ∀ a ∈ args, evalOpt n w e1 a = evalOpt n w e2 a := by
          intro args htl a ha
          have hnls : NoLetSpine argsExpr = true := by
            simp only [NoLet, hq] at hnl
            by_cases hl : (s.isNamed "let" || s.isNamed "let*") = true
            · simp [hl] at hnl
            · simp only [Bool.not_eq_true] at hl; simp [hl] at hnl
              simpa using hnl
          exact ih e1 e2 a (NoLet_of_mem_spine htl hnls a ha)
            (fun s' hs' => hfv s' (by simp only [freeVars, hq]; exact freeVars_subset_spine htl ha hs'))
        cases hif : s.isNamed "if" with
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
          cases hlet : (s.isNamed "let" || s.isNamed "let*") with
          | true =>
            exfalso; simp only [NoLet, hq, hlet, if_true, Bool.false_eq_true] at hnl
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
    (h_ns : s.isNamed "quote" = false ∧ s.isNamed "if" = false ∧
            s.isNamed "let" = false ∧ s.isNamed "let*" = false)
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
    (h_ns : s.isNamed "quote" = false ∧ s.isNamed "if" = false ∧
            s.isNamed "let" = false ∧ s.isNamed "let*" = false)
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
      (.cons (.atom (.symbol { name := "if" })) (.cons c (.cons t (.cons el .nil)))) = some v := by
  obtain ⟨Nc, hc⟩ := htest; obtain ⟨Nt, ht⟩ := hthen
  refine ⟨max Nc Nt + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [evalOpt_if_true g w env c t el cv (hc g (by omega)) hcv]
  exact ht g (by omega)

/-- A 1-arg user-defined call converges to the body's value (in `bindArgs`). -/
theorem conv_defn_1 (w : World) (env : Env) (s : Symbol) (arg av : SExpr)
    (formal : Symbol) (body v : SExpr)
    (h_ns : s.isNamed "quote" = false ∧ s.isNamed "if" = false ∧
            s.isNamed "let" = false ∧ s.isNamed "let*" = false)
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
    (h_ns : s.isNamed "quote" = false ∧ s.isNamed "if" = false ∧
            s.isNamed "let" = false ∧ s.isNamed "let*" = false)
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

/-! ## Term substitution (definition-unfold / IH replay)

  Ported sorry-free from the prior hand-proof branch; dispatch-agnostic (they
  factor through mapM/argument congruence), so unchanged by callBuiltin->Option.
  substTerm is first-order formal->arg-term substitution (intrinsic :DEFINITION
  replay); evalOpt_substTerm_eq / evalOpt_substTerm_quote / evalOpt_envUpdate_bindArgs
  are the substitution lemma the driver needs for definition unfolds and the IH. -/

/-- Positional lookup of a symbol in parallel formals/args lists; first match. -/
def lookupSubst (s : Symbol) : List Symbol → List SExpr → Option SExpr
  | f :: fs, a :: as => if s == f then some a else lookupSubst s fs as
  | _, _ => none

/-- Wrap a value as a self-evaluating `(quote v)` term. -/
def quoteVal (v : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "quote" })) (.cons v .nil)

mutual
/-- Substitute each formal by its corresponding arg term throughout `term`.
    Quote-opaque; rewrites bare variable positions and function-call spines. -/
def substTerm (formals : List Symbol) (args : List SExpr) : SExpr → SExpr
  | .atom (.symbol s) => (lookupSubst s formals args).getD (.atom (.symbol s))
  | .cons (.atom (.symbol q)) rest =>
      if q.isNamed "quote" then .cons (.atom (.symbol q)) rest
      else .cons (.atom (.symbol q)) (substSpine formals args rest)
  | t => t
/-- Map `substTerm` across an argument spine. -/
def substSpine (formals : List Symbol) (args : List SExpr) : SExpr → SExpr
  | .cons a rest => .cons (substTerm formals args a) (substSpine formals args rest)
  | t => t
end

/-- Extend `env` by binding each formal to its value (first formal wins, as in
    `bindArgs`). `bindArgs` is the empty-base instance (see below). -/
def envUpdate (env : Env) : List Symbol → List SExpr → Env
  | f :: fs, v :: vs => (envUpdate env fs vs).insert f v
  | _, _ => env

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

/-- `bindArgs` is `envUpdate` over the empty environment. -/
theorem bindArgs_eq_envUpdate_empty :
    ∀ (formals : List Symbol) (vals : List SExpr),
      bindArgs formals vals = envUpdate (∅ : Env) formals vals
  | [], _ => rfl
  | _ :: _, [] => rfl
  | f :: fs, v :: vs => by
      show (bindArgs fs vs).insert f v = (envUpdate (∅ : Env) fs vs).insert f v
      rw [bindArgs_eq_envUpdate_empty fs vs]

/-- Looking up a symbol in `envUpdate` = the substitution lookup, falling back to
    the base env. -/
theorem envUpdate_get (env : Env) (s : Symbol) :
    ∀ (formals : List Symbol) (vals : List SExpr),
      (envUpdate env formals vals).get? s
        = match lookupSubst s formals vals with
          | some v => some v
          | none => env.get? s
  | [], _ => rfl
  | _ :: _, [] => rfl
  | f :: fs, v :: vs => by
      show ((envUpdate env fs vs).insert f v).get? s = _
      rw [Env.get?_insert, envUpdate_get env s fs vs]
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

/-- Two envs that agree at `s` evaluate the variable `s` identically. -/
theorem evalOpt_symbol_of_get (f : Nat) (w : World) (e1 e2 : Env) (s : Symbol)
    (h : e1.get? s = e2.get? s) :
    evalOpt (f + 1) w e1 (.atom (.symbol s)) = evalOpt (f + 1) w e2 (.atom (.symbol s)) := by
  simp only [evalOpt, evalOptStep, h]

/-- SUBSTITUTION (quoted values): substituting each formal by `(quote vᵢ)` in a
    LET-free body, evaluated in `env`, equals evaluating the body in the env
    extended with the formals bound to the `vᵢ`. Fixed fuel — no convergence
    needed, since quoted values evaluate immediately. The bridge from this to
    `bindArgs` is `evalOpt_freevar_congr` (when the body is closed under the
    formals). -/
theorem evalOpt_substTerm_quote (w : World) (formals : List Symbol) (vals : List SExpr) :
    ∀ (m : Nat) (env : Env) (body : SExpr), NoLet body = true →
      evalOpt m w env (substTerm formals (vals.map quoteVal) body)
        = evalOpt m w (envUpdate env formals vals) body := by
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
    | .atom (.symbol s) =>
      show evalOpt (n + 1) w env
            ((lookupSubst s formals (vals.map quoteVal)).getD (.atom (.symbol s)))
         = evalOpt (n + 1) w (envUpdate env formals vals) (.atom (.symbol s))
      rw [lookupSubst_map_quoteVal]
      cases hl : lookupSubst s formals vals with
      | some vi =>
        simp only [Option.map_some, Option.getD_some, quoteVal]
        rw [evalOpt_quote n w env vi]
        have hg : (envUpdate env formals vals).get? s = some vi := by
          have he := envUpdate_get env s formals vals; rw [hl] at he; exact he
        rw [evalOpt_var n w (envUpdate env formals vals) s vi hg]
      | none =>
        simp only [Option.map_none, Option.getD_none]
        have hg : env.get? s = (envUpdate env formals vals).get? s := by
          have he := envUpdate_get env s formals vals; rw [hl] at he; exact he.symm
        exact evalOpt_symbol_of_get n w env (envUpdate env formals vals) s hg
    | .cons (.atom (.number _)) _ => rfl
    | .cons (.atom (.string _)) _ => rfl
    | .cons (.atom (.keyword _)) _ => rfl
    | .cons .nil _ => rfl
    | .cons (.cons _ _) _ => rfl
    | .cons (.atom (.symbol q)) rest =>
      by_cases hq : q.isNamed "quote" = true
      · rw [show substTerm formals (vals.map quoteVal) (.cons (.atom (.symbol q)) rest)
              = .cons (.atom (.symbol q)) rest from by simp only [substTerm, hq, if_true]]
        show evalOptStep (evalOpt n) w env (.cons (.atom (.symbol q)) rest)
           = evalOptStep (evalOpt n) w (envUpdate env formals vals) (.cons (.atom (.symbol q)) rest)
        simp only [evalOptStep_cons_symbol, hq, ↓reduceIte]
      · have hqf : q.isNamed "quote" = false := by
          simp only [Bool.not_eq_true] at hq; exact hq
        rw [show substTerm formals (vals.map quoteVal) (.cons (.atom (.symbol q)) rest)
              = .cons (.atom (.symbol q)) (substSpine formals (vals.map quoteVal) rest)
            from by simp only [substTerm, hqf, Bool.false_eq_true, if_false]]
        show evalOptStep (evalOpt n) w env
              (.cons (.atom (.symbol q)) (substSpine formals (vals.map quoteVal) rest))
           = evalOptStep (evalOpt n) w (envUpdate env formals vals)
              (.cons (.atom (.symbol q)) rest)
        simp only [evalOptStep_cons_symbol, hqf, Bool.false_eq_true, if_false]
        -- Per-element bridge: substituted arg in `env` = original arg in `envUpdate`.
        have hnls : NoLetSpine rest = true := by
          simp only [NoLet, hqf] at hnl
          by_cases hl : (q.isNamed "let" || q.isNamed "let*") = true
          · simp [hl] at hnl
          · simp only [Bool.not_eq_true] at hl; simp [hl] at hnl; simpa using hnl
        have ihkey : ∀ a ∈ (rest.toList?).getD [],
            evalOpt n w env (substTerm formals (vals.map quoteVal) a)
              = evalOpt n w (envUpdate env formals vals) a := by
          intro a ha
          cases htl : rest.toList? with
          | none => simp [htl] at ha
          | some l =>
            simp only [htl, Option.getD_some] at ha
            exact ih env a (NoLet_of_mem_spine htl hnls a ha)
        rw [substSpine_toList]
        by_cases hif : q.isNamed "if" = true
        · simp only [hif, ↓reduceIte]
          match htl : rest.toList? with
          | some [c, t, e] =>
            show (evalOpt n w env (substTerm formals (vals.map quoteVal) c)).bind
                   (fun cv => if Logic.toBool cv = true
                     then evalOpt n w env (substTerm formals (vals.map quoteVal) t)
                     else evalOpt n w env (substTerm formals (vals.map quoteVal) e))
               = (evalOpt n w (envUpdate env formals vals) c).bind
                   (fun cv => if Logic.toBool cv = true
                     then evalOpt n w (envUpdate env formals vals) t
                     else evalOpt n w (envUpdate env formals vals) e)
            simp only [ihkey c (by simp [htl]), ihkey t (by simp [htl]), ihkey e (by simp [htl])]
          | none => rfl
          | some [] => rfl
          | some [_] => rfl
          | some [_, _] => rfl
          | some (_ :: _ :: _ :: _ :: _) => rfl
        · have hiff : q.isNamed "if" = false := by
            simp only [Bool.not_eq_true] at hif; exact hif
          by_cases hlet : (q.isNamed "let" || q.isNamed "let*") = true
          · exfalso; simp only [NoLet, hqf, hlet, if_true, Bool.false_eq_true] at hnl
          · have hletf : (q.isNamed "let" || q.isNamed "let*") = false := by
              simp only [Bool.not_eq_true] at hlet; exact hlet
            simp only [hiff, hletf, Bool.false_eq_true, if_false]
            match htl : rest.toList? with
            | some l =>
              simp only [Option.map_some]
              rw [show List.mapM (fun a => evalOpt n w env a)
                      (List.map (substTerm formals (List.map quoteVal vals)) l)
                    = List.mapM (fun a => evalOpt n w (envUpdate env formals vals) a) l from by
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
    ∀ (f : Nat) (body : SExpr), NoLet body = true →
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
    | .atom (.symbol s) => exact hpw s (n + 1)
    | .cons (.atom (.number _)) _ => rfl
    | .cons (.atom (.string _)) _ => rfl
    | .cons (.atom (.keyword _)) _ => rfl
    | .cons .nil _ => rfl
    | .cons (.cons _ _) _ => rfl
    | .cons (.atom (.symbol q)) rest =>
      by_cases hq : q.isNamed "quote" = true
      · rw [show substTerm formals args (.cons (.atom (.symbol q)) rest)
              = .cons (.atom (.symbol q)) rest from by simp only [substTerm, hq, if_true],
            show substTerm formals args' (.cons (.atom (.symbol q)) rest)
              = .cons (.atom (.symbol q)) rest from by simp only [substTerm, hq, if_true]]
      · have hqf : q.isNamed "quote" = false := by
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
        have hnls : NoLetSpine rest = true := by
          simp only [NoLet, hqf] at hnl
          by_cases hl : (q.isNamed "let" || q.isNamed "let*") = true
          · simp [hl] at hnl
          · simp only [Bool.not_eq_true] at hl; simp [hl] at hnl; simpa using hnl
        have ihkey : ∀ a ∈ (rest.toList?).getD [],
            evalOpt n w env (substTerm formals args a)
              = evalOpt n w env (substTerm formals args' a) := by
          intro a ha
          cases htl : rest.toList? with
          | none => simp [htl] at ha
          | some l =>
            simp only [htl, Option.getD_some] at ha
            exact ih a (NoLet_of_mem_spine htl hnls a ha)
        rw [substSpine_toList, substSpine_toList]
        by_cases hif : q.isNamed "if" = true
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
        · have hiff : q.isNamed "if" = false := by
            simp only [Bool.not_eq_true] at hif; exact hif
          by_cases hlet : (q.isNamed "let" || q.isNamed "let*") = true
          · exfalso; simp only [NoLet, hqf, hlet, if_true, Bool.false_eq_true] at hnl
          · have hletf : (q.isNamed "let" || q.isNamed "let*") = false := by
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
    ∀ (n : Nat) (body : SExpr), sizeOf body ≤ n → NoLet body = true →
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
    | .atom (.symbol s) => exact ⟨Nag, fun f hf => hag s f hf⟩
    | .cons (.atom (.number _)) _ => exact ⟨0, fun f _ => rfl⟩
    | .cons (.atom (.string _)) _ => exact ⟨0, fun f _ => rfl⟩
    | .cons (.atom (.keyword _)) _ => exact ⟨0, fun f _ => rfl⟩
    | .cons .nil _ => exact ⟨0, fun f _ => rfl⟩
    | .cons (.cons _ _) _ => exact ⟨0, fun f _ => rfl⟩
    | .cons (.atom (.symbol q)) rest =>
      by_cases hq : q.isNamed "quote" = true
      · exact ⟨0, fun f _ => by simp only [substTerm, hq, ↓reduceIte]⟩
      · have hqf : q.isNamed "quote" = false := by
          simp only [Bool.not_eq_true] at hq; exact hq
        have hnls : NoLetSpine rest = true := by
          simp only [NoLet, hqf] at hnl
          by_cases hl : (q.isNamed "let" || q.isNamed "let*") = true
          · simp [hl] at hnl
          · simp only [Bool.not_eq_true] at hl; simp [hl] at hnl; simpa using hnl
        -- each spine element agrees eventually (it is structurally smaller)
        obtain ⟨Ns, hs⟩ : ∃ Ns, ∀ f ≥ Ns, ∀ a ∈ (rest.toList?).getD [],
            evalOpt f w env (substTerm formals args a)
              = evalOpt f w env (substTerm formals args' a) := by
          apply exists_bound_forall_mem
          intro a ha
          have hsz : sizeOf a ≤ n := by
            have h1 := sizeOf_mem_toList ha
            simp only [SExpr.cons.sizeOf_spec] at hb; omega
          have hnl_a : NoLet a = true := by
            match htl : rest.toList? with
            | some l => exact NoLet_of_mem_spine htl hnls a (by rw [htl] at ha; simpa using ha)
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
        by_cases hif : q.isNamed "if" = true
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
        · have hiff : q.isNamed "if" = false := by
            simp only [Bool.not_eq_true] at hif; exact hif
          by_cases hlet : (q.isNamed "let" || q.isNamed "let*") = true
          · exfalso; simp only [NoLet, hqf, hlet, if_true, Bool.false_eq_true] at hnl
          · have hletf : (q.isNamed "let" || q.isNamed "let*") = false := by
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

/-- Evaluating a closed (under `formals`) LET-free body in `envUpdate env` is the
    same as in `bindArgs` — the base env is invisible past the formals. -/
theorem evalOpt_envUpdate_bindArgs (w : World) (env : Env) (formals : List Symbol)
    (vals : List SExpr) (hlen : formals.length = vals.length) (g : Nat) (body : SExpr)
    (hnl : NoLet body = true) (hcl : ∀ s ∈ freeVars body, s ∈ formals) :
    evalOpt g w (envUpdate env formals vals) body = evalOpt g w (bindArgs formals vals) body := by
  rw [bindArgs_eq_envUpdate_empty]
  refine evalOpt_freevar_congr w g (envUpdate env formals vals) (envUpdate ∅ formals vals) body hnl
    (fun s hs => ?_)
  obtain ⟨v, hv⟩ := lookupSubst_some_of_mem s formals vals (hcl s hs) hlen
  have h1 := envUpdate_get env s formals vals
  have h2 := envUpdate_get (∅ : Env) s formals vals
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
    (hns : fn.isNamed "quote" = false ∧ fn.isNamed "if" = false ∧
           fn.isNamed "let" = false ∧ fn.isNamed "let*" = false)
    (hdef : w.defs.get? fn = some ([formal], body))
    (hclosed : ∀ s ∈ freeVars body, s ∈ [formal]) (hnolet : NoLet body = true)
    (harg : ∃ N, ∀ f ≥ N, evalOpt f w env arg = some av)
    (hbody : ∃ N, ∀ f ≥ N, evalOpt f w (bindArgs [formal] [av]) body = some v) :
    ∃ N, ∀ f ≥ N, evalOpt f w env (.cons (.atom (.symbol fn)) (.cons arg .nil))
      = evalOpt f w env (substTerm [formal] [arg] body) := by
  -- LHS ⇒ v  (definition unfold, call-by-value, body converges in bindArgs)
  have hlhs : ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol fn)) (.cons arg .nil)) = some v :=
    conv_defn_1 w env fn arg av formal body v hns hdef harg hbody
  -- RHS ⇒ v : substTerm [formal][arg] body ≈ substTerm [formal][quoteVal av] body
  --          = body in (envUpdate = bindArgs) ⇒ v
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
    (sizeOf body) body (Nat.le_refl _) hnolet
  have hrhs : ∃ N, ∀ f ≥ N, evalOpt f w env (substTerm [formal] [arg] body) = some v := by
    obtain ⟨Nb, hb⟩ := hbody
    refine ⟨max Ncong Nb, fun f hf => ?_⟩
    rw [← hcong f (by omega), evalOpt_substTerm_quote w [formal] [av] f env body hnolet,
        evalOpt_envUpdate_bindArgs w env [formal] [av] rfl f body hnolet hclosed]
    exact hb f (by omega)
  obtain ⟨Nl, hl⟩ := hlhs; obtain ⟨Nr, hr⟩ := hrhs
  exact ⟨max Nl Nr, fun f hf => by rw [hl f (by omega), hr f (by omega)]⟩

/-- Compound-argument `:DEFINITION` unfold (2-arg): the 2-formal analogue of
    `evalOpt_unfold1_conv`. `eval(fn arg1 arg2) = eval(substTerm [f1,f2] [arg1,arg2] body)`
    eventually, when both args converge. Requires the formals distinct. -/
theorem evalOpt_unfold2_conv (w : World) (env : Env) (fn formal1 formal2 : Symbol)
    (body arg1 arg2 av1 av2 v : SExpr)
    (hns : fn.isNamed "quote" = false ∧ fn.isNamed "if" = false ∧
           fn.isNamed "let" = false ∧ fn.isNamed "let*" = false)
    (hdef : w.defs.get? fn = some ([formal1, formal2], body))
    (hclosed : ∀ s ∈ freeVars body, s ∈ [formal1, formal2]) (hnolet : NoLet body = true)
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
    (sizeOf body) body (Nat.le_refl _) hnolet
  have hrhs : ∃ N, ∀ f ≥ N,
      evalOpt f w env (substTerm [formal1, formal2] [arg1, arg2] body) = some v := by
    obtain ⟨Nb, hb⟩ := hbody
    refine ⟨max Ncong Nb, fun f hf => ?_⟩
    rw [← hcong f (by omega), evalOpt_substTerm_quote w [formal1, formal2] [av1, av2] f env body hnolet,
        evalOpt_envUpdate_bindArgs w env [formal1, formal2] [av1, av2] rfl f body hnolet hclosed]
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
    (arg av body : SExpr) (hnl : NoLet body = true)
    (harg : ∃ N, ∀ f ≥ N, evalOpt f w env arg = some av) :
    ∃ N, ∀ f ≥ N, evalOpt f w env (substTerm [s] [arg] body)
      = evalOpt f w (envUpdate env [s] [av]) body := by
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

/-! ## Layer 2: Derived rules (compose Layer 1) -/

/-- Logic.equal returns T iff arguments are BEq-equal. -/
theorem Logic.equal_t_iff (a b : SExpr) :
    Logic.equal a b = SExpr.t ↔ a = b := by
  constructor
  · intro h
    simp [Logic.equal] at h
    exact h
  · intro h; subst h; exact Logic.equal_self a

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
    callBuiltin "equal" [a, b] = some (Logic.equal a b) := by rfl
@[simp] theorem callBuiltin_not (a : SExpr) :
    callBuiltin "not" [a] = some (Logic.not a) := by rfl
@[simp] theorem callBuiltin_consp (a : SExpr) :
    callBuiltin "consp" [a] = some (Logic.consp a) := by rfl
@[simp] theorem callBuiltin_car (a : SExpr) :
    callBuiltin "car" [a] = some (Logic.car a) := by rfl
@[simp] theorem callBuiltin_cdr (a : SExpr) :
    callBuiltin "cdr" [a] = some (Logic.cdr a) := by rfl
@[simp] theorem callBuiltin_plus (a b : SExpr) :
    callBuiltin "binary-+" [a, b] = some (Logic.plus a b) := by rfl
@[simp] theorem callBuiltin_times (a b : SExpr) :
    callBuiltin "binary-*" [a, b] = some (Logic.times a b) := by rfl
@[simp] theorem callBuiltin_true_listp (a : SExpr) :
    callBuiltin "true-listp" [a] = some (Logic.trueListp a) := by
  rfl

@[simp] theorem callBuiltin_acl2_numberp (a : SExpr) :
    callBuiltin "acl2-numberp" [a] = some (Logic.acl2Numberp a) := by
  cases a with
  | atom x => cases x <;> rfl
  | nil => rfl
  | cons _ _ => rfl
@[simp] theorem callBuiltin_atom (a : SExpr) :
    callBuiltin "atom" [a] = some (Logic.atom a) := by rfl
@[simp] theorem callBuiltin_endp (a : SExpr) :
    callBuiltin "endp" [a] = some (Logic.endp a) := by rfl
@[simp] theorem callBuiltin_natp (a : SExpr) :
    callBuiltin "natp" [a] = some (Logic.natp a) := by rfl
@[simp] theorem callBuiltin_posp (a : SExpr) :
    callBuiltin "posp" [a] = some (Logic.posp a) := by rfl

/-- T3: EQUAL-self — (EQUAL t t) evaluates to T when t converges. -/
theorem evalOpt_equal_self (f : Nat) (w : World) (env : Env)
    (t : SExpr) (v : SExpr)
    (hv : evalOpt f w env t = some v)
    (h_not_def : w.defs.get? ({ name := "equal" } : Symbol) = none) :
    evalOpt (f + 1) w env
      (.cons (.atom (.symbol { name := "equal" })) (.cons t (.cons t .nil)))
    = some SExpr.t := by
  have h_ns : ({ name := "equal" } : Symbol).isNamed "quote" = false ∧
              ({ name := "equal" } : Symbol).isNamed "if" = false ∧
              ({ name := "equal" } : Symbol).isNamed "let" = false ∧
              ({ name := "equal" } : Symbol).isNamed "let*" = false := by decide
  rw [evalOpt_builtin_2 f w env { name := "equal" } t t v v h_ns h_not_def hv hv]
  simp [callBuiltin_equal]

/-- T2: EQUAL-T implies evaluation equality. -/
theorem eval_equal_t_implies_eq (f : Nat) (w : World) (env : Env)
    (a b : SExpr) (va vb : SExpr)
    (ha : evalOpt f w env a = some va)
    (hb : evalOpt f w env b = some vb)
    (h_not_def : w.defs.get? (({ name := "equal" } : Symbol)) = none)
    (h_eq : evalOpt (f + 1) w env
      (.cons (.atom (.symbol (({ name := "equal" } : Symbol)))) (.cons a (.cons b .nil)))
      = some SExpr.t) :
    va = vb := by
  have h_ns : (({ name := "equal" } : Symbol)).isNamed "quote" = false ∧
              (({ name := "equal" } : Symbol)).isNamed "if" = false ∧
              (({ name := "equal" } : Symbol)).isNamed "let" = false ∧
              (({ name := "equal" } : Symbol)).isNamed "let*" = false := by decide
  rw [evalOpt_builtin_2 f w env (({ name := "equal" } : Symbol)) a b va vb h_ns h_not_def ha hb] at h_eq
  -- h_eq : some (callBuiltin "equal" [va, vb]) = some SExpr.t
  simp only [callBuiltin_equal, Option.some.injEq] at h_eq
  exact (Logic.equal_t_iff va vb).mp h_eq

/-- T11a: NOT(e) = NIL implies e evaluates to something truthy. -/
theorem not_nil_means_truthy (f : Nat) (w : World) (env : Env)
    (t : SExpr) (tv : SExpr)
    (h_not_def : w.defs.get? (({ name := "not" } : Symbol)) = none)
    (ht : evalOpt f w env t = some tv)
    (h_not : evalOpt (f + 1) w env
      (.cons (.atom (.symbol (({ name := "not" } : Symbol)))) (.cons t .nil))
      = some SExpr.nil) :
    Logic.toBool tv = true := by
  have h_ns : (({ name := "not" } : Symbol)).isNamed "quote" = false ∧
              (({ name := "not" } : Symbol)).isNamed "if" = false ∧
              (({ name := "not" } : Symbol)).isNamed "let" = false ∧
              (({ name := "not" } : Symbol)).isNamed "let*" = false := by decide
  rw [evalOpt_builtin_1 f w env (({ name := "not" } : Symbol)) t tv h_ns h_not_def ht] at h_not
  -- h_not : some (callBuiltin "not" [tv]) = some SExpr.nil
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

/-- `toRat` always yields a positive denominator. -/
theorem toRat_den_pos (s : SExpr) : 0 < (Logic.toRat s).2 := by
  unfold Logic.toRat
  split
  · exact Nat.one_pos
  · split
    · exact Nat.one_pos
    · omega
  · split
    · exact Nat.one_pos
    · positivity
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
  simp only [Logic.mkNumber, Int.ofNat_eq_natCast, if_neg (show ¬ d = 0 by omega)]
  by_cases h1 : d / Nat.gcd n.natAbs d = 1
  · simp [Logic.toRat, h1]
  · simp [Logic.toRat, h1, (show d / Nat.gcd n.natAbs d ≠ 0 by omega)]

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
    simp only [Logic.mkNumber, Int.ofNat_eq_natCast, if_neg hd, if_neg hdk, hnat,
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
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some bv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "cdr" }))
        (.cons (.cons (.atom (.symbol { name := "cons" })) (.cons a (.cons b .nil))) .nil))
      = evalOpt f w env b :=
  fuel_eq_of_conv
    (conv_builtin1 w env { name := "cdr" }
      (.cons (.atom (.symbol { name := "cons" })) (.cons a (.cons b .nil)))
      (.cons av bv) bv (by decide) h_no_cdr
      (conv_builtin2 w env { name := "cons" } a b av bv (.cons av bv) (by decide) h_no_cons ha hb rfl)
      (by rw [callBuiltin_cdr, logic_cdr_cons]))
    hb rfl

/-- RUNE `car-cons`: `(car (cons a b)) ⇒ a`. Operands existential. -/
theorem re_car_cons (w : World) (env : Env) (a b av bv : SExpr)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some bv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "car" }))
        (.cons (.cons (.atom (.symbol { name := "cons" })) (.cons a (.cons b .nil))) .nil))
      = evalOpt f w env a :=
  fuel_eq_of_conv
    (conv_builtin1 w env { name := "car" }
      (.cons (.atom (.symbol { name := "cons" })) (.cons a (.cons b .nil)))
      (.cons av bv) av (by decide) h_no_car
      (conv_builtin2 w env { name := "cons" } a b av bv (.cons av bv) (by decide) h_no_cons ha hb rfl)
      (by rw [callBuiltin_car, logic_car_cons]))
    ha rfl

/-- RUNE `commutativity-of-+`: `(+ a b) ⇒ (+ b a)`. -/
theorem re_plus_comm (w : World) (env : Env) (a b av bv : SExpr)
    (h_no_plus : w.defs.get? ({ name := "binary-+" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some bv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "binary-+" })) (.cons a (.cons b .nil)))
      = evalOpt f w env (.cons (.atom (.symbol { name := "binary-+" })) (.cons b (.cons a .nil))) :=
  fuel_eq_of_conv
    (conv_builtin2 w env { name := "binary-+" } a b av bv (Logic.plus av bv)
      (by decide) h_no_plus ha hb (callBuiltin_plus _ _))
    (conv_builtin2 w env { name := "binary-+" } b a bv av (Logic.plus bv av)
      (by decide) h_no_plus hb ha (callBuiltin_plus _ _))
    (logic_plus_comm av bv)

/-- RUNE `commutativity-2-of-+`: `(+ a (+ b c)) ⇒ (+ b (+ a c))`. Unconditional —
    faithful to ACL2's `(defthm commutativity-2-of-+ …)`, which has no type
    hypothesis (`binary-+` coerces via `fix`). Operands converge to SOME value;
    the value-equality is `logic_plus_comm2`. -/
theorem re_plus_comm2 (w : World) (env : Env) (a b c : SExpr) (av bv cv : SExpr)
    (h_no_plus : w.defs.get? ({ name := "binary-+" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some bv)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some cv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "binary-+" }))
        (.cons a (.cons (.cons (.atom (.symbol { name := "binary-+" })) (.cons b (.cons c .nil))) .nil)))
      = evalOpt f w env (.cons (.atom (.symbol { name := "binary-+" }))
        (.cons b (.cons (.cons (.atom (.symbol { name := "binary-+" })) (.cons a (.cons c .nil))) .nil))) := by
  have hbc : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "binary-+" })) (.cons b (.cons c .nil)))
      = some (Logic.plus bv cv) :=
    conv_builtin2 w env { name := "binary-+" } b c _ _ _ (by decide) h_no_plus hb hc (callBuiltin_plus _ _)
  have hac : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "binary-+" })) (.cons a (.cons c .nil)))
      = some (Logic.plus av cv) :=
    conv_builtin2 w env { name := "binary-+" } a c _ _ _ (by decide) h_no_plus ha hc (callBuiltin_plus _ _)
  exact fuel_eq_of_conv
    (conv_builtin2 w env { name := "binary-+" } a _ _ _ _ (by decide) h_no_plus ha hbc (callBuiltin_plus _ _))
    (conv_builtin2 w env { name := "binary-+" } b _ _ _ _ (by decide) h_no_plus hb hac (callBuiltin_plus _ _))
    (logic_plus_comm2 av bv cv)

/-- RUNE `if-simplification` (true test): `(if c t e) ⇒ t` when the test converges
    to a truthy value. Term-to-term; the then-branch's value stays existential. -/
theorem re_if_true (w : World) (env : Env) (c t e cv tv : SExpr)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some cv) (hcv : Logic.toBool cv = true)
    (ht : ∃ N, ∀ f ≥ N, evalOpt f w env t = some tv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "if" })) (.cons c (.cons t (.cons e .nil))))
      = evalOpt f w env t :=
  fuel_eq_of_conv (conv_if_true w env c t e cv tv hc hcv ht) ht rfl

/-- RUNE `if-simplification` (false test): `(if c t e) ⇒ e` when the test
    converges to `nil`. Term-to-term; the else-branch's value stays existential. -/
theorem re_if_false (w : World) (env : Env) (c t e ev : SExpr)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some .nil)
    (he : ∃ N, ∀ f ≥ N, evalOpt f w env e = some ev) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "if" })) (.cons c (.cons t (.cons e .nil))))
      = evalOpt f w env e := by
  have hconv : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "if" })) (.cons c (.cons t (.cons e .nil)))) = some ev := by
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
    (hns : fn.isNamed "quote" = false ∧ fn.isNamed "if" = false ∧
           fn.isNamed "let" = false ∧ fn.isNamed "let*" = false)
    (hdef : w.defs.get? fn = some ([formal], body))
    (hclosed : ∀ s ∈ freeVars body, s = formal) (hnolet : NoLet body = true)
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
  rw [evalOpt_freevar_congr w f env (bindArgs [formal] [av]) body hnolet (fun s hs => ?_)]
  · exact hb f hf
  · rw [hclosed s hs]
    exact (hbind 0).trans (evalOpt_var 0 w _ formal av (bindArgs_single_get_self formal av)).symm

/-- RUNE `:DEFINITION fn` on two VARIABLE arguments: `(fn x y) ⇒ body`. -/
theorem re_unfold2_var (w : World) (env : Env) (fn f1 f2 : Symbol) (av1 av2 body v : SExpr)
    (hne : f1 ≠ f2)
    (hns : fn.isNamed "quote" = false ∧ fn.isNamed "if" = false ∧
           fn.isNamed "let" = false ∧ fn.isNamed "let*" = false)
    (hdef : w.defs.get? fn = some ([f1, f2], body))
    (hclosed : ∀ s ∈ freeVars body, s = f1 ∨ s = f2) (hnolet : NoLet body = true)
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
  rw [evalOpt_freevar_congr w f env (bindArgs [f1, f2] [av1, av2]) body hnolet (fun s hs => ?_)]
  · exact hb f hf
  · rcases hclosed s hs with h | h
    · rw [h]; exact (hbind1 0).trans
        (evalOpt_var 0 w _ f1 av1 (bindArgs_pair_get_fst f1 f2 av1 av2)).symm
    · rw [h]; exact (hbind2 0).trans
        (evalOpt_var 0 w _ f2 av2 (bindArgs_pair_get_snd f1 f2 av1 av2 hne)).symm

/-! ## Induction principles (T10) -/

/-- T10: Induction on consp/cdr structure (matching my-app's recursion).
    If P holds when consp(v) is nil, and P(cdr(v)) implies P(v) when consp(v) is non-nil,
    then P holds for all v. Proved by well-founded induction on acl2Count. -/
theorem acl2_induction_consp (P : SExpr → Prop)
    (base : ∀ v, Logic.consp v = .nil → P v)
    (step : ∀ v, Logic.consp v ≠ .nil → P (Logic.cdr v) → P v) :
    ∀ v, P v := by
  intro v
  -- Strong induction on acl2Count v
  have : ∀ n, ∀ v, v.acl2Count ≤ n → P v := by
    intro n
    induction n with
    | zero =>
      intro v hv
      -- acl2Count v ≤ 0 means v is nil or atom (not cons)
      apply base
      match v with
      | .nil => rfl
      | .atom _ => rfl
      | .cons a d => simp [SExpr.acl2Count] at hv
    | succ n ih =>
      intro v hv
      by_cases hc : Logic.consp v = .nil
      · exact base v hc
      · apply step v hc
        apply ih
        -- Need: acl2Count (Logic.cdr v) ≤ n
        match v, hc with
        | .cons a d, _ =>
          simp [Logic.cdr, SExpr.acl2Count] at hv ⊢
          omega
  exact this v.acl2Count v (Nat.le_refl _)

/-! ## Driver combinators for terminal nodes (fuel-existential form)

These package a terminal rune as the `∃N∀f≥N` fact the driver emits, so `replayNode`
just applies the combinator (no inline fuel plumbing). Kernel-checked once here. -/

/-- Convergence (totality form) of a `quote`: `(quote v)` converges to SOME value
    (namely `v`) for all sufficient fuel. The witness is existential so callers need
    no concrete value. -/
-- CONVENTION: convergence is stated in **v-fixed totality** form
-- `∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env t = some v` — a single definite value `v`
-- (`evalOpt` is fuel-monotone, so a converging term HAS one value). This feeds any
-- value-specific lemma: `obtain ⟨N, v, h⟩` gives `∀ f ≥ N, … = some v`. (The weaker
-- v-inside form `∃ N, ∀ f ≥ N, ∃ v` supplies no usable witness.)

theorem re_conv_quote (w : World) (env : Env) (v : SExpr) :
    ∃ N, ∃ v', ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "quote" })) (.cons v .nil)) = some v' :=
  ⟨1, v, fun f _ => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact evalOpt_quote g w env v⟩

/-- Convergence (v-fixed) of a VARIABLE: `(var s)` converges to its binding (or `nil`
    if unbound, provided `s` is not the constant `t`) in ANY environment — the
    variable-convergence fact the mirror theorem's `∀ env` quantification needs. -/
theorem re_conv_var (w : World) (env : Env) (s : Symbol) (h_not_t : s.isNamed "t" = false) :
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
    (h_no_equal : w.defs.get? ({ name := "equal" } : Symbol) = none) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "equal" })) (.cons A (.cons A .nil))) = some SExpr.t := by
  obtain ⟨N, v, hN⟩ := hconv
  refine ⟨N + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  exact evalOpt_equal_self g w env A v (hN g (by omega)) h_no_equal

/-- RUNE `cdr-cons`, driver-facing (v-fixed convergence): `(cdr (cons a b)) ⇒ b` given
    `a`, `b` converge. A thin wrapper over the value-specific `re_cdr_cons` that
    `obtain`s the fixed operand witnesses — so the driver passes `proveConv`'s output
    straight in (no `Exists.elim` threading). -/
theorem re_cdr_cons_conv (w : World) (env : Env) (a b : SExpr)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none)
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∃ bv, ∀ f ≥ N, evalOpt f w env b = some bv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "cdr" }))
        (.cons (.cons (.atom (.symbol { name := "cons" })) (.cons a (.cons b .nil))) .nil))
      = evalOpt f w env b := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨Nb, bv, hb⟩ := hb
  exact re_cdr_cons w env a b av bv h_no_cdr h_no_cons ⟨Na, ha⟩ ⟨Nb, hb⟩

/-- RUNE `car-cons` (conv form): `(car (cons a b)) ⇒ a`, term-to-term. -/
theorem re_car_cons_conv (w : World) (env : Env) (a b : SExpr)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none)
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∃ bv, ∀ f ≥ N, evalOpt f w env b = some bv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "car" }))
        (.cons (.cons (.atom (.symbol { name := "cons" })) (.cons a (.cons b .nil))) .nil))
      = evalOpt f w env a := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨Nb, bv, hb⟩ := hb
  exact re_car_cons w env a b av bv h_no_car h_no_cons ⟨Na, ha⟩ ⟨Nb, hb⟩

/-- Convergence (v-fixed) of a `(cons a b)` application: converges to `(cons av bv)`
    when `a`, `b` converge. The convergence-analyzer's compound-term case for `cons`
    (`car`/`cdr`/`binary-*`/… follow the same shape via their `callBuiltin` lemma). -/
theorem re_conv_cons (w : World) (env : Env) (a b : SExpr)
    (h_no_cons : w.defs.get? ({ name := "cons" } : Symbol) = none)
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∃ bv, ∀ f ≥ N, evalOpt f w env b = some bv) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "cons" })) (.cons a (.cons b .nil)))
      = some v := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨Nb, bv, hb⟩ := hb
  obtain ⟨N, h⟩ := conv_builtin2 w env { name := "cons" } a b av bv (.cons av bv)
    (by decide) h_no_cons ⟨Na, ha⟩ ⟨Nb, hb⟩ rfl
  exact ⟨N, .cons av bv, h⟩

/-- Convergence (v-fixed) of a `(binary-* a b)` application: converges to `times av bv`
    when `a`, `b` converge. (Same shape as `re_conv_cons`.) -/
theorem re_conv_times (w : World) (env : Env) (a b : SExpr)
    (h_no_times : w.defs.get? ({ name := "binary-*" } : Symbol) = none)
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∃ bv, ∀ f ≥ N, evalOpt f w env b = some bv) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "binary-*" })) (.cons a (.cons b .nil)))
      = some v := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨Nb, bv, hb⟩ := hb
  obtain ⟨N, h⟩ := conv_builtin2 w env { name := "binary-*" } a b av bv (Logic.times av bv)
    (by decide) h_no_times ⟨Na, ha⟩ ⟨Nb, hb⟩ rfl
  exact ⟨N, Logic.times av bv, h⟩

/-- Convergence (v-fixed) of a `(binary-+ a b)` application: converges to `plus av bv`
    when `a`, `b` converge. (Same shape as `re_conv_times`.) -/
theorem re_conv_plus (w : World) (env : Env) (a b : SExpr)
    (h_no_plus : w.defs.get? ({ name := "binary-+" } : Symbol) = none)
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∃ bv, ∀ f ≥ N, evalOpt f w env b = some bv) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "binary-+" })) (.cons a (.cons b .nil)))
      = some v := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨Nb, bv, hb⟩ := hb
  obtain ⟨N, h⟩ := conv_builtin2 w env { name := "binary-+" } a b av bv (Logic.plus av bv)
    (by decide) h_no_plus ⟨Na, ha⟩ ⟨Nb, hb⟩ rfl
  exact ⟨N, Logic.plus av bv, h⟩

/-- Convergence (v-fixed) of a UNARY builtin application `(car a)`: converges to
    `car av` when `a` converges. The convergence-analyzer's unary-builtin shape;
    `cdr`/`consp` follow identically via their `callBuiltin` lemma. -/
theorem re_conv_car (w : World) (env : Env) (a : SExpr)
    (h_no_car : w.defs.get? ({ name := "car" } : Symbol) = none)
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "car" })) (.cons a .nil)) = some v := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨N, h⟩ := conv_builtin1 w env { name := "car" } a av (Logic.car av)
    (by decide) h_no_car ⟨Na, ha⟩ (callBuiltin_car av)
  exact ⟨N, Logic.car av, h⟩

/-- Convergence (v-fixed) of `(cdr a)`: converges to `cdr av` when `a` converges. -/
theorem re_conv_cdr (w : World) (env : Env) (a : SExpr)
    (h_no_cdr : w.defs.get? ({ name := "cdr" } : Symbol) = none)
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "cdr" })) (.cons a .nil)) = some v := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨N, h⟩ := conv_builtin1 w env { name := "cdr" } a av (Logic.cdr av)
    (by decide) h_no_cdr ⟨Na, ha⟩ (callBuiltin_cdr av)
  exact ⟨N, Logic.cdr av, h⟩

/-- Convergence (v-fixed) of `(consp a)`: converges to `consp av` when `a` converges. -/
theorem re_conv_consp (w : World) (env : Env) (a : SExpr)
    (h_no_consp : w.defs.get? ({ name := "consp" } : Symbol) = none)
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av) :
    ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "consp" })) (.cons a .nil)) = some v := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨N, h⟩ := conv_builtin1 w env { name := "consp" } a av (Logic.consp av)
    (by decide) h_no_consp ⟨Na, ha⟩ (callBuiltin_consp av)
  exact ⟨N, Logic.consp av, h⟩

/-- RUNE `definition` (1-arg), driver-facing: `(fn arg) ⇒ substTerm [formal] [arg] body`.
    Takes `arg`'s convergence (v-fixed) and the body's convergence in EVERY env
    (`hbodyAll` — the driver proves this by running the convergence analyzer under a
    quantified env). A wrapper over `evalOpt_unfold1_conv` that instantiates the body
    convergence at the `bindArgs` env (which mentions the obtained arg value `av`), so
    the driver needs no `Exists.elim` of its own. -/
theorem re_unfold1_conv (w : World) (env : Env) (fn formal : Symbol) (body arg : SExpr)
    (hns : fn.isNamed "quote" = false ∧ fn.isNamed "if" = false ∧
           fn.isNamed "let" = false ∧ fn.isNamed "let*" = false)
    (hdef : w.defs.get? fn = some ([formal], body))
    (hclosed : ∀ s ∈ freeVars body, s ∈ [formal]) (hnolet : NoLet body = true)
    (harg : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env arg = some av)
    (hbodyAll : ∀ env', ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' body = some v) :
    ∃ N, ∀ f ≥ N, evalOpt f w env (.cons (.atom (.symbol fn)) (.cons arg .nil))
      = evalOpt f w env (substTerm [formal] [arg] body) := by
  obtain ⟨Na, av, ha⟩ := harg
  obtain ⟨Nb, v, hb⟩ := hbodyAll (bindArgs [formal] [av])
  exact evalOpt_unfold1_conv w env fn formal body arg av v hns hdef hclosed hnolet ⟨Na, ha⟩ ⟨Nb, hb⟩

/-- RUNE recognizer (true): `(acl2-numberp z) ⇒ t` when `z` converges to an integer — the
    form `type-prescription:my-len` supplies. Mirrors the recognizer node that feeds
    `definition:fix`'s `if` test in the base case (a builtin recognizer like the step
    case's `consp`; the operand value stays existential). -/
theorem re_acl2_numberp_int (w : World) (env : Env) (z : SExpr) (k : Int)
    (h_no : w.defs.get? ({ name := "acl2-numberp" } : Symbol) = none)
    (hz : ∃ N, ∀ f ≥ N, evalOpt f w env z = some (.atom (.number (.int k)))) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "acl2-numberp" })) (.cons z .nil)) = some .t :=
  conv_builtin1 w env { name := "acl2-numberp" } z (.atom (.number (.int k))) .t
    (by decide) h_no hz (by rfl)

/-! ## Decision-procedure discharge leaves (the ratified carve-out)

    A clause ACL2 closed by a verdict-only decision procedure (tau / type-set
    forward-chain) carries an emitted discharge node `(disjoin clause) ⇒ t`. The
    driver replays it by VALUE-characterized evaluation of the if-spine
    (`proveVal`): every subterm's value is an explicit `Logic`-primitive
    expression over the clause variables' env values, the spine splits on each
    literal's value via `re_dp_if_split`, and the residual fact
    `∀ vars, v₁ = nil → … → vₖ = t` is closed by a kernel-checked decision
    procedure (`omega` after SExpr case-split — see the carve-out in CLAUDE.md). -/

@[simp] theorem callBuiltin_zp (a : SExpr) :
    callBuiltin "zp" [a] = some (Logic.zp a) := by rfl
@[simp] theorem callBuiltin_lt (a b : SExpr) :
    callBuiltin "<" [a, b] = some (Logic.lt a b) := by rfl
@[simp] theorem callBuiltin_integerp (a : SExpr) :
    callBuiltin "integerp" [a] = some (Logic.integerp a) := by rfl
@[simp] theorem callBuiltin_cons (a b : SExpr) :
    callBuiltin "cons" [a, b] = some (SExpr.cons a b) := by rfl
@[simp] theorem callBuiltin_implies (a b : SExpr) :
    callBuiltin "implies" [a, b] = some (Logic.implies a b) := by rfl
@[simp] theorem callBuiltin_iff (a b : SExpr) :
    callBuiltin "iff" [a, b] = some (Logic.iff a b) := by rfl

/-- Value-characterized convergence of a quoted constant: `(quote v) ⇒ v`. -/
theorem re_val_quote (w : World) (env : Env) (v : SExpr) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "quote" })) (.cons v .nil)) = some v :=
  ⟨1, fun f hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact evalOpt_quote g w env v⟩

/-- Value-characterized convergence of a variable: `(var s) ⇒ (env.get? s).getD nil`
    (the binding, or `nil` if unbound — requires `s ≠ t`, the self-evaluating symbol). -/
theorem re_val_var (w : World) (env : Env) (s : Symbol)
    (h_not_t : s.isNamed "t" = false) :
    ∃ N, ∀ f ≥ N, evalOpt f w env (.atom (.symbol s)) = some ((env.get? s).getD .nil) := by
  match h : env.get? s with
  | some v => exact ⟨1, fun f _ => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      simpa [h] using evalOpt_var g w env s v h⟩
  | none => exact ⟨1, fun f _ => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      simpa [h] using evalOpt_var_unbound g w env s h h_not_t⟩

/-- Discharge-leaf if-split: `(if c t e) ⇒ t` (the value `t`) given the test's
    VALUE-characterized convergence to `cv` and t-convergence of the branch selected
    by EITHER case of `cv` (both implications supplied; the proof case-splits on
    `cv = nil`). The spine combinator for a decision-procedure discharge: the driver
    cannot know which literal of the disjunction is true for a given env, so both
    branches are discharged hypothetically. -/
theorem re_dp_if_split (w : World) (env : Env) (c t e cv : SExpr)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some cv)
    (hthen : cv ≠ .nil → ∃ N, ∀ f ≥ N, evalOpt f w env t = some .t)
    (helse : cv = .nil → ∃ N, ∀ f ≥ N, evalOpt f w env e = some .t) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "if" })) (.cons c (.cons t (.cons e .nil))))
      = some .t := by
  obtain ⟨Nc, hc⟩ := hc
  by_cases hcv : cv = .nil
  · obtain ⟨Ne, he⟩ := helse hcv
    refine ⟨max Nc Ne + 1, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [evalOpt_if_false g w env c t e (hcv ▸ hc g (by omega))]
    exact he g (by omega)
  · obtain ⟨Nt, ht⟩ := hthen hcv
    refine ⟨max Nc Nt + 1, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [evalOpt_if_true g w env c t e cv (hc g (by omega))
      (by cases cv <;> simp_all [Logic.toBool])]
    exact ht g (by omega)

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
    (h_ns : fn.isNamed "quote" = false ∧ fn.isNamed "if" = false ∧
            fn.isNamed "let" = false ∧ fn.isNamed "let*" = false)
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
    (h_ns : fn.isNamed "quote" = false ∧ fn.isNamed "if" = false ∧
            fn.isNamed "let" = false ∧ fn.isNamed "let*" = false)
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
    (h_ns : s.isNamed "quote" = false ∧ s.isNamed "if" = false ∧
            s.isNamed "let" = false ∧ s.isNamed "let*" = false)
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
    (h_ns : s.isNamed "quote" = false ∧ s.isNamed "if" = false ∧
            s.isNamed "let" = false ∧ s.isNamed "let*" = false)
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
        (.cons (.atom (.symbol { name := "if" })) (.cons c (.cons t (.cons e .nil))))
      = evalOpt f w env
        (.cons (.atom (.symbol { name := "if" })) (.cons c' (.cons t (.cons e .nil)))) := by
  obtain ⟨N, h⟩ := h
  refine ⟨N + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  show evalOptStep (evalOpt g) w env _ = evalOptStep (evalOpt g) w env _
  unfold evalOptStep
  simp only [Symbol.isNamed, SExpr.toList?]
  show (evalOpt g w env c).bind _ = (evalOpt g w env c').bind _
  rw [h g (by omega)]

/-- RUNE `:DEFINITION fn` on two general arguments, body convergence supplied for
    EVERY environment (the ∀-env analyzer form — the 2-arg sibling of
    `re_unfold1_conv`). -/
theorem re_unfold2_conv (w : World) (env : Env) (fn f1 f2 : Symbol)
    (body arg1 arg2 : SExpr)
    (hns : fn.isNamed "quote" = false ∧ fn.isNamed "if" = false ∧
           fn.isNamed "let" = false ∧ fn.isNamed "let*" = false)
    (hdef : w.defs.get? fn = some ([f1, f2], body))
    (hclosed : ∀ s ∈ freeVars body, s ∈ [f1, f2]) (hnolet : NoLet body = true)
    (harg1 : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env arg1 = some av)
    (harg2 : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env arg2 = some av)
    (hbodyAll : ∀ env', ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' body = some v) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol fn)) (.cons arg1 (.cons arg2 .nil)))
      = evalOpt f w env (substTerm [f1, f2] [arg1, arg2] body) := by
  obtain ⟨N1, av1, h1⟩ := harg1
  obtain ⟨N2, av2, h2⟩ := harg2
  obtain ⟨Nb, v, hb⟩ := hbodyAll (bindArgs [f1, f2] [av1, av2])
  exact evalOpt_unfold2_conv w env fn f1 f2 body arg1 arg2 av1 av2 v hns hdef hclosed hnolet
    ⟨N1, h1⟩ ⟨N2, h2⟩ ⟨Nb, hb⟩

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

The bridge consumes a PROVED child clause (`eval (disjoin cl) = some t`) and
rebuilds the truth of the clausify INPUT term by mirroring `clausify-input1`'s
pure if-recursion: `if_fact_elim` peels the proved disjunction literal by
literal (one leaf per firing literal), the value helpers below convert each
leaf's literal facts into test-value facts, and `re_dp_if_split` re-composes
the input term's if-tree (the impossible branch in each leaf is vacuous). -/

/-- ELIMINATE a proved `if` fact by its test's value: from
    `eval (if c thn els) = some v` and the test's value, either the test is
    truthy and the THEN branch carries the value, or it is nil and the ELSE
    branch does. The dual of `re_dp_if_split`. -/
theorem if_fact_elim {w : World} {env : Env} {c thn els cv v : SExpr} {C : Prop}
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some cv)
    (hfact : ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol { name := "if" }))
        (.cons c (.cons thn (.cons els .nil)))) = some v)
    (hthen : cv ≠ SExpr.nil → (∃ N, ∀ f ≥ N, evalOpt f w env thn = some v) → C)
    (helse : cv = SExpr.nil → (∃ N, ∀ f ≥ N, evalOpt f w env els = some v) → C) :
    C := by
  obtain ⟨Nc, hcf⟩ := hc
  obtain ⟨Nf, hff⟩ := hfact
  by_cases hcv : cv = SExpr.nil
  · refine helse hcv ⟨Nc + Nf + 1, fun f hge => ?_⟩
    have h1 := hff (f + 1) (by omega)
    rwa [evalOpt_if_false f w env c thn els (by rw [hcf f (by omega), hcv])] at h1
  · refine hthen hcv ⟨Nc + Nf + 1, fun f hge => ?_⟩
    have h1 := hff (f + 1) (by omega)
    rwa [evalOpt_if_true f w env c thn els cv (hcf f (by omega))
          (by cases cv <;> simp_all [Logic.toBool])] at h1

/-- `toBool` of a non-nil value is `true`. -/
theorem toBool_true_of_ne_nil {v : SExpr} (h : v ≠ SExpr.nil) :
    Logic.toBool v = true := by cases v <;> simp_all [Logic.toBool]

/-- `toBool` of nil is `false`. -/
theorem toBool_false_of_nil {v : SExpr} (h : v = SExpr.nil) :
    Logic.toBool v = false := by subst h; rfl

/-- A truthy `not` pins its argument to nil. -/
theorem arg_nil_of_not_truthy {v : SExpr} (h : Logic.not v ≠ SExpr.nil) :
    v = SExpr.nil := by
  cases v <;> simp_all [Logic.not, Logic.toBool]

/-- A `not` valued exactly `t` pins its argument to nil. -/
theorem arg_nil_of_not_t {v : SExpr} (h : Logic.not v = SExpr.t) :
    v = SExpr.nil := by
  cases v <;> simp_all [Logic.not, Logic.toBool, SExpr.t]

/-- A nil `not` pins its argument truthy. -/
theorem arg_truthy_of_not_nil {v : SExpr} (h : Logic.not v = SExpr.nil) :
    v ≠ SExpr.nil := by
  cases v <;> simp_all [Logic.not, Logic.toBool, SExpr.t]

/-- Two value characterizations of the SAME evaluation pin the same value. -/
theorem val_unique {a : Nat → Option SExpr} {u v : SExpr}
    (hu : ∃ N, ∀ f ≥ N, a f = some u) (hv : ∃ N, ∀ f ≥ N, a f = some v) : u = v := by
  obtain ⟨n1, h1⟩ := hu; obtain ⟨n2, h2⟩ := hv
  exact Option.some.inj ((h1 (n1+n2) (by omega)).symm.trans (h2 (n1+n2) (by omega)))

/-- Transport non-nil-ness along a value equation. -/
theorem ne_nil_of_eq {v w : SExpr} (h : v = w) (hw : w ≠ SExpr.nil) :
    v ≠ SExpr.nil := h ▸ hw

/-- A value equal to `t` is non-nil. -/
theorem ne_nil_of_eq_t {v : SExpr} (h : v = SExpr.t) : v ≠ SExpr.nil := by
  subst h; simp [SExpr.t]

/-- A nil argument makes `not` exactly `t`. -/
theorem not_t_of_nil {v : SExpr} (h : v = SExpr.nil) :
    Logic.not v = SExpr.t := by subst h; rfl

/-- A truthy argument makes `not` nil. -/
theorem not_nil_of_truthy {v : SExpr} (h : v ≠ SExpr.nil) :
    Logic.not v = SExpr.nil := by
  cases v <;> simp_all [Logic.not, Logic.toBool]

/-- Reduce a `cond` value by a known-true test. -/
theorem cond_val_true {b : Bool} {x y : SExpr} (h : b = true) :
    (bif b then x else y) = x := by subst h; rfl

/-- Reduce a `cond` value by a known-false test. -/
theorem cond_val_false {b : Bool} {x y : SExpr} (h : b = false) :
    (bif b then x else y) = y := by subst h; rfl

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
      (.cons (.atom (.symbol { name := "if" }))
        (.cons A (.cons
          (.cons (.atom (.symbol { name := "quote" })) (.cons SExpr.t .nil))
          (.cons (.cons (.atom (.symbol { name := "quote" })) (.cons .nil .nil))
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
      (.cons (.atom (.symbol { name := "if" })) (.cons c (.cons thn (.cons els .nil))))
      (.cons (.atom (.symbol { name := "if" })) (.cons c (.cons thn' (.cons els .nil)))) := by
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
      (.cons (.atom (.symbol { name := "if" })) (.cons c (.cons thn (.cons els .nil))))
      (.cons (.atom (.symbol { name := "if" })) (.cons c (.cons thn (.cons els' .nil)))) := by
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
        (.cons (.atom (.symbol { name := "if" })) (.cons c (.cons thn (.cons els .nil))))
      = evalOpt f w env
        (.cons (.atom (.symbol { name := "if" })) (.cons c' (.cons thn (.cons els .nil)))) := by
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

/-- Transport exact truth BACKWARDS along an iff: the chain's end is `some t`,
    so the chain's start is TRUTHY (its value need not be `t`). -/
theorem truthy_of_evrel_siff {w : World} {env : Env} {a b : SExpr}
    (hab : EvRel SIff w env a b)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env b = some SExpr.t) :
    ∃ N, ∀ f ≥ N, ∃ u, evalOpt f w env a = some u ∧ u ≠ SExpr.nil := by
  obtain ⟨n1, hab⟩ := hab; obtain ⟨n2, hb⟩ := hb
  refine ⟨n1 + n2, fun f hf => ?_⟩
  obtain ⟨u, v, hau, hbv, huv⟩ := hab f (by omega)
  have : v = SExpr.t := Option.some.inj ((hbv.symm.trans (hb f (by omega))))
  refine ⟨u, hau, fun hnu => ?_⟩
  have hvnil : v = SExpr.nil := Iff.mp huv hnu
  simp_all [SExpr.t]

/-- Strengthen truthiness to `= some t` at a pinned BOOLEAN value (the chain
    start's head is boolean-valued, e.g. `implies`). G2's `EvTrue` migration
    removes the need for this. -/
theorem eq_t_of_truthy_boolean {w : World} {env : Env} {a va : SExpr}
    (hconv : ∃ N, ∀ f ≥ N, evalOpt f w env a = some va)
    (hbool : va = SExpr.t ∨ va = SExpr.nil)
    (htruthy : ∃ N, ∀ f ≥ N, ∃ u, evalOpt f w env a = some u ∧ u ≠ SExpr.nil) :
    ∃ N, ∀ f ≥ N, evalOpt f w env a = some SExpr.t := by
  obtain ⟨n1, hconv⟩ := hconv; obtain ⟨n2, htruthy⟩ := htruthy
  refine ⟨n1 + n2, fun f hf => ?_⟩
  obtain ⟨u, hau, hnu⟩ := htruthy f (by omega)
  have hva : u = va := Option.some.inj ((hau.symm.trans (hconv f (by omega))))
  rcases hbool with h | h
  · rwa [hva, h] at hau
  · exact absurd (hva.trans h) hnu

/-- `Logic.implies` is boolean-valued (the chain-start head fact). -/
theorem logic_implies_boolean (p q : SExpr) :
    Logic.implies p q = SExpr.t ∨ Logic.implies p q = SExpr.nil := by
  rw [logic_implies_cond]
  cases Logic.toBool p <;> cases Logic.toBool q <;> simp


/-- Extract `integerp v = t` from a TRUE type-prescription corollary of the
    standard `(IF (INTEGERP v) … 'NIL)` shape (lifted: `cond (toBool (integerp v))
    X nil = t`): the recognizer is two-valued, and a false test would make the
    cond `nil ≠ t`. -/
theorem tp_cond_integerp_t (v X : SExpr)
    (h : cond (Logic.toBool (Logic.integerp v)) X SExpr.nil = SExpr.t) :
    Logic.integerp v = SExpr.t := by
  match v with
  | .atom (.number (.int _)) => rfl
  | .atom (.number (.rational _ _)) => simp [Logic.integerp, Logic.toBool, SExpr.t] at h
  | .atom (.number (.decimal _ _)) => simp [Logic.integerp, Logic.toBool, SExpr.t] at h
  | .atom (.symbol _) => simp [Logic.integerp, Logic.toBool, SExpr.t] at h
  | .atom (.keyword _) => simp [Logic.integerp, Logic.toBool, SExpr.t] at h
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

/-- EXTRACT the else-branch's convergence from a converged `if` with a nil test
    (the induction scaffold's per-case step: the case fact discharges the case
    literal, leaving the pushed clause). -/
theorem re_extract_else (w : World) (env : Env) (c t e : SExpr) (r : SExpr)
    (hif : ∃ N, ∀ f ≥ N,
      evalOpt f w env
        (.cons (.atom (.symbol { name := "if" })) (.cons c (.cons t (.cons e .nil))))
      = some r)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some .nil) :
    ∃ N, ∀ f ≥ N, evalOpt f w env e = some r := by
  obtain ⟨Ni, hi⟩ := hif; obtain ⟨Nc, hc⟩ := hc
  refine ⟨max Ni Nc + 1, fun f hf => ?_⟩
  have heq := evalOpt_if_false f w env c t e (hc f (by omega))
  have := hi (f + 1) (by omega)
  rw [heq] at this
  exact this

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
  | .atom (.number (.rational _ _)) => simp [Logic.integerp, SExpr.t] at h
  | .atom (.number (.decimal _ _)) => simp [Logic.integerp, SExpr.t] at h
  | .atom (.symbol _) => simp [Logic.integerp, SExpr.t] at h
  | .atom (.keyword _) => simp [Logic.integerp, SExpr.t] at h
  | .atom (.string _) => simp [Logic.integerp, SExpr.t] at h
  | .nil => simp [Logic.integerp, SExpr.t] at h
  | .cons _ _ => simp [Logic.integerp, SExpr.t] at h

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
        (.cons (.atom (.symbol { name := "if" })) (.cons c (.cons t (.cons e .nil))))
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
        (.cons (.atom (.symbol { name := "if" })) (.cons c (.cons t (.cons e .nil))))
      = some v := by
  obtain ⟨Nc, cv, hc⟩ := hc
  obtain ⟨Nt, tv, ht⟩ := ht
  obtain ⟨Ne, ev, he⟩ := he
  obtain ⟨N, h⟩ := re_val_if w env c t e cv tv ev ⟨Nc, hc⟩ ⟨Nt, ht⟩ ⟨Ne, he⟩
  exact ⟨N, cond (Logic.toBool cv) tv ev, h⟩

end ACL2.Replay
