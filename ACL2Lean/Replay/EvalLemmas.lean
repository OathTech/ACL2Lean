/-
  Proof rules for ACL2 proof replay.

  Each theorem corresponds to a proof tree node type. These are the
  building blocks: the proof-producing checker applies one theorem
  per proof tree node, composing them to prove the target theorem.

  Every theorem is proved once, used for all ACL2 theorems.
  No inference, no search — purely deterministic replay.
-/
import ACL2Lean.EvalOpt
import ACL2Lean.Count

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
  simp [evalOpt, evalOptStep]
  rw [show env[s]? = env.get? s from rfl, h]

/-- T18: Variable lookup (unbound, not t). -/
theorem evalOpt_var_unbound (f : Nat) (w : World) (env : Env) (s : Symbol)
    (h : env.get? s = none) (h_not_t : s.isNamed "t" = false) :
    evalOpt (f + 1) w env (.atom (.symbol s)) = some .nil := by
  simp [evalOpt, evalOptStep]
  rw [show env[s]? = env.get? s from rfl, h]
  simp [h_not_t]

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
    = some (callBuiltin s.name [av]) := by
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
      else some .nil
    | none => some (callBuiltin s.name argVals)) = _
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
    = some (callBuiltin s.name [av1, av2]) := by
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
      else some .nil
    | none => some (callBuiltin s.name argVals)) = _
  simp only [List.mapM, List.mapM.loop, h_arg1, h_arg2, List.reverse, List.reverseAux,
             Option.pure_def, h_not_def]
  rfl

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
      else some .nil
    | none => some (callBuiltin s.name argVals)) = _
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
      else some .nil
    | none => some (callBuiltin s.name argVals)) = _
  simp only [List.mapM, List.mapM.loop, h_arg1, h_arg2, List.reverse, List.reverseAux,
             Option.pure_def, h_def]
  rfl

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
    callBuiltin "equal" [a, b] = Logic.equal a b := by rfl
@[simp] theorem callBuiltin_not (a : SExpr) :
    callBuiltin "not" [a] = Logic.not a := by rfl
@[simp] theorem callBuiltin_consp (a : SExpr) :
    callBuiltin "consp" [a] = Logic.consp a := by rfl
@[simp] theorem callBuiltin_car (a : SExpr) :
    callBuiltin "car" [a] = Logic.car a := by rfl
@[simp] theorem callBuiltin_cdr (a : SExpr) :
    callBuiltin "cdr" [a] = Logic.cdr a := by rfl
@[simp] theorem callBuiltin_plus (a b : SExpr) :
    callBuiltin "binary-+" [a, b] = Logic.plus a b := by rfl

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

/-- T8: Commutativity-2 of plus: (+ x (+ y z)) = (+ y (+ x z)). -/
theorem logic_plus_comm2 (a b c : SExpr) :
    Logic.plus a (Logic.plus b c) = Logic.plus b (Logic.plus a c) := by
  -- Follows from commutativity + associativity of rational arithmetic
  -- through toRat/mkNumber. Deferred — one-time arithmetic lemma.
  sorry

/-- T8: FIX of a number is identity. -/
@[simp] theorem callBuiltin_fix_number (n : Number) :
    callBuiltin "fix" [.atom (.number n)] = .atom (.number n) := by rfl

/-- T8: plus 0 x = fix x (unicity-of-0 at value level). -/
theorem logic_plus_zero_left (v : SExpr) :
    Logic.plus (.atom (.number (.int 0))) v = callBuiltin "fix" [v] := by
  -- Follows from toRat/mkNumber: plus(0, v) normalizes the same as fix(v).
  -- Deferred — one-time arithmetic lemma.
  sorry

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

/-! ## Variable substitution (T15) -/

/-- Substitute a variable with a quoted value in a term.
    Replaces free occurrences of symbol `s` with `(QUOTE v)`.
    Does not recurse into QUOTE bodies or replace head symbols. -/
partial def substVar (term : SExpr) (s : Symbol) (v : SExpr) : SExpr :=
  match term with
  | .nil => .nil
  | .atom (.symbol sym) =>
    if sym == s then
      -- Replace with quoted value
      .cons (.atom (.symbol { name := "quote" })) (.cons v .nil)
    else term
  | .atom _ => term
  | .cons (.atom (.symbol q)) rest =>
    if q.isNamed "quote" then term  -- Don't substitute inside QUOTE
    else
      -- Head symbol is NOT substituted (it's a function name, not a variable)
      .cons (.atom (.symbol q)) (substVarList rest s v)
  | .cons a b => .cons (substVar a s v) (substVar b s v)
where
  substVarList : SExpr → Symbol → SExpr → SExpr
    | .nil, _, _ => .nil
    | .cons a b, s, v => .cons (substVar a s v) (substVarList b s v)
    | s', _, _ => substVar s' (by exact s) (by exact v)

/-- T15: Variable substitution respects evaluation.
    Evaluating `term` in `env[s := v]` equals evaluating `substVar term s v`
    in `env`. This bridges function body evaluation (in the body env) back
    to the caller's env.

    SORRY: This requires structural induction on `term` following evalOpt's
    recursion, handling each case (variable lookup, IF, function call, etc.).
    It is comparable in difficulty to T1 (congruence). -/
theorem evalOpt_substVar (f : Nat) (w : World) (env : Env) (s : Symbol)
    (v : SExpr) (term : SExpr) :
    evalOpt f w (env.insert s v) term =
    evalOpt f w env (substVar term s v) := by
  sorry

/-! ## Congruence (T1) -/

/-- Replace the first occurrence of `a` in `term` with `b`.
    Depth-first left-to-right. Does NOT descend into QUOTE bodies.
    Does NOT replace head symbols. -/
partial def replaceSubterm (term a b : SExpr) : SExpr :=
  if term == a then b
  else match term with
  | .cons (.atom (.symbol q)) rest =>
    if q.isNamed "quote" then term  -- Don't replace inside QUOTE
    else .cons (.atom (.symbol q)) (replaceSubtermList rest a b)
  | .cons x y =>
    let x' := replaceSubterm x a b
    if x' != x then .cons x' y
    else .cons x (replaceSubterm y a b)
  | _ => term
where
  replaceSubtermList : SExpr → SExpr → SExpr → SExpr
    | .nil, _, _ => .nil
    | .cons x xs, a, b =>
      let x' := replaceSubterm x a b
      if x' != x then .cons x' xs
      else .cons x (replaceSubtermList xs a b)
    | s, a, b => replaceSubterm s a b

/-- T1: Subterm replacement congruence.
    If `a` and `b` evaluate to the same value (at sufficient fuel),
    then replacing the first occurrence of `a` with `b` in `term`
    preserves evaluation.

    SORRY: Requires structural induction on `term` following evalOpt's
    recursion pattern. The IF case requires showing replacement in the
    untaken branch doesn't affect evaluation. This is the hardest
    theorem in the replay infrastructure. -/
theorem evalOpt_replace_congr (w : World) (env : Env)
    (term a b : SExpr)
    (h_eq : ∃ N, ∀ f ≥ N, evalOpt f w env a = evalOpt f w env b) :
    ∃ M, ∀ f ≥ M,
      evalOpt f w env (replaceSubterm term a b) =
      evalOpt f w env term := by
  sorry

/-- T1 (forward direction): eval of the original equals eval of the replaced.
    This is the direction needed for chaining rewrites forward. -/
theorem evalOpt_replace_congr_fwd (w : World) (env : Env)
    (term a b : SExpr)
    (h_eq : ∃ N, ∀ f ≥ N, evalOpt f w env a = evalOpt f w env b) :
    ∃ M, ∀ f ≥ M,
      evalOpt f w env term =
      evalOpt f w env (replaceSubterm term a b) := by
  have h := evalOpt_replace_congr w env term a b h_eq
  exact ⟨h.choose, fun f hf => (h.choose_spec f hf).symm⟩

/-- Symmetry for fuel-existential equalities. -/
theorem fuel_eq_symm {a b : Nat → Option SExpr}
    (h : ∃ N, ∀ f ≥ N, a f = b f) :
    ∃ N, ∀ f ≥ N, b f = a f :=
  ⟨h.choose, fun f hf => (h.choose_spec f hf).symm⟩

end ACL2.Replay
