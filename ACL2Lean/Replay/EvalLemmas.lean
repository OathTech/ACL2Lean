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

/-- Variable convergence: any symbol evaluates to some value at fuel ≥ 1.
    The value depends on the env but convergence is unconditional. -/
theorem evalOpt_symbol_converges (f : Nat) (w : World) (env : Env) (s : Symbol) :
    ∃ v, evalOpt (f + 1) w env (.atom (.symbol s)) = some v := by
  simp [evalOpt, evalOptStep]
  match h : env[s]? with
  | some v => exact ⟨v, by rfl⟩
  | none =>
    simp
    match ht : s.isNamed "t" with
    | true => exact ⟨SExpr.t, by rfl⟩
    | false => exact ⟨.nil, by rfl⟩

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

/-- `mkNumber` with denominator 1 yields the plain integer. -/
theorem mkNumber_one (n : Int) :
    Logic.mkNumber n 1 = .atom (.number (.int n)) := by
  simp [Logic.mkNumber]

/-- T8: Commutativity-2 of plus, integer form: (+ a (+ b c)) = (+ b (+ a c)).

    Stated for integer arguments. The general rational statement is also
    true but requires reasoning about `mkNumber`'s gcd-normalization
    (value-level ℚ equality); deferred until non-integer arithmetic appears
    in the corpus. The sorting books' recursion produces only integers. -/
theorem logic_plus_comm2_int (a b c : Int) :
    Logic.plus (.atom (.number (.int a)))
      (Logic.plus (.atom (.number (.int b))) (.atom (.number (.int c))))
    = Logic.plus (.atom (.number (.int b)))
      (Logic.plus (.atom (.number (.int a))) (.atom (.number (.int c)))) := by
  simp [Logic.plus, Logic.toRat, mkNumber_one]
  omega

/-- T8: FIX of a number is identity. -/
@[simp] theorem callBuiltin_fix_number (n : Number) :
    callBuiltin "fix" [.atom (.number n)] = .atom (.number n) := by rfl

/-- T8: unicity-of-0, integer form: (+ 0 k) = k.

    Stated for integer `k`. The general `plus 0 v = fix v` (∀ v) is FALSE
    in this model: `plus` normalizes via `mkNumber` (2/4 → 1/2, 5/0 → 0)
    whereas `fix` returns `v` unchanged — they agree only on canonical
    numbers. ACL2 numbers are always canonical and `my-len` returns
    integers, so the integer form is what the replay needs. -/
theorem logic_plus_zero_left_int (k : Int) :
    Logic.plus (.atom (.number (.int 0))) (.atom (.number (.int k)))
    = .atom (.number (.int k)) := by
  simp [Logic.plus, Logic.toRat, mkNumber_one]

/-- T8: integer addition: (+ a b) = a + b for integer arguments. -/
theorem logic_plus_int (a b : Int) :
    Logic.plus (.atom (.number (.int a))) (.atom (.number (.int b)))
    = .atom (.number (.int (a + b))) := by
  simp [Logic.plus, Logic.toRat, mkNumber_one]

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

/-\! ## Congruence (T1): one-step argument congruence

    The proof producer descends the term structure at meta-level, so the
    only congruence lemma it needs is a SINGLE step: replacing one argument
    of a function call with an eventually-equal term. This is stated in
    existential-equality form (transitive, composes via `fuel_chain_eq`),
    needs no `pcEq`/`EvalCtx`/`replaceSubterm`, and is sound for recursive
    subterms (no concrete fuel bound required). -/

/-- Round-trip: `toList?` of `ofList` gives back the list. -/
@[simp] theorem SExpr.ofList_toList? (l : List SExpr) :
    (SExpr.ofList l).toList? = some l := by
  induction l with
  | nil => simp [SExpr.ofList, SExpr.toList?]
  | cons x xs ih => simp [SExpr.ofList, SExpr.toList?, ih]

/-- `mapM` agrees when one element's image agrees. -/
theorem mapM_eq_of_single {α β : Type} {g : α → Option β}
    (l1 l2 : List α) (a b : α) (hab : g a = g b) :
    (l1 ++ a :: l2).mapM g = (l1 ++ b :: l2).mapM g := by
  induction l1 with
  | nil => simp only [List.nil_append, List.mapM_cons, hab]
  | cons x xs ih => simp only [List.cons_append, List.mapM_cons, ih]

/-- One-step argument congruence: if `a` and `b` are eventually-equal, then
    a function call with `a` at one argument position is eventually-equal to
    the same call with `b` there. `s` must be a non-special symbol (a user
    function or builtin — not quote/if/let). -/
theorem evalOpt_arg_congr (w : World) (env : Env) (s : Symbol)
    (before after : List SExpr) (a b : SExpr)
    (h_nq : s.isNamed "quote" = false) (h_ni : s.isNamed "if" = false)
    (h_nl : s.isNamed "let" = false) (h_nl2 : s.isNamed "let*" = false)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env a = evalOpt f w env b) :
    ∃ M, ∀ f ≥ M,
      evalOpt f w env (.cons (.atom (.symbol s)) (SExpr.ofList (before ++ a :: after))) =
      evalOpt f w env (.cons (.atom (.symbol s)) (SExpr.ofList (before ++ b :: after))) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hg : g ≥ N := by omega
  show evalOptStep (evalOpt g) w env _ = evalOptStep (evalOpt g) w env _
  simp only [evalOptStep_cons_symbol, h_nq, h_ni, h_nl, h_nl2]
  simp only [Bool.false_eq_true, if_false, Bool.or_self, SExpr.ofList_toList?]
  rw [mapM_eq_of_single before after a b (hN g hg)]

/-- Unary specialization: congruence in the sole argument of `(s a)`. -/
theorem evalOpt_cong_unary (w : World) (env : Env) (s : Symbol) (a b : SExpr)
    (h_nq : s.isNamed "quote" = false) (h_ni : s.isNamed "if" = false)
    (h_nl : s.isNamed "let" = false) (h_nl2 : s.isNamed "let*" = false)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env a = evalOpt f w env b) :
    ∃ M, ∀ f ≥ M, evalOpt f w env (.cons (.atom (.symbol s)) (.cons a .nil))
                = evalOpt f w env (.cons (.atom (.symbol s)) (.cons b .nil)) :=
  evalOpt_arg_congr w env s [] [] a b h_nq h_ni h_nl h_nl2 h

/-- Binary specialization: congruence in the FIRST argument of `(s a c)`. -/
theorem evalOpt_cong_bin1 (w : World) (env : Env) (s : Symbol) (a b c : SExpr)
    (h_nq : s.isNamed "quote" = false) (h_ni : s.isNamed "if" = false)
    (h_nl : s.isNamed "let" = false) (h_nl2 : s.isNamed "let*" = false)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env a = evalOpt f w env b) :
    ∃ M, ∀ f ≥ M, evalOpt f w env (.cons (.atom (.symbol s)) (.cons a (.cons c .nil)))
                = evalOpt f w env (.cons (.atom (.symbol s)) (.cons b (.cons c .nil))) :=
  evalOpt_arg_congr w env s [] [c] a b h_nq h_ni h_nl h_nl2 h

/-- Binary specialization: congruence in the SECOND argument of `(s c a)`. -/
theorem evalOpt_cong_bin2 (w : World) (env : Env) (s : Symbol) (c a b : SExpr)
    (h_nq : s.isNamed "quote" = false) (h_ni : s.isNamed "if" = false)
    (h_nl : s.isNamed "let" = false) (h_nl2 : s.isNamed "let*" = false)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env a = evalOpt f w env b) :
    ∃ M, ∀ f ≥ M, evalOpt f w env (.cons (.atom (.symbol s)) (.cons c (.cons a .nil)))
                = evalOpt f w env (.cons (.atom (.symbol s)) (.cons c (.cons b .nil))) :=
  evalOpt_arg_congr w env s [c] [] a b h_nq h_ni h_nl h_nl2 h

/-! ### Call congruence across envs (induction-hypothesis bridge)

    Two calls to the same defined function whose arguments evaluate to the
    SAME values — even in different environments or from different argument
    expressions — are eventually-equal, because both definition-expand to
    evaluating the same `bindArgs` body. This is what connects an inductive
    hypothesis (stated at one binding of the recursion variable) to the
    recursive subterm in the goal (at another binding), WITHOUT a general
    substitution lemma. -/

/-- IH bridge, 1-ary defined function. -/
theorem evalOpt_defn1_call_congr (w : World) (E1 E2 : Env) (s : Symbol)
    (f1 : Symbol) (body : SExpr) (A C : SExpr) (av : SExpr)
    (h_ns : s.isNamed "quote" = false ∧ s.isNamed "if" = false ∧
            s.isNamed "let" = false ∧ s.isNamed "let*" = false)
    (h_def : w.defs.get? s = some ([f1], body))
    (hA : ∃ N, ∀ f ≥ N, evalOpt f w E1 A = some av)
    (hC : ∃ N, ∀ f ≥ N, evalOpt f w E2 C = some av) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w E1 (.cons (.atom (.symbol s)) (.cons A .nil))
        = evalOpt f w E2 (.cons (.atom (.symbol s)) (.cons C .nil)) := by
  obtain ⟨Na, ha⟩ := hA; obtain ⟨Nc, hc⟩ := hC
  refine ⟨max Na Nc + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [evalOpt_defn_1 g w E1 s A av f1 body h_ns h_def (ha g (by omega)),
      evalOpt_defn_1 g w E2 s C av f1 body h_ns h_def (hc g (by omega))]

/-- IH bridge, 2-ary defined function. -/
theorem evalOpt_defn2_call_congr (w : World) (E1 E2 : Env) (s : Symbol)
    (f1 f2 : Symbol) (body : SExpr) (A B C D : SExpr) (av bv : SExpr)
    (h_ns : s.isNamed "quote" = false ∧ s.isNamed "if" = false ∧
            s.isNamed "let" = false ∧ s.isNamed "let*" = false)
    (h_def : w.defs.get? s = some ([f1, f2], body))
    (hA : ∃ N, ∀ f ≥ N, evalOpt f w E1 A = some av)
    (hB : ∃ N, ∀ f ≥ N, evalOpt f w E1 B = some bv)
    (hC : ∃ N, ∀ f ≥ N, evalOpt f w E2 C = some av)
    (hD : ∃ N, ∀ f ≥ N, evalOpt f w E2 D = some bv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w E1 (.cons (.atom (.symbol s)) (.cons A (.cons B .nil)))
        = evalOpt f w E2 (.cons (.atom (.symbol s)) (.cons C (.cons D .nil))) := by
  obtain ⟨Na, ha⟩ := hA; obtain ⟨Nb, hb⟩ := hB
  obtain ⟨Nc, hc⟩ := hC; obtain ⟨Nd, hd⟩ := hD
  refine ⟨max (max Na Nb) (max Nc Nd) + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [evalOpt_defn_2 g w E1 s A B av bv f1 f2 body h_ns h_def (ha g (by omega)) (hb g (by omega)),
      evalOpt_defn_2 g w E2 s C D av bv f1 f2 body h_ns h_def (hc g (by omega)) (hd g (by omega))]

/-- IH bridge, 2-ary builtin (not in world.defs). Same idea as the defn
    version: both calls reduce to `callBuiltin s [av, bv]`. Used to bridge the
    `BINARY-+` side of an inductive hypothesis across environments. -/
theorem evalOpt_builtin2_call_congr (w : World) (E1 E2 : Env) (s : Symbol)
    (A B C D : SExpr) (av bv : SExpr)
    (h_ns : s.isNamed "quote" = false ∧ s.isNamed "if" = false ∧
            s.isNamed "let" = false ∧ s.isNamed "let*" = false)
    (h_nodef : w.defs.get? s = none)
    (hA : ∃ N, ∀ f ≥ N, evalOpt f w E1 A = some av)
    (hB : ∃ N, ∀ f ≥ N, evalOpt f w E1 B = some bv)
    (hC : ∃ N, ∀ f ≥ N, evalOpt f w E2 C = some av)
    (hD : ∃ N, ∀ f ≥ N, evalOpt f w E2 D = some bv) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w E1 (.cons (.atom (.symbol s)) (.cons A (.cons B .nil)))
        = evalOpt f w E2 (.cons (.atom (.symbol s)) (.cons C (.cons D .nil))) := by
  obtain ⟨Na, ha⟩ := hA; obtain ⟨Nb, hb⟩ := hB
  obtain ⟨Nc, hc⟩ := hC; obtain ⟨Nd, hd⟩ := hD
  refine ⟨max (max Na Nb) (max Nc Nd) + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [evalOpt_builtin_2 g w E1 s A B av bv h_ns h_nodef (ha g (by omega)) (hb g (by omega)),
      evalOpt_builtin_2 g w E2 s C D av bv h_ns h_nodef (hc g (by omega)) (hd g (by omega))]

end ACL2.Replay
