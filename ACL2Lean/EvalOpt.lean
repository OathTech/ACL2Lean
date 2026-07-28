/-
  ACL2 evaluator: the semantic definition of what ACL2 terms mean.

  Returns `Option SExpr`: `none` = fuel exhaustion, `some v` = value.
  This distinction is critical for soundness proofs — it avoids conflating
  fuel exhaustion with legitimate nil results.

  The evaluator is factored into `evalOptStep` (non-recursive body) and
  `evalOpt` (fuel-bounded recursion calling evalOptStep). This factoring
  makes fuel monotonicity provable without fighting Lean's term reduction.
-/
import ACL2Lean.Syntax
import ACL2Lean.Logic
import ACL2Lean.Parser
import ACL2Lean.Lexorder

namespace ACL2

/-- Bind function formals to argument values, producing a new environment. -/
def bindArgs : List Symbol → List SExpr → Env
  | f :: fs, v :: vs => (bindArgs fs vs).insert f v
  | _, _ => {}  -- ⚠ silent default on formals/args length mismatch (no hard-fail); see callBuiltin note

/-- Bind formals to values OVER an existing environment (lambda application:
    lexical extension; see the LAMBDA arm's comment). Same shape as
    `bindArgs`, seeded with `env` instead of `{}`. -/
def bindArgsOver (env : Env) : List Symbol → List SExpr → Env
  | f :: fs, v :: vs => (bindArgsOver env fs vs).insert f v
  | _, _ => env

/-- The formals of a translated lambda: a proper list of symbols, or `none`
    (a malformed binder is a frontier — never a default). Named so the
    interpreter's LAMBDA arm and the replay's scoping certificate speak of
    the SAME symbol list. -/
def lamFormals? (formalsE : SExpr) : Option (List Symbol) :=
  match formalsE.toList? with
  | some l => l.mapM (fun fm =>
      match fm with
      | .atom (.symbol fs) => some fs
      | _ => none)
  | none => none

/-- Dispatch an ACL2 built-in primitive by normalized name, modeling ACL2's
    LOGICAL (total) semantics. Returns `none` for a primitive we do not yet model
    or a wrong arity — a frontier the evaluator surfaces as non-convergence rather
    than silently returning a wrong value (`nil`). A genuinely undefined function
    cannot occur in a faithfully-translated admitted term (ACL2's translate
    rejects it); an unmodeled-but-real primitive (`numerator`, `integer-abs`, …)
    must be added here with its faithful value, not left to default. -/
def callBuiltin (name : String) (args : List SExpr) : Option SExpr :=
  match name, args with
  | "CONS", [a, b] => some (.cons a b)
  | "CAR", [a] => some (Logic.car a)
  | "CDR", [a] => some (Logic.cdr a)
  | "CONSP", [a] => some (Logic.consp a)
  | "ATOM", [a] => some (Logic.atom a)
  | "ENDP", [a] => some (Logic.endp a)
  | "EQUAL", [a, b] => some (Logic.equal a b)
  | "EQL", [a, b] => some (Logic.equal a b)
  | "NOT", [a] => some (Logic.not a)
  | "BINARY-+", [a, b] => some (Logic.plus a b)
  | "BINARY-*", [a, b] => some (Logic.times a b)
  | "UNARY--", [a] =>
      let (n, d) := Logic.toRat a
      some (Logic.mkNumber (-n) d)
  | "UNARY-/", [a] =>
      let (n, d) := Logic.toRat a
      some (if n == 0 then .atom (.number (.int 0))
        else if n > 0 then Logic.mkNumber (Int.ofNat d) n.natAbs
        else Logic.mkNumber (-(Int.ofNat d)) n.natAbs)
  | "+", [a, b] => some (Logic.plus a b)
  | "-", [a] =>
      let (n, d) := Logic.toRat a
      some (Logic.mkNumber (-n) d)
  | "-", [a, b] => some (Logic.minus a b)
  | "*", [a, b] => some (Logic.times a b)
  | "1+", [a] => some (Logic.plus (.atom (.number (.int 1))) a)
  | "1-", [a] => some (Logic.minus a (.atom (.number (.int 1))))
  | "<", [a, b] => some (Logic.lt a b)
  | "INTEGERP", [a] => some (Logic.integerp a)
  | "NATP", [a] => some (Logic.natp a)
  | "POSP", [a] => some (Logic.posp a)
  | "RATIONALP", [a] =>
      some (match a with | .atom (.number _) => .t | _ => .nil)
  | "ACL2-NUMBERP", [a] =>
      some (match a with | .atom (.number _) => .t | _ => .nil)
  | "ZP", [a] => some (Logic.zp a)
  | "SYMBOLP", [a] => some (Logic.symbolp a)
  | "BOOLEANP", [a] => some (Logic.booleanp a)
  | "STRINGP", [a] => some (Logic.stringp a)
  | "CHARACTERP", [a] => some (Logic.characterp a)
  | "CHAR-CODE", [a] => some (Logic.charCode a)
  | "CODE-CHAR", [a] => some (Logic.codeChar a)
  | "FIX", [a] => some (Logic.fix a)
  | "NFIX", [a] => some (Logic.nfix a)
  | "IFIX", [a] =>
      some (match a with | .atom (.number (.int _)) => a | _ => .atom (.number (.int 0)))
  | "IMPLIES", [a, b] => some (Logic.implies a b)
  | "IFF", [a, b] => some (Logic.iff a b)
  | "TRUE-LISTP", [a] => some (Logic.trueListp a)
  | "LEN", [a] => some (Logic.len a)
  | "LEXORDER", [a, b] => some (lexorder a b)
  | "EVENP", [a] => some (Logic.evenp a)
  | "ODDP", [a] => some (Logic.oddp a)
  | "EXPT", [a, b] => some (Logic.expt a b)
  | "STRING-APPEND", [a, b] => some (Logic.string_append a b)
  | "NUMERATOR", [a] => some (Logic.numerator a)
  | "DENOMINATOR", [a] => some (Logic.denominator a)
  | "REALPART", [a] => some (Logic.realpart a)
  | "IMAGPART", [a] => some (Logic.imagpart a)
  | "COMPLEX-RATIONALP", [a] => some (Logic.complexRationalp a)
  | "COERCE", [a, b] => some (Logic.coerce a b)
  | "LIST", xs => some (SExpr.ofList xs)
  | "FORCE", [a] => some a
  | "DOUBLE-REWRITE", [a] => some a
  | "HIDE", [a] => some a
  | _, _ => none

/-- Every name `callBuiltin` dispatches — one entry per match arm above,
    KEPT IN SYNC (enforced by `scripts/check-no-shadow.sh` in `just ci`,
    which scrapes both and diffs). This is the NO-SHADOW exclusion set
    (design D3/D2): a ground-zero snapshot defun whose name is listed here
    must NOT become a `World` entry — world-first dispatch (`evalOptStep`)
    would shadow the builtin, changing fuel profiles (e.g. `LEN` via a
    world body recurses per element where `Logic.len` is one step) and
    falsifying the `hnew` side condition of `evalOpt_world_mono`. Such fns
    take the D4 definition-fact route instead. -/
def builtinNames : List String :=
  ["CONS", "CAR", "CDR", "CONSP", "ATOM", "ENDP", "EQUAL", "EQL", "NOT",
   "BINARY-+", "BINARY-*", "UNARY--", "UNARY-/", "+", "-", "*", "1+", "1-",
   "<", "INTEGERP", "NATP", "POSP", "RATIONALP", "ACL2-NUMBERP", "ZP",
   "SYMBOLP", "BOOLEANP", "STRINGP", "CHARACTERP", "CHAR-CODE", "CODE-CHAR",
   "FIX", "NFIX", "IFIX", "IMPLIES", "IFF", "TRUE-LISTP", "LEN", "LEXORDER",
   "EVENP", "ODDP", "EXPT", "STRING-APPEND", "NUMERATOR", "DENOMINATOR",
   "REALPART", "IMAGPART", "COMPLEX-RATIONALP", "COERCE",
   "LIST", "FORCE", "DOUBLE-REWRITE", "HIDE"]

/-- One step of the option-returning evaluator, parameterized by the
    recursive evaluator function. Factored out so that monotonicity
    can be proved about this non-recursive function directly.

    MALFORMED TERM SHAPES return `none` — fail-closed, indistinguishable
    from non-convergence, so no mirror theorem over a malformed term is
    provable (fail-closed audit 2026-07-06, F15; matches the already-`none`
    unknown-builtin/arity arms F13/F14). The one DELIBERATE total default
    that stays: an UNBOUND VARIABLE evaluates to `nil` (`t` to itself) —
    that is the total-env modeling choice the `∀ env` mirror-statement form
    relies on (an env that omits a theorem variable behaves as binding it
    to `nil`), mirroring ACL2's total logical semantics, NOT a fail-open
    default. -/
def evalOptStep (rec : World → Env → SExpr → Option SExpr)
    (w : World) (env : Env) (term : SExpr) : Option SExpr :=
  match term with
  | .nil => some .nil
  | .atom (.number n) => some (.atom (.number n))
  | .atom (.string s) => some (.atom (.string s))
  | .atom (.keyword k) => some (.atom (.keyword k))
  | .atom (.char c) => some (.atom (.char c))  -- characters self-evaluate
  | .atom (.symbol s) =>
      match env.get? s with
      | some v => some v
      | none =>
          if s.isNamed "T" then some SExpr.t
          else some .nil
  | .cons (.atom (.symbol s)) argsExpr =>
      if s.isNamed "QUOTE" then
        match argsExpr with
        | .cons v .nil => some v
        | _ => none
      else if s.isNamed "IF" then
        match argsExpr.toList? with
        | some [c, t, e] => do
            let cv ← rec w env c
            if Logic.toBool cv then rec w env t else rec w env e
        | _ => none
      else if s.isNamed "LET" || s.isNamed "LET*" then
        match argsExpr.toList? with
        | some [bindings, body] =>
            match bindings.toList? with
            | some bList => do
                -- `let*` is sequential (each value sees prior bindings: eval in `acc`);
                -- `let` is parallel (every value sees the outer env: eval in `env`).
                let env' ← bList.foldlM (fun acc b =>
                  match b.toList? with
                  | some [.atom (.symbol var), valExpr] => do
                      let v ← rec w (if s.isNamed "LET*" then acc else env) valExpr
                      pure (acc.insert var v)
                  | _ => none) env
                rec w env' body
            | none => none
        | _ => none
      else
        match argsExpr.toList? with
        | some args => do
            let argVals ← args.mapM (fun a => rec w env a)
            match w.defs.get? s with
            | some (formals, body) =>
                if formals.length = argVals.length then
                  rec w (bindArgs formals argVals) body
                else none
            | none => callBuiltin s.name argVals
        | none => none
  | .cons (.cons (.atom (.symbol lam))
      (.cons formalsE (.cons lamBody .nil))) argsExpr =>
      -- ((LAMBDA (formals) body) actuals) — ACL2's TRANSLATED binding form
      -- (`let`/`mv-let` become lambda applications; S2 2026-07-24, pinned by
      -- Tests/differential/corpus/lambda.lisp). Actuals evaluate in the
      -- OUTER env (parallel binding); the body in the outer env EXTENDED by
      -- formals↦values. On a translated (closed) body this is observationally
      -- `ev`'s fresh `(pairlis$ formals args)`; on surface input it matches
      -- ACL2 because translate CLOSES an open lambda over its lexical scope
      -- (the nested-lambda differential pin caught the fresh-env variant
      -- diverging), and it is the same extension the surface LET arm uses.
      -- A non-LAMBDA cons head, malformed formals, or an arity mismatch is
      -- `none` — a frontier, never a default value.
      if lam.isNamed "LAMBDA" then
        match lamFormals? formalsE, argsExpr.toList? with
        | some formals, some args => do
            let argVals ← args.mapM (fun a => rec w env a)
            if formals.length = argVals.length then
              rec w (bindArgsOver env formals argVals) lamBody
            else none
        | _, _ => none
      else none
  | _ => none

/-- Equation lemma for evalOptStep on symbol-headed cons. -/
@[simp] theorem evalOptStep_cons_symbol (rec : World → Env → SExpr → Option SExpr)
    (w : World) (env : Env) (s : Symbol) (argsExpr : SExpr) :
    evalOptStep rec w env (.cons (.atom (.symbol s)) argsExpr) =
    if s.isNamed "QUOTE" then
      match argsExpr with
      | .cons v .nil => some v
      | _ => none
    else if s.isNamed "IF" then
      match argsExpr.toList? with
      | some [c, t, e] => do
          let cv ← rec w env c
          if Logic.toBool cv then rec w env t else rec w env e
      | _ => none
    else if s.isNamed "LET" || s.isNamed "LET*" then
      match argsExpr.toList? with
      | some [bindings, body] =>
          match bindings.toList? with
          | some bList => do
              let env' ← bList.foldlM (fun acc b =>
                match b.toList? with
                | some [.atom (.symbol var), valExpr] => do
                    let v ← rec w (if s.isNamed "LET*" then acc else env) valExpr
                    pure (acc.insert var v)
                | _ => none) env
              rec w env' body
          | none => none
      | _ => none
    else
      match argsExpr.toList? with
      | some args => do
          let argVals ← args.mapM (fun a => rec w env a)
          match w.defs.get? s with
          | some (formals, body) =>
              if formals.length = argVals.length then
                rec w (bindArgs formals argVals) body
              else none
          | none => callBuiltin s.name argVals
      | none => none := by
  rfl

/-- Equation lemma for evalOptStep on a LAMBDA application (the translated
    `let`; S2 2026-07-24). Mirrors the arm verbatim so downstream proofs can
    `show`/`simp only` their way into it. -/
@[simp] theorem evalOptStep_cons_lam (rec : World → Env → SExpr → Option SExpr)
    (w : World) (env : Env) (lam : Symbol) (formalsE lamBody argsExpr : SExpr) :
    evalOptStep rec w env
      (.cons (.cons (.atom (.symbol lam)) (.cons formalsE (.cons lamBody .nil))) argsExpr) =
    if lam.isNamed "LAMBDA" then
      match lamFormals? formalsE, argsExpr.toList? with
      | some formals, some args => do
          let argVals ← args.mapM (fun a => rec w env a)
          if formals.length = argVals.length then
            rec w (bindArgsOver env formals argVals) lamBody
          else none
      | _, _ => none
    else none := by
  rfl

/-- Option-returning ACL2 evaluator. `none` = fuel exhaustion.
    Structurally mirrors `eval` exactly. -/
def evalOpt (fuel : Nat) (w : World) (env : Env) (term : SExpr) : Option SExpr :=
  match fuel with
  | 0 => none
  | fuel + 1 => evalOptStep (evalOpt fuel) w env term

/-! ## Generic Option-monad monotonicity helpers -/

/-- If every element maps successfully under `f`, and `g` agrees with `f` on
    successful outputs, then `mapM g` also succeeds with the same result. -/
theorem List.mapM_option_mono {f g : α → Option β} {l : List α} {vs : List β}
    (hmono : ∀ a, a ∈ l → ∀ v, f a = some v → g a = some v)
    (h : l.mapM f = some vs) :
    l.mapM g = some vs := by
  induction l generalizing vs with
  | nil => simpa [List.mapM_nil] using h
  | cons x xs ih =>
    simp only [List.mapM_cons] at h ⊢
    cases hfx : f x with
    | none => simp [hfx] at h
    | some vx =>
      cases hfxs : List.mapM f xs with
      | none => simp [hfx, hfxs] at h
      | some vtl =>
        simp [hfx, hfxs] at h; subst h
        simp [hmono x (.head ..) vx hfx, ih (fun a ha => hmono a (.tail _ ha)) hfxs]

/-- If every step maps successfully under `f`, and `g` agrees with `f` on
    successful outputs, then `foldlM g` also succeeds with the same result. -/
theorem List.foldlM_option_mono {f g : β → α → Option β} {l : List α} {init result : β}
    (hmono : ∀ acc a, a ∈ l → ∀ v, f acc a = some v → g acc a = some v)
    (h : l.foldlM f init = some result) :
    l.foldlM g init = some result := by
  induction l generalizing init with
  | nil => simpa [List.foldlM_nil] using h
  | cons x xs ih =>
    simp only [List.foldlM_cons] at h ⊢
    cases hfx : f init x with
    | none => simp [hfx] at h
    | some mid =>
      simp [hfx] at h
      simp [hmono init x (.head ..) mid hfx,
            ih (fun acc a ha => hmono acc a (.tail _ ha)) h]

/-! ## evalOptStep monotonicity helpers -/

/-- Monotonicity of the LET binding fold step. -/
-- `valEnv` is the environment a binding's value is evaluated in: the accumulator `acc`
-- for `let*` (sequential — each value sees the prior bindings), or the original `env` for
-- `let` (parallel — every value sees the outer env). The new bindings are always added on
-- top of `acc`. Generalizing over `valEnv` lets one lemma cover both.
private theorem letFoldStep_mono
    (f g : World → Env → SExpr → Option SExpr)
    (hmono : ∀ w env t v, f w env t = some v → g w env t = some v)
    (w : World) (valEnv acc : Env) (b : SExpr) (mid : Env)
    (hmid : (match b.toList? with
      | some [.atom (.symbol var), valExpr] =>
          (f w valEnv valExpr).bind fun v => some (acc.insert var v)
      | _ => none) = some mid) :
    (match b.toList? with
      | some [.atom (.symbol var), valExpr] =>
          (g w valEnv valExpr).bind fun v => some (acc.insert var v)
      | _ => none) = some mid := by
  match hbl : b.toList? with
  | some [.atom (.symbol var), valExpr] =>
    simp only [hbl] at hmid ⊢
    cases hval : f w valEnv valExpr with
    | none => simp [hval] at hmid
    | some val => simp [hval] at hmid; simp [hmono w valEnv valExpr val hval, hmid]
  | some [.nil, _] | some [.atom (.number _), _] | some [.atom (.string _), _]
  | some [.atom (.keyword _), _] | some [.atom (.char _), _] | some [.cons _ _, _]
  | some (_ :: _ :: _ :: _) | some [_] | some [] | none =>
    simp only [hbl] at hmid ⊢; exact hmid

/-! ## evalOptStep monotonicity -/

/-- `evalOptStep` is monotone in its function argument: if `f` and `g`
    agree on successful evaluations, then `evalOptStep f` and `evalOptStep g`
    agree on successful evaluations. This is the heart of fuel monotonicity,
    proved about the non-recursive step function. -/
theorem evalOptStep_mono
    (f g : World → Env → SExpr → Option SExpr)
    (hmono : ∀ w env t v, f w env t = some v → g w env t = some v)
    (w : World) (env : Env) (t : SExpr) (v : SExpr)
    (h : evalOptStep f w env t = some v) :
    evalOptStep g w env t = some v := by
  -- evalOptStep is non-recursive; f and g are opaque parameters.
  -- Match on t to reduce evalOptStep's dispatch. For non-recursive
  -- cases, h and goal are definitionally equal (no f/g calls).
  match t with
  | .nil | .atom (.number _) | .atom (.string _)
  | .atom (.keyword _) | .atom (.char _) | .atom (.symbol _) => exact h
  | .cons (.atom (.number _)) _ | .cons (.atom (.string _)) _
  | .cons (.atom (.keyword _)) _ | .cons (.atom (.char _)) _ | .cons .nil _ => exact h
  | .cons (.cons .nil _) _ | .cons (.cons (.atom (.number _)) _) _
  | .cons (.cons (.atom (.string _)) _) _ | .cons (.cons (.atom (.keyword _)) _) _
  | .cons (.cons (.atom (.char _)) _) _ | .cons (.cons (.cons _ _) _) _ => exact h
  | .cons (.cons (.atom (.symbol lam)) .nil) _
  | .cons (.cons (.atom (.symbol lam)) (.atom _)) _
  | .cons (.cons (.atom (.symbol lam)) (.cons _ .nil)) _
  | .cons (.cons (.atom (.symbol lam)) (.cons _ (.atom _))) _
  | .cons (.cons (.atom (.symbol lam)) (.cons _ (.cons _ (.cons _ _)))) _
  | .cons (.cons (.atom (.symbol lam)) (.cons _ (.cons _ (.atom _)))) _ => exact h
  | .cons (.cons (.atom (.symbol lam)) (.cons formalsE (.cons lamBody .nil))) argsExpr =>
    -- the LAMBDA-application arm (S2 2026-07-24): mirrors the function-call
    -- branch — actuals via `mapM` monotonicity, body via `hmono`
    simp only [evalOptStep] at h ⊢
    by_cases hlam : lam.isNamed "LAMBDA" = true
    · simp only [hlam, ite_true] at h ⊢
      match hfl : lamFormals? formalsE, hal : argsExpr.toList? with
      | some formals, some args =>
        simp only [hfl, hal] at h ⊢
        cases hmap : List.mapM (fun a => f w env a) args with
        | none => simp [hmap] at h
        | some argVals =>
          simp [hmap] at h
          simp [List.mapM_option_mono (fun a _ val hval =>
            hmono w env a val hval) hmap]
          by_cases hlen : formals.length = argVals.length
          · simp [hlen] at h ⊢
            exact hmono w (bindArgsOver env formals argVals) lamBody v h
          · simp [hlen] at h
      | none, some _ => simp only [hfl] at h ⊢; exact h
      | none, none => simp only [hfl] at h ⊢; exact h
      | some _, none => simp only [hfl, hal] at h ⊢; exact h
    · simp only [hlam] at h ⊢; exact h
  | .cons (.atom (.symbol s)) argsExpr =>
    simp only [evalOptStep] at h ⊢
    by_cases hq : s.isNamed "QUOTE" = true
    · simp [hq] at h ⊢; exact h
    · simp [hq] at h ⊢
      by_cases hif : s.isNamed "IF" = true
      · simp [hif] at h ⊢
        match htl : argsExpr.toList? with
        | some [c, t', e] =>
          simp [htl] at h ⊢
          cases hc : f w env c with
          | none => simp [hc] at h
          | some cv =>
            simp [hc] at h; simp [hmono w env c cv hc]
            cases cv with
            | nil => simp at h ⊢; exact hmono w env e v h
            | atom _ => simp at h ⊢; exact hmono w env t' v h
            | cons _ _ => simp at h ⊢; exact hmono w env t' v h
        | none | some [] | some [_] | some [_, _]
        | some (_ :: _ :: _ :: _ :: _) => simp only [htl] at h; exact h
      · simp [hif] at h ⊢
        by_cases hlet : (s.isNamed "LET" || s.isNamed "LET*") = true
        · -- LET branch
          simp only [Bool.or_eq_true] at hlet
          simp only [hlet, ite_true] at h ⊢
          match htl : argsExpr.toList? with
          | some [bindings, body] =>
            simp only [htl] at h ⊢
            match hbl : bindings.toList? with
            | some bList =>
              simp only [hbl] at h ⊢
              cases hfold : List.foldlM (fun acc b => match b.toList? with
                | some [.atom (.symbol var), valExpr] =>
                    (f w (if s.isNamed "LET*" then acc else env) valExpr).bind
                      fun v => some (acc.insert var v)
                | _ => none) env bList with
              | none => simp [hfold] at h
              | some env' =>
                simp [hfold] at h
                have hfold' := List.foldlM_option_mono
                  (fun acc b _ mid hmid =>
                    letFoldStep_mono f g hmono w (if s.isNamed "LET*" then acc else env) acc b mid hmid)
                  hfold
                simp [hfold', hmono w env' _ v h]
            | none => simp only [hbl] at h; exact h
          | none | some [] | some [_]
          | some (_ :: _ :: _ :: _) => simp only [htl] at h; exact h
        · -- Function call branch
          simp only [Bool.or_eq_true] at hlet
          simp only [hlet, ite_false] at h ⊢
          match htl : argsExpr.toList? with
          | some args =>
            simp only [htl] at h ⊢
            cases hmap : (List.mapM (fun a => f w env a) args) with
            | none => simp [hmap] at h
            | some argVals =>
              simp [hmap] at h
              simp [List.mapM_option_mono (fun a _ val hval =>
                hmono w env a val hval) hmap]
              match hdef : w.defs.get? s with
              | some (formals, body) =>
                simp [hdef] at h ⊢
                by_cases hlen : formals.length = argVals.length
                · simp [hlen] at h ⊢
                  exact hmono w (bindArgs formals argVals) body v h
                · simp [hlen] at h
              | none => simp [hdef] at h ⊢; exact h
          | none => simp only [htl] at h; exact h

/-! ## Defs-extensionality

`evalOpt` consults the world ONLY through `defs.get?`, so worlds that agree on
every lookup are observationally identical. This is the transfer principle for
results proved over one concrete world (e.g. the hand-proof dischargers) to a
`get?`-equal world (e.g. the log-derived one, which may list the same defs in
a different order). It is also the semantic content of binding invariant L3:
world-parametric lemmas can never depend on entry order. -/

theorem evalOptStep_defs_ext
    (f g : World → Env → SExpr → Option SExpr)
    (w1 w2 : World)
    (hdefs : ∀ s, w1.defs.get? s = w2.defs.get? s)
    (hrec : ∀ env t, f w1 env t = g w2 env t)
    (env : Env) (t : SExpr) :
    evalOptStep f w1 env t = evalOptStep g w2 env t := by
  -- Unlike the monotonicity congruence (an implication, needing the case
  -- bash above), the EQUALITY version collapses: the recursive calls rewrite
  -- uniformly by the function-level equality, and the world is consulted
  -- ONLY through `defs.get?`.
  have hfun : f w1 = g w2 := funext fun e => funext fun u => hrec e u
  unfold evalOptStep
  simp only [hfun, hdefs]

/-- Worlds that agree on every `defs.get?` evaluate identically. -/
theorem evalOpt_defs_ext {w1 w2 : World}
    (hdefs : ∀ s, w1.defs.get? s = w2.defs.get? s) :
    ∀ (f : Nat) (env : Env) (t : SExpr), evalOpt f w1 env t = evalOpt f w2 env t := by
  intro f
  induction f with
  | zero => intro env t; rfl
  | succ n ih =>
    intro env t
    exact evalOptStep_defs_ext (evalOpt n) (evalOpt n) w1 w2 hdefs
      (fun env t => ih env t) env t

/-! ## Fuel monotonicity -/

/-- Once evalOpt converges, more fuel doesn't change the result. -/
theorem evalOpt_fuel_mono (f : Nat) (w : World) (env : Env)
    (t : SExpr) (v : SExpr)
    (h : evalOpt f w env t = some v) :
    evalOpt (f + 1) w env t = some v := by
  induction f generalizing w env t v with
  | zero => simp [evalOpt] at h
  | succ n ih =>
    -- evalOpt (n+1) = evalOptStep (evalOpt n)
    -- evalOpt (n+2) = evalOptStep (evalOpt (n+1))
    -- By ih: evalOpt n agrees with evalOpt (n+1) on successful evals
    -- By evalOptStep_mono: therefore evalOptStep (evalOpt n) agrees with evalOptStep (evalOpt (n+1))
    exact evalOptStep_mono (evalOpt n) (evalOpt (n + 1)) ih w env t v h

/-- Fuel sufficiency: if evalOpt converges at fuel N, it gives the same
    result at any fuel f ≥ N. -/
theorem evalOpt_ge_fuel (N f : Nat) (w : World) (env : Env)
    (t : SExpr) (v : SExpr)
    (h : evalOpt N w env t = some v) (hge : f ≥ N) :
    evalOpt f w env t = some v := by
  induction hge with
  | refl => exact h
  | step _ ih => exact evalOpt_fuel_mono _ w env t v ih

/-! ## World monotonicity (external-knowledge design §D2, WP5)

A convergent evaluation over `w1` transfers to an EXTENSION `w2` — the
cross-book lemma (a mirror proved over an included book's world, used in a
proof over the including book's larger world). `hnew` is NOT bureaucracy:
world-FIRST dispatch means a `w2` def for a name that `w1` resolved via
`callBuiltin` (e.g. `LEN`) would send the two evaluations down different
routes, and the implication would be FALSE — `hnew` is exactly the
soundness condition that dispatch order forces. Both side conditions are
decidable per world pair. (ACL2 itself prohibits redefining built-ins, so
on legal input the shadow case never arises; `hnew` makes that assumption
explicit and checked rather than ambient.) -/

private theorem letFoldStep_world_mono
    (f g : World → Env → SExpr → Option SExpr) {w1 w2 : World}
    (hmono : ∀ env t v, f w1 env t = some v → g w2 env t = some v)
    (valEnv acc : Env) (b : SExpr) (mid : Env)
    (hmid : (match b.toList? with
      | some [.atom (.symbol var), valExpr] =>
          (f w1 valEnv valExpr).bind fun v => some (acc.insert var v)
      | _ => none) = some mid) :
    (match b.toList? with
      | some [.atom (.symbol var), valExpr] =>
          (g w2 valEnv valExpr).bind fun v => some (acc.insert var v)
      | _ => none) = some mid := by
  match hbl : b.toList? with
  | some [.atom (.symbol var), valExpr] =>
    simp only [hbl] at hmid ⊢
    cases hval : f w1 valEnv valExpr with
    | none => simp [hval] at hmid
    | some val => simp [hval] at hmid; simp [hmono valEnv valExpr val hval, hmid]
  | some [.nil, _] | some [.atom (.number _), _] | some [.atom (.string _), _]
  | some [.atom (.keyword _), _] | some [.atom (.char _), _] | some [.cons _ _, _]
  | some (_ :: _ :: _ :: _) | some [_] | some [] | none =>
    simp only [hbl] at hmid ⊢; exact hmid

/-- The two-world step congruence behind `evalOpt_world_mono` — the
    `evalOptStep_mono` case bash with the call branch split FOUR ways on
    `w1.defs.get? s × w2.defs.get? s` (def/def via `hext`, none/… via
    `hnew`'s disjunction; def/none is impossible by `hext`). -/
theorem evalOptStep_world_mono
    (f g : World → Env → SExpr → Option SExpr) {w1 w2 : World}
    (hext : ∀ s d, w1.defs.get? s = some d → w2.defs.get? s = some d)
    (hnew : ∀ s, w1.defs.get? s = none →
      w2.defs.get? s = none ∨ (∀ args, callBuiltin s.name args = none))
    (hmono : ∀ env t v, f w1 env t = some v → g w2 env t = some v)
    (env : Env) (t : SExpr) (v : SExpr)
    (h : evalOptStep f w1 env t = some v) :
    evalOptStep g w2 env t = some v := by
  match t with
  | .nil | .atom (.number _) | .atom (.string _)
  | .atom (.keyword _) | .atom (.char _) | .atom (.symbol _) => exact h
  | .cons (.atom (.number _)) _ | .cons (.atom (.string _)) _
  | .cons (.atom (.keyword _)) _ | .cons (.atom (.char _)) _ | .cons .nil _ => exact h
  | .cons (.cons .nil _) _ | .cons (.cons (.atom (.number _)) _) _
  | .cons (.cons (.atom (.string _)) _) _ | .cons (.cons (.atom (.keyword _)) _) _
  | .cons (.cons (.atom (.char _)) _) _ | .cons (.cons (.cons _ _) _) _ => exact h
  | .cons (.cons (.atom (.symbol lam)) .nil) _
  | .cons (.cons (.atom (.symbol lam)) (.atom _)) _
  | .cons (.cons (.atom (.symbol lam)) (.cons _ .nil)) _
  | .cons (.cons (.atom (.symbol lam)) (.cons _ (.atom _))) _
  | .cons (.cons (.atom (.symbol lam)) (.cons _ (.cons _ (.cons _ _)))) _
  | .cons (.cons (.atom (.symbol lam)) (.cons _ (.cons _ (.atom _)))) _ => exact h
  | .cons (.cons (.atom (.symbol lam)) (.cons formalsE (.cons lamBody .nil))) argsExpr =>
    -- LAMBDA application (S2 2026-07-24): world-independent — actuals via
    -- `mapM` under `hmono`, body via `hmono`; no `defs.get?` consulted
    simp only [evalOptStep] at h ⊢
    by_cases hlam : lam.isNamed "LAMBDA" = true
    · simp only [hlam, ite_true] at h ⊢
      match hfl : lamFormals? formalsE, hal : argsExpr.toList? with
      | some formals, some args =>
        simp only [hfl, hal] at h ⊢
        cases hmap : List.mapM (fun a => f w1 env a) args with
        | none => simp [hmap] at h
        | some argVals =>
          simp [hmap] at h
          simp [List.mapM_option_mono (fun a _ val hval =>
            hmono env a val hval) hmap]
          by_cases hlen : formals.length = argVals.length
          · simp [hlen] at h ⊢
            exact hmono (bindArgsOver env formals argVals) lamBody v h
          · simp [hlen] at h
      | none, some _ => simp only [hfl] at h ⊢; exact h
      | none, none => simp only [hfl] at h ⊢; exact h
      | some _, none => simp only [hfl, hal] at h ⊢; exact h
    · simp only [hlam] at h ⊢; exact h
  | .cons (.atom (.symbol s)) argsExpr =>
    simp only [evalOptStep] at h ⊢
    by_cases hq : s.isNamed "QUOTE" = true
    · simp [hq] at h ⊢; exact h
    · simp [hq] at h ⊢
      by_cases hif : s.isNamed "IF" = true
      · simp [hif] at h ⊢
        match htl : argsExpr.toList? with
        | some [c, t', e] =>
          simp [htl] at h ⊢
          cases hc : f w1 env c with
          | none => simp [hc] at h
          | some cv =>
            simp [hc] at h; simp [hmono env c cv hc]
            cases cv with
            | nil => simp at h ⊢; exact hmono env e v h
            | atom _ => simp at h ⊢; exact hmono env t' v h
            | cons _ _ => simp at h ⊢; exact hmono env t' v h
        | none | some [] | some [_] | some [_, _]
        | some (_ :: _ :: _ :: _ :: _) => simp only [htl] at h; exact h
      · simp [hif] at h ⊢
        by_cases hlet : (s.isNamed "LET" || s.isNamed "LET*") = true
        · -- LET branch
          simp only [Bool.or_eq_true] at hlet
          simp only [hlet, ite_true] at h ⊢
          match htl : argsExpr.toList? with
          | some [bindings, body] =>
            simp only [htl] at h ⊢
            match hbl : bindings.toList? with
            | some bList =>
              simp only [hbl] at h ⊢
              cases hfold : List.foldlM (fun acc b => match b.toList? with
                | some [.atom (.symbol var), valExpr] =>
                    (f w1 (if s.isNamed "LET*" then acc else env) valExpr).bind
                      fun v => some (acc.insert var v)
                | _ => none) env bList with
              | none => simp [hfold] at h
              | some env' =>
                simp [hfold] at h
                have hfold' := List.foldlM_option_mono
                  (fun acc b _ mid hmid =>
                    letFoldStep_world_mono f g hmono
                      (if s.isNamed "LET*" then acc else env) acc b mid hmid)
                  hfold
                simp [hfold', hmono env' _ v h]
            | none => simp only [hbl] at h; exact h
          | none | some [] | some [_]
          | some (_ :: _ :: _ :: _) => simp only [htl] at h; exact h
        · -- Function-call branch: the four-way world split
          simp only [Bool.or_eq_true] at hlet
          simp only [hlet, ite_false] at h ⊢
          match htl : argsExpr.toList? with
          | some args =>
            simp only [htl] at h ⊢
            cases hmap : (List.mapM (fun a => f w1 env a) args) with
            | none => simp [hmap] at h
            | some argVals =>
              simp [hmap] at h
              simp [List.mapM_option_mono (fun a _ val hval =>
                hmono env a val hval) hmap]
              match hdef : w1.defs.get? s with
              | some (formals, body) =>
                -- def/def: `hext` carries the SAME (formals, body) to w2
                simp [hdef, hext s _ hdef] at h ⊢
                by_cases hlen : formals.length = argVals.length
                · simp [hlen] at h ⊢
                  exact hmono (bindArgs formals argVals) body v h
                · simp [hlen] at h
              | none =>
                simp [hdef] at h
                rcases hnew s hdef with h2 | hcb
                · -- none/none: both dispatch to `callBuiltin`
                  simp [h2]; exact h
                · -- none/def would shadow — but then `callBuiltin` returns
                  -- none on every args, contradicting h's convergence
                  rw [hcb argVals] at h; cases h
          | none => simp only [htl] at h; exact h

/-- WORLD MONOTONICITY (design §D2 — the statement is fixed there): a
    convergent `evalOpt` over `w1` converges identically over any extension
    `w2` that (a) preserves every `w1` def (`hext`) and (b) adds no def that
    would SHADOW a builtin `w1` dispatched via `callBuiltin` (`hnew` — the
    side condition world-first dispatch forces; see the section note).
    Fuel-shape preserving (per-fuel), so `∃N∀f≥N` facts transfer directly. -/
theorem evalOpt_world_mono {w1 w2 : World}
    (hext : ∀ s d, w1.defs.get? s = some d → w2.defs.get? s = some d)
    (hnew : ∀ s, w1.defs.get? s = none →
      w2.defs.get? s = none ∨ (∀ args, callBuiltin s.name args = none)) :
    ∀ (f : Nat) (env : Env) (t : SExpr) (v : SExpr),
      evalOpt f w1 env t = some v → evalOpt f w2 env t = some v := by
  intro f
  induction f with
  | zero => intro env t v h; simp [evalOpt] at h
  | succ n ih =>
    intro env t v h
    exact evalOptStep_world_mono (evalOpt n) (evalOpt n) hext hnew
      (fun env t v hv => ih env t v hv) env t v h

/-! ## Smoke tests -/

section Tests

-- Symbol names are stored UPCASED (readtable :upcase), so these test helpers
-- construct uppercase names to match how the interpreter looks up defs/builtins.
private def sym (name : String) : Symbol := { package := "ACL2", name := name.map Char.toUpper }

private def mkCall (name : String) (args : List SExpr) : SExpr :=
  .cons (.atom (.symbol (sym name))) (SExpr.ofList args)

private def mkVar (name : String) : SExpr := .atom (.symbol (sym name))

-- my-len body: (if (consp x) (+ 1 (my-len (cdr x))) 0)
private def myLenBody : SExpr :=
  mkCall "if" [mkCall "consp" [mkVar "x"],
               mkCall "+" [.atom (.number (.int 1)),
                           mkCall "my-len" [mkCall "cdr" [mkVar "x"]]],
               .atom (.number (.int 0))]

-- my-app body: (if (consp x) (cons (car x) (my-app (cdr x) y)) y)
private def myAppBody : SExpr :=
  mkCall "if" [mkCall "consp" [mkVar "x"],
               mkCall "cons" [mkCall "car" [mkVar "x"],
                              mkCall "my-app" [mkCall "cdr" [mkVar "x"], mkVar "y"]],
               mkVar "y"]

private def simpleWorld : World :=
  { defs := ({} : DefMap)
      |>.insert (sym "my-len") ([sym "x"], myLenBody)
      |>.insert (sym "my-app") ([sym "x", sym "y"], myAppBody) }

-- Fuel 0 returns none
#guard evalOpt 0 simpleWorld {} .nil == none

-- Simple self-evaluating forms
#guard evalOpt 1 simpleWorld {} .nil == some .nil
#guard evalOpt 1 simpleWorld {} (.atom (.number (.int 42))) == some (.atom (.number (.int 42)))
#guard evalOpt 1 simpleWorld {} SExpr.t == some SExpr.t

-- Variable lookup
private def testEnv : Env :=
  ({} : Env).insert (sym "x") (.atom (.number (.int 7)))

#guard evalOpt 1 simpleWorld testEnv (mkVar "x") == some (.atom (.number (.int 7)))

-- Quote
private def mkQuote (v : SExpr) : SExpr :=
  .cons (.atom (.symbol (sym "quote"))) (.cons v .nil)

#guard evalOpt 1 simpleWorld {} (mkQuote (.atom (.number (.int 99)))) == some (.atom (.number (.int 99)))

-- Builtin: (consp nil) = nil
#guard evalOpt 2 simpleWorld {} (mkCall "consp" [.nil]) == some .nil

-- Builtin: (consp (cons 1 2)) = t
#guard evalOpt 3 simpleWorld {} (mkCall "consp" [mkCall "cons" [.atom (.number (.int 1)), .atom (.number (.int 2))]]) == some SExpr.t

-- Builtin: (equal 3 3) = t
#guard evalOpt 2 simpleWorld {} (mkCall "equal" [.atom (.number (.int 3)), .atom (.number (.int 3))]) == some SExpr.t

-- IF: (if nil 1 2) = 2
#guard evalOpt 2 simpleWorld {} (mkCall "if" [.nil, .atom (.number (.int 1)), .atom (.number (.int 2))]) == some (.atom (.number (.int 2)))

-- IF: (if t 1 2) = 1
#guard evalOpt 2 simpleWorld {} (mkCall "if" [SExpr.t, .atom (.number (.int 1)), .atom (.number (.int 2))]) == some (.atom (.number (.int 1)))

-- my-len of nil = 0
#guard evalOpt 10 simpleWorld (({} : Env).insert (sym "x") .nil) (mkCall "my-len" [mkVar "x"]) == some (.atom (.number (.int 0)))

-- my-len of (cons 1 nil) = 1
private def list1 : SExpr := .cons (.atom (.number (.int 1))) .nil
#guard evalOpt 10 simpleWorld (({} : Env).insert (sym "x") list1) (mkCall "my-len" [mkVar "x"]) == some (.atom (.number (.int 1)))

-- my-app of nil and (cons 1 nil) = (cons 1 nil)
#guard evalOpt 10 simpleWorld (({} : Env).insert (sym "x") .nil |>.insert (sym "y") list1) (mkCall "my-app" [mkVar "x", mkVar "y"]) == some list1

-- Key property: at insufficient fuel, evalOpt returns none (not a wrong answer)
-- (my-len (cons 1 (cons 2 nil))) needs several fuel units
private def list2 : SExpr := .cons (.atom (.number (.int 1))) (.cons (.atom (.number (.int 2))) .nil)
#guard evalOpt 1 simpleWorld (({} : Env).insert (sym "x") list2) (mkCall "my-len" [mkVar "x"]) == none

-- With enough fuel, it succeeds
#guard evalOpt 20 simpleWorld (({} : Env).insert (sym "x") list2) (mkCall "my-len" [mkVar "x"]) == some (.atom (.number (.int 2)))

-- An unmodeled / unknown primitive does NOT silently evaluate to nil; it fails
-- to converge (none), surfacing that the primitive needs a faithful model rather
-- than producing a wrong value.
#guard evalOpt 2 simpleWorld {} (mkCall "no-such-primitive" [.atom (.number (.int 1))]) == none
#guard evalOpt 2 simpleWorld {} (mkCall "floor" [.atom (.number (.int 3)), .atom (.number (.int 2))]) == none

-- COMPLEX-RATIONALP is now a modeled builtin (sorting arc 2026-07-28,
-- differential-pinned): NIL on every representable value (the value space
-- has no complex numbers; #c is a pinned unsupported reader class).
#guard evalOpt 2 simpleWorld {} (mkCall "complex-rationalp" [.atom (.number (.int 3))]) == some .nil

end Tests

end ACL2
