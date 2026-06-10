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

namespace ACL2

/-- Bind function formals to argument values, producing a new environment. -/
def bindArgs : List Symbol → List SExpr → Env
  | f :: fs, v :: vs => (bindArgs fs vs).insert f v
  | _, _ => {}  -- ⚠ silent default on formals/args length mismatch (no hard-fail); see callBuiltin note

/-- Dispatch an ACL2 built-in primitive by normalized name, modeling ACL2's
    LOGICAL (total) semantics. Returns `none` for a primitive we do not yet model
    or a wrong arity — a frontier the evaluator surfaces as non-convergence rather
    than silently returning a wrong value (`nil`). A genuinely undefined function
    cannot occur in a faithfully-translated admitted term (ACL2's translate
    rejects it); an unmodeled-but-real primitive (`numerator`, `integer-abs`, …)
    must be added here with its faithful value, not left to default. -/
def callBuiltin (name : String) (args : List SExpr) : Option SExpr :=
  match name, args with
  | "cons", [a, b] => some (.cons a b)
  | "car", [a] => some (Logic.car a)
  | "cdr", [a] => some (Logic.cdr a)
  | "consp", [a] => some (Logic.consp a)
  | "atom", [a] => some (Logic.atom a)
  | "endp", [a] => some (Logic.endp a)
  | "equal", [a, b] => some (Logic.equal a b)
  | "eql", [a, b] => some (Logic.equal a b)
  | "not", [a] => some (Logic.not a)
  | "binary-+", [a, b] => some (Logic.plus a b)
  | "binary-*", [a, b] => some (Logic.times a b)
  | "unary--", [a] =>
      let (n, d) := Logic.toRat a
      some (Logic.mkNumber (-n) d)
  | "unary-/", [a] =>
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
  | "integerp", [a] => some (Logic.integerp a)
  | "natp", [a] => some (Logic.natp a)
  | "posp", [a] => some (Logic.posp a)
  | "rationalp", [a] =>
      some (match a with | .atom (.number _) => .t | _ => .nil)
  | "acl2-numberp", [a] =>
      some (match a with | .atom (.number _) => .t | _ => .nil)
  | "zp", [a] => some (Logic.zp a)
  | "symbolp", [a] =>
      some (match a with | .atom (.symbol _) | .nil => .t | _ => .nil)
  | "stringp", [a] => some (Logic.stringp a)
  | "fix", [a] =>
      some (match a with | .atom (.number _) => a | _ => .atom (.number (.int 0)))
  | "nfix", [a] =>
      some (match a with
      | .atom (.number (.int n)) => if n >= 0 then a else .atom (.number (.int 0))
      | _ => .atom (.number (.int 0)))
  | "ifix", [a] =>
      some (match a with | .atom (.number (.int _)) => a | _ => .atom (.number (.int 0)))
  | "implies", [a, b] => some (Logic.implies a b)
  | "iff", [a, b] => some (Logic.iff a b)
  | "true-listp", [a] => some (Logic.trueListp a)
  | "len", [a] => some (Logic.len a)
  | "list", xs => some (SExpr.ofList xs)
  | "force", [a] => some a
  | "double-rewrite", [a] => some a
  | "hide", [a] => some a
  | _, _ => none

/-- One step of the option-returning evaluator, parameterized by the
    recursive evaluator function. Factored out so that monotonicity
    can be proved about this non-recursive function directly. -/
def evalOptStep (rec : World → Env → SExpr → Option SExpr)
    (w : World) (env : Env) (term : SExpr) : Option SExpr :=
  match term with
  | .nil => some .nil
  | .atom (.number n) => some (.atom (.number n))
  | .atom (.string s) => some (.atom (.string s))
  | .atom (.keyword k) => some (.atom (.keyword k))
  | .atom (.symbol s) =>
      match env.get? s with
      | some v => some v
      | none =>
          if s.isNamed "t" then some SExpr.t
          else some .nil
  | .cons (.atom (.symbol s)) argsExpr =>
      if s.isNamed "quote" then
        match argsExpr with
        | .cons v .nil => some v
        | _ => some .nil
      else if s.isNamed "if" then
        match argsExpr.toList? with
        | some [c, t, e] => do
            let cv ← rec w env c
            if Logic.toBool cv then rec w env t else rec w env e
        | _ => some .nil
      else if s.isNamed "let" || s.isNamed "let*" then
        match argsExpr.toList? with
        | some [bindings, body] =>
            match bindings.toList? with
            | some bList => do
                -- `let*` is sequential (each value sees prior bindings: eval in `acc`);
                -- `let` is parallel (every value sees the outer env: eval in `env`).
                let env' ← bList.foldlM (fun acc b =>
                  match b.toList? with
                  | some [.atom (.symbol var), valExpr] => do
                      let v ← rec w (if s.isNamed "let*" then acc else env) valExpr
                      pure (acc.insert var v)
                  | _ => some acc) env
                rec w env' body
            | none => some .nil
        | _ => some .nil
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
        | none => some .nil
  | _ => some .nil

/-- Equation lemma for evalOptStep on symbol-headed cons. -/
@[simp] theorem evalOptStep_cons_symbol (rec : World → Env → SExpr → Option SExpr)
    (w : World) (env : Env) (s : Symbol) (argsExpr : SExpr) :
    evalOptStep rec w env (.cons (.atom (.symbol s)) argsExpr) =
    if s.isNamed "quote" then
      match argsExpr with
      | .cons v .nil => some v
      | _ => some .nil
    else if s.isNamed "if" then
      match argsExpr.toList? with
      | some [c, t, e] => do
          let cv ← rec w env c
          if Logic.toBool cv then rec w env t else rec w env e
      | _ => some .nil
    else if s.isNamed "let" || s.isNamed "let*" then
      match argsExpr.toList? with
      | some [bindings, body] =>
          match bindings.toList? with
          | some bList => do
              let env' ← bList.foldlM (fun acc b =>
                match b.toList? with
                | some [.atom (.symbol var), valExpr] => do
                    let v ← rec w (if s.isNamed "let*" then acc else env) valExpr
                    pure (acc.insert var v)
                | _ => some acc) env
              rec w env' body
          | none => some .nil
      | _ => some .nil
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
      | none => some .nil := by
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
      | _ => some acc) = some mid) :
    (match b.toList? with
      | some [.atom (.symbol var), valExpr] =>
          (g w valEnv valExpr).bind fun v => some (acc.insert var v)
      | _ => some acc) = some mid := by
  match hbl : b.toList? with
  | some [.atom (.symbol var), valExpr] =>
    simp only [hbl] at hmid ⊢
    cases hval : f w valEnv valExpr with
    | none => simp [hval] at hmid
    | some val => simp [hval] at hmid; simp [hmono w valEnv valExpr val hval, hmid]
  | some [.nil, _] | some [.atom (.number _), _] | some [.atom (.string _), _]
  | some [.atom (.keyword _), _] | some [.cons _ _, _]
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
  | .atom (.keyword _) | .atom (.symbol _) => exact h
  | .cons (.atom (.number _)) _ | .cons (.atom (.string _)) _
  | .cons (.atom (.keyword _)) _ | .cons .nil _
  | .cons (.cons _ _) _ => exact h
  | .cons (.atom (.symbol s)) argsExpr =>
    simp only [evalOptStep] at h ⊢
    by_cases hq : s.isNamed "quote" = true
    · simp [hq] at h ⊢; exact h
    · simp [hq] at h ⊢
      by_cases hif : s.isNamed "if" = true
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
        by_cases hlet : (s.isNamed "let" || s.isNamed "let*") = true
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
                    (f w (if s.isNamed "let*" then acc else env) valExpr).bind
                      fun v => some (acc.insert var v)
                | _ => some acc) env bList with
              | none => simp [hfold] at h
              | some env' =>
                simp [hfold] at h
                have hfold' := List.foldlM_option_mono
                  (fun acc b _ mid hmid =>
                    letFoldStep_mono f g hmono w (if s.isNamed "let*" then acc else env) acc b mid hmid)
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

/-! ## Smoke tests -/

section Tests

private def sym (name : String) : Symbol := ⟨"ACL2", name⟩

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
#guard evalOpt 2 simpleWorld {} (mkCall "complex-rationalp" [.atom (.number (.int 3))]) == none

end Tests

end ACL2
