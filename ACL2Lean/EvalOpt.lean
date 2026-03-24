/-
  Option-returning ACL2 evaluator for soundness proofs.

  Structurally identical to `eval` but returns `Option SExpr`:
  - `none` means fuel exhaustion (computation incomplete)
  - `some v` means successful evaluation to value `v`

  This distinction is critical for the verified rewriter's soundness proof:
  at insufficient fuel, `evalOpt f w env lhs = none = evalOpt f w env rhs`,
  so the hypothesis `∀ f, evalOpt f w env lhs = evalOpt f w env rhs` holds
  trivially. With the original `eval` (which returns `.nil` for fuel exhaustion),
  intermediate fuel levels can produce `.nil` on one side and a real value on
  the other, breaking the universal quantification.
-/
import ACL2Lean.Eval

namespace ACL2

/-- Option-returning ACL2 evaluator. `none` = fuel exhaustion.
    Structurally mirrors `eval` exactly. -/
def evalOpt (fuel : Nat) (w : World) (env : Env) (term : SExpr) : Option SExpr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
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
            else some .nil  -- NIL or unbound variable
    | .cons (.atom (.symbol s)) argsExpr =>
        if s.isNamed "quote" then
          match argsExpr with
          | .cons v .nil => some v
          | _ => some .nil
        else if s.isNamed "if" then
          match argsExpr.toList? with
          | some [c, t, e] => do
              let cv ← evalOpt fuel w env c
              if Logic.toBool cv then
                evalOpt fuel w env t
              else
                evalOpt fuel w env e
          | _ => some .nil
        else if s.isNamed "let" || s.isNamed "let*" then
          match argsExpr.toList? with
          | some [bindings, body] =>
              match bindings.toList? with
              | some bList => do
                  let env' ← bList.foldlM (fun acc b =>
                    match b.toList? with
                    | some [.atom (.symbol var), valExpr] => do
                        let v ← evalOpt fuel w acc valExpr
                        pure (acc.insert var v)
                    | _ => some acc) env
                  evalOpt fuel w env' body
              | none => some .nil
          | _ => some .nil
        else
          -- Function call: evaluate args, then dispatch
          match argsExpr.toList? with
          | some args => do
              let argVals ← args.mapM (fun a => evalOpt fuel w env a)
              match w.defs.get? s with
              | some (formals, body) =>
                  if formals.length = argVals.length then
                    evalOpt fuel w (bindArgs formals argVals) body
                  else some .nil
              | none => some (callBuiltin s.normalizedName argVals)
          | none => some .nil
    | _ => some .nil

/-! ## Bridge lemma: evalOpt agrees with eval when successful -/

theorem evalOpt_some_eq_eval (fuel : Nat) (w : World) (env : Env) (term : SExpr) (v : SExpr) :
    evalOpt fuel w env term = some v → eval fuel w env term = v := by
  sorry -- TODO: prove by induction on fuel, mirroring eval's structure

/-! ## Smoke tests — evalOpt agrees with eval on concrete inputs -/

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
  { defs := ({} : Std.HashMap Symbol (List Symbol × SExpr))
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
  ({} : Std.HashMap Symbol SExpr).insert (sym "x") (.atom (.number (.int 7)))

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

end Tests

end ACL2
