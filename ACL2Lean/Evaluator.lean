import ACL2Lean.Syntax
import ACL2Lean.Parser

namespace ACL2

/-- Environment maps symbols to values (SExprs). -/
abbrev Env := Std.HashMap Symbol SExpr

/-- Evaluation result. -/
abbrev EvalM := Except String

namespace Evaluator

/-- Check if an s-expression is truthy (non-nil). -/
def isTruthy : SExpr → Bool
  | .nil => false
  | _ => true

/-- Convert a boolean to an ACL2 boolean (t or nil). -/
def toACL2Bool (b : Bool) : SExpr :=
  if b then SExpr.t else SExpr.nil

def isTrueList : SExpr → Bool
  | .nil => true
  | .cons _ t => isTrueList t
  | _ => false

def append (a b : SExpr) : SExpr :=
  match a with
  | .nil => b
  | .cons h t => .cons h (append t b)
  | _ => b

/-- Basic built-in functions. -/
partial def callBuiltin (name : String) (args : List SExpr) : EvalM SExpr :=
  match name.map Char.toLower, args with
  | "cons", [a, b] => .ok (SExpr.cons a b)
  | "car", [.cons a _] => .ok a
  | "car", [.nil] => .ok .nil
  | "cdr", [.cons _ b] => .ok b
  | "cdr", [.nil] => .ok .nil
  | "equal", [a, b] => .ok (toACL2Bool (a == b))
  | "=", [a, b] => .ok (toACL2Bool (a == b))
  | "not", [a] => .ok (toACL2Bool (¬ isTruthy a))
  | "list", args => .ok (SExpr.ofList args)
  | "append", [a, b] => .ok (append a b)
  | "consp", [.cons _ _] => .ok (toACL2Bool true)
  | "consp", [_] => .ok (toACL2Bool false)
  | "atom", [.cons _ _] => .ok (toACL2Bool false)
  | "atom", [_] => .ok (toACL2Bool true)
  | "true-listp", [a] => .ok (toACL2Bool (isTrueList a))
  | "integerp", [.atom (.number (.int _))] => .ok (toACL2Bool true)
  | "integerp", [_] => .ok (toACL2Bool false)
  | "natp", [.atom (.number (.int n))] => .ok (toACL2Bool (n >= 0))
  | "natp", [_] => .ok (toACL2Bool false)
  | "posp", [.atom (.number (.int n))] => .ok (toACL2Bool (n > 0))
  | "posp", [_] => .ok (toACL2Bool false)
  | "symbolp", [.atom (.symbol _)] => .ok (toACL2Bool true)
  | "symbolp", [.nil] => .ok (toACL2Bool true)
  | "symbolp", [_] => .ok (toACL2Bool false)
  | "stringp", [.atom (.string _)] => .ok (toACL2Bool true)
  | "stringp", [_] => .ok (toACL2Bool false)
  | "if", [c, t, e] => .ok (if isTruthy c then t else e)
  | "+", [.atom (.number (.int a)), .atom (.number (.int b))] => .ok (SExpr.atom (.number (.int (a + b))))
  | "binary-+", [.atom (.number (.int a)), .atom (.number (.int b))] => .ok (SExpr.atom (.number (.int (a + b))))
  | "-", [.atom (.number (.int a)), .atom (.number (.int b))] => .ok (SExpr.atom (.number (.int (a - b))))
  | "binary--", [.atom (.number (.int a)), .atom (.number (.int b))] => .ok (SExpr.atom (.number (.int (a - b))))
  | "*", [.atom (.number (.int a)), .atom (.number (.int b))] => .ok (SExpr.atom (.number (.int (a * b))))
  | "binary-*", [.atom (.number (.int a)), .atom (.number (.int b))] => .ok (SExpr.atom (.number (.int (a * b))))
  | "<", [.atom (.number (.int a)), .atom (.number (.int b))] => .ok (toACL2Bool (a < b))
  | "zp", [.atom (.number (.int n))] => .ok (toACL2Bool (n <= 0))
  | "zp", [_] => .ok (toACL2Bool true)
  | "evenp", [.atom (.number (.int n))] => .ok (toACL2Bool (n % 2 == 0))
  | "oddp", [.atom (.number (.int n))] => .ok (toACL2Bool (n % 2 != 0))
  | "/", [.atom (.number (.int a)), .atom (.number (.int b))] =>
      if b == 0 then .error "division by zero"
      else if a % b == 0 then .ok (SExpr.atom (.number (.int (a / b))))
      else
        let g := Nat.gcd a.natAbs b.toNat
        let n := a / Int.ofNat g
        let d := b.toNat / g
        if d == 1 then .ok (SExpr.atom (.number (.int n)))
        else .ok (SExpr.atom (.number (.rational n d)))
  | n, _ => .error s!"unknown built-in or wrong arity: {n}"

/-- Bind formals to arguments in a new environment. -/
def bindArgs (formals : List Symbol) (args : List SExpr) : EvalM Env := do
  if formals.length != args.length then
    throw s!"wrong number of arguments: expected {formals.length}, got {args.length}"
  else
    let mut env := {}
    for i in [0:formals.length] do
      env := env.insert formals[i]! args[i]!
    .ok env

/-- Evaluate an ACL2 expression in a given world and local environment. -/
partial def eval (w : World) (env : Env) (expr : SExpr) : EvalM SExpr :=
  match expr with
  | .nil => .ok .nil
  | .atom (.number n) => .ok (SExpr.atom (.number n))
  | .atom (.string s) => .ok (SExpr.atom (.string s))
  | .atom (.keyword k) => .ok (SExpr.atom (.keyword k))
  | .atom (.symbol s) =>
      match env.get? s with
      | some v => .ok v
      | none =>
          if s.normalizedName = "t" then .ok SExpr.t
          else if s.normalizedName = "nil" then .ok .nil
          else throw s!"unbound variable: {s.name}"
  | .cons (.atom (.symbol s)) argsExpr => do
      if s.isNamed "quote" then
        match argsExpr with
        | .cons v .nil => .ok v
        | _ => throw "malformed quote"
      else if s.isNamed "if" then
        match argsExpr with
        | .cons c (.cons t (.cons e .nil)) => do
            let cv ← eval w env c
            if isTruthy cv then eval w env t else eval w env e
        | _ => throw "malformed if"
      else if s.isNamed "let" then
        match argsExpr with
        | .cons bindings (.cons fbody .nil) => do
            let bList ← match bindings.toList? with | some l => .ok l | none => throw "invalid let bindings"
            let mut curEnv := env
            for b in bList do
              let bItems ← match b.toList? with | some l => .ok l | none => throw "invalid binding"
              match bItems with
              | [SExpr.atom (.symbol s), valExpr] => do
                  let v ← eval w env valExpr
                  curEnv := curEnv.insert s v
              | _ => throw "invalid binding format"
            eval w curEnv fbody
        | _ => throw "malformed let"
      else
        let args ← match argsExpr.toList? with | some l => .ok l | none => throw "invalid arguments"
        let argVals ← args.mapM (eval w env)
        match w.defs.get? s with
        | some (formals, fbody) =>
            if formals.length != argVals.length then
              throw s!"wrong number of arguments for {s.name}"
            else
              let mut newEnv := {}
              for i in [0:formals.length] do
                newEnv := newEnv.insert formals[i]! argVals[i]!
              eval w newEnv fbody
        | none => callBuiltin s.name argVals
  | _ => throw s!"invalid expression: {repr expr}"

/-- Expand macros in an s-expression. -/
partial def macroexpand (w : World) (sexpr : SExpr) : EvalM SExpr :=
  match sexpr with
  | .cons (.atom (.symbol s)) argsExpr => do
      match w.macros.get? s with
      | some (formals, fbody) =>
          let args ← match argsExpr.toList? with | some l => .ok l | none => throw "invalid macro arguments"
          let env' ← bindArgs formals args
          let expanded ← eval w env' fbody
          macroexpand w expanded
      | none =>
          let args ← match argsExpr.toList? with | some l => .ok l | none => throw "invalid arguments"
          let expandedArgs ← args.mapM (macroexpand w)
          .ok (SExpr.cons (.atom (.symbol s)) (SExpr.ofList expandedArgs))
  | .cons car cdr => do
      let car' ← macroexpand w car
      let cdr' ← macroexpand w cdr
      .ok (.cons car' cdr')
  | _ => .ok sexpr

private def parseOne (input : String) : EvalM SExpr := do
  let (sx, rest) ← Parse.parseSExpr input.toList
  let rest := Parse.skipWS rest
  if rest.isEmpty then
    pure sx
  else
    throw s!"unexpected trailing input: {String.ofList rest}"

private def parseWorld (input : String) : EvalM World := do
  let raw ← Parse.parseAll input
  pure (World.replay (raw.map Event.classify))

private def parseAndEval (input : String) : EvalM SExpr := do
  let sx ← parseOne input
  eval World.empty {} sx

private def evalInSource (src expr : String) : EvalM SExpr := do
  let w ← parseWorld src
  let sx ← parseOne expr
  eval w {} sx

private def uppercaseIfEvaluates : Bool :=
  match parseAndEval "(IF T 1 2)" with
  | .ok (SExpr.atom (.number (.int 1))) => true
  | _ => false

private def uppercaseLetEvaluates : Bool :=
  match parseAndEval "(LET ((X 5)) (BINARY-+ X 10))" with
  | .ok (SExpr.atom (.number (.int 15))) => true
  | _ => false

private def uppercaseImportedDefunEvaluates : Bool :=
  match evalInSource "(DEFUN FOO (X) (BINARY-+ X 1))" "(FOO 4)" with
  | .ok (SExpr.atom (.number (.int 5))) => true
  | _ => false

#guard uppercaseIfEvaluates
#guard uppercaseLetEvaluates
#guard uppercaseImportedDefunEvaluates

end Evaluator

end ACL2
