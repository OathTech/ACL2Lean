/-
  Total ACL2 evaluator with fuel-bounded recursion.

  This defines the semantics of ACL2 terms (s-expressions) in a given
  World environment. It is total (fuel parameter for termination) and
  serves as the semantic anchor for the verified rewriter's soundness proof.
-/
import ACL2Lean.Syntax
import ACL2Lean.Logic
import ACL2Lean.Parser

namespace ACL2

/-- Bind function formals to argument values, producing a new environment. -/
def bindArgs : List Symbol → List SExpr → Env
  | f :: fs, v :: vs => (bindArgs fs vs).insert f v
  | _, _ => {}

/-- Dispatch an ACL2 built-in primitive by normalized name.
    Returns SExpr.nil for unknown functions or wrong arity. -/
def callBuiltin (name : String) (args : List SExpr) : SExpr :=
  match name, args with
  -- Core constructors/accessors
  | "cons", [a, b] => .cons a b
  | "car", [a] => Logic.car a
  | "cdr", [a] => Logic.cdr a
  -- Predicates
  | "consp", [a] => Logic.consp a
  | "atom", [a] => Logic.atom a
  | "endp", [a] => Logic.endp a
  | "equal", [a, b] => Logic.equal a b
  | "eql", [a, b] => Logic.equal a b
  | "not", [a] => Logic.not a
  -- Arithmetic (canonical binary forms)
  | "binary-+", [a, b] => Logic.plus a b
  | "binary-*", [a, b] => Logic.times a b
  | "unary--", [a] =>
      let (n, d) := Logic.toRat a
      Logic.mkNumber (-n) d
  | "unary-/", [a] =>
      let (n, d) := Logic.toRat a
      if n == 0 then .atom (.number (.int 0))
      else if n > 0 then Logic.mkNumber (Int.ofNat d) n.natAbs
      else Logic.mkNumber (-(Int.ofNat d)) n.natAbs
  -- Arithmetic aliases (for raw/unexpanded source)
  | "+", [a, b] => Logic.plus a b
  | "-", [a] =>
      let (n, d) := Logic.toRat a
      Logic.mkNumber (-n) d
  | "-", [a, b] => Logic.minus a b
  | "*", [a, b] => Logic.times a b
  | "1+", [a] => Logic.plus (.atom (.number (.int 1))) a
  | "1-", [a] => Logic.minus a (.atom (.number (.int 1)))
  -- Comparisons
  | "<", [a, b] => Logic.lt a b
  -- Type predicates
  | "integerp", [a] => Logic.integerp a
  | "natp", [a] => Logic.natp a
  | "posp", [a] => Logic.posp a
  | "rationalp", [a] =>
      match a with | .atom (.number _) => .t | _ => .nil
  | "acl2-numberp", [a] =>
      match a with | .atom (.number _) => .t | _ => .nil
  | "zp", [a] => Logic.zp a
  | "symbolp", [a] =>
      match a with | .atom (.symbol _) | .nil => .t | _ => .nil
  | "stringp", [a] => Logic.stringp a
  -- Fixers
  | "fix", [a] =>
      match a with | .atom (.number _) => a | _ => .atom (.number (.int 0))
  | "nfix", [a] =>
      match a with
      | .atom (.number (.int n)) => if n >= 0 then a else .atom (.number (.int 0))
      | _ => .atom (.number (.int 0))
  | "ifix", [a] =>
      match a with | .atom (.number (.int _)) => a | _ => .atom (.number (.int 0))
  -- Logic
  | "implies", [a, b] => Logic.implies a b
  | "iff", [a, b] => Logic.iff a b
  -- List operations
  | "true-listp", [a] => Logic.trueListp a
  | "len", [a] => Logic.len a
  | "list", xs => SExpr.ofList xs
  -- Identity functions (proof hints with no logical content)
  | "force", [a] => a
  | "double-rewrite", [a] => a
  | "hide", [a] => a
  -- Unknown function or wrong arity
  | _, _ => .nil

/-- Total ACL2 evaluator with fuel-bounded recursion.
    Returns SExpr.nil on fuel exhaustion or evaluation errors.
    This is the semantic definition of what ACL2 terms mean. -/
def eval (fuel : Nat) (w : World) (env : Env) (term : SExpr) : SExpr :=
  match fuel with
  | 0 => .nil
  | fuel + 1 =>
    match term with
    | .nil => .nil
    | .atom (.number n) => .atom (.number n)
    | .atom (.string s) => .atom (.string s)
    | .atom (.keyword k) => .atom (.keyword k)
    | .atom (.symbol s) =>
        match env.get? s with
        | some v => v
        | none =>
            if s.isNamed "t" then SExpr.t
            else .nil  -- NIL or unbound variable
    | .cons (.atom (.symbol s)) argsExpr =>
        if s.isNamed "quote" then
          match argsExpr with
          | .cons v .nil => v
          | _ => .nil
        else if s.isNamed "if" then
          match argsExpr.toList? with
          | some [c, t, e] =>
              if Logic.toBool (eval fuel w env c) then
                eval fuel w env t
              else
                eval fuel w env e
          | _ => .nil
        else if s.isNamed "let" || s.isNamed "let*" then
          match argsExpr.toList? with
          | some [bindings, body] =>
              match bindings.toList? with
              | some bList =>
                  let env' := bList.foldl (fun acc b =>
                    match b.toList? with
                    | some [.atom (.symbol var), valExpr] =>
                        acc.insert var (eval fuel w acc valExpr)
                    | _ => acc) env
                  eval fuel w env' body
              | none => .nil
          | _ => .nil
        else
          -- Function call: evaluate args, then dispatch
          match argsExpr.toList? with
          | some args =>
              let argVals := args.map (fun a => eval fuel w env a)
              match w.defs.get? s with
              | some (formals, body) =>
                  if formals.length = argVals.length then
                    eval fuel w (bindArgs formals argVals) body
                  else .nil
              | none => callBuiltin s.normalizedName argVals
          | none => .nil
    | _ => .nil

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
  { defs := ({} : Std.HashMap Symbol (List Symbol × SExpr))
      |>.insert (sym "my-len") ([sym "x"], myLenBody)
      |>.insert (sym "my-app") ([sym "x", sym "y"], myAppBody) }

-- Helper: make a quoted literal
private def quoted (v : SExpr) : SExpr :=
  mkCall "quote" [v]

-- Helper: make a cons-list of symbol atoms
private def symList (names : List String) : SExpr :=
  SExpr.ofList (names.map (fun n => SExpr.atom (.symbol (sym n))))

-- Test 1: (my-len nil) = 0
#guard eval 100 simpleWorld {} (mkCall "my-len" [.nil])
    == .atom (.number (.int 0))

-- Test 2: (my-len '(a b c)) = 3
#guard eval 100 simpleWorld {} (mkCall "my-len" [quoted (symList ["a", "b", "c"])])
    == .atom (.number (.int 3))

-- Test 3: (my-app '(a b) '(c)) = (a b c)
#guard eval 100 simpleWorld {} (mkCall "my-app" [quoted (symList ["a", "b"]),
                                                  quoted (symList ["c"])])
    == symList ["a", "b", "c"]

-- Test 4: (my-app nil y) = y, with y bound to '(d)
private def envY : Env := ({} : Env).insert (sym "y") (symList ["d"])
#guard eval 100 simpleWorld (({} : Env).insert (sym "x") .nil |>.insert (sym "y") (symList ["d"]))
    (mkCall "my-app" [mkVar "x", mkVar "y"])
    == symList ["d"]

-- Test 5: the theorem formula with x=nil, y=nil
-- (equal (my-len (my-app x y)) (+ (my-len x) (my-len y)))
-- When x=nil, y=nil: my-app nil nil = nil, my-len nil = 0, equal 0 (+ 0 0) = equal 0 0 = T
private def formula : SExpr :=
  mkCall "equal" [mkCall "my-len" [mkCall "my-app" [mkVar "x", mkVar "y"]],
                  mkCall "+" [mkCall "my-len" [mkVar "x"],
                              mkCall "my-len" [mkVar "y"]]]

private def envNilNil : Env :=
  ({} : Env).insert (sym "x") .nil |>.insert (sym "y") .nil

#guard eval 100 simpleWorld envNilNil formula == SExpr.t

-- Test 6: formula with x = '(a), y = nil
-- my-app (a) nil = (a), my-len (a) = 1, my-len nil = 0, equal 1 (+ 1 0) = equal 1 1 = T
private def envOneNil : Env :=
  ({} : Env).insert (sym "x") (symList ["a"]) |>.insert (sym "y") .nil

#guard eval 100 simpleWorld envOneNil formula == SExpr.t

-- Test 7: formula with x = '(a b), y = '(c)
-- my-app (a b) (c) = (a b c), my-len (a b c) = 3
-- my-len (a b) = 2, my-len (c) = 1, + 2 1 = 3, equal 3 3 = T
private def envTwoOne : Env :=
  ({} : Env).insert (sym "x") (symList ["a", "b"]) |>.insert (sym "y") (symList ["c"])

#guard eval 100 simpleWorld envTwoOne formula == SExpr.t

-- Test 8: fuel exhaustion returns nil
#guard eval 0 simpleWorld envNilNil formula == .nil

-- Test 9: IF special form
#guard eval 10 World.empty {} (mkCall "if" [SExpr.t, .atom (.number (.int 1)), .atom (.number (.int 2))])
    == .atom (.number (.int 1))
#guard eval 10 World.empty {} (mkCall "if" [.nil, .atom (.number (.int 1)), .atom (.number (.int 2))])
    == .atom (.number (.int 2))

-- Test 10: QUOTE
#guard eval 10 World.empty {} (mkCall "quote" [symList ["a", "b"]])
    == symList ["a", "b"]

-- Test 11: LET
-- (let ((x 5)) (+ x 3)) = 8
private def letExpr : SExpr :=
  mkCall "let" [SExpr.ofList [SExpr.ofList [mkVar "x", .atom (.number (.int 5))]],
                mkCall "+" [mkVar "x", .atom (.number (.int 3))]]
#guard eval 10 World.empty {} letExpr == .atom (.number (.int 8))

-- Helper: integer literal
private def int (n : Int) : SExpr := .atom (.number (.int n))

/-! ### Builtin arithmetic -/

-- binary-+
#guard eval 10 World.empty {} (mkCall "binary-+" [int 3, int 4]) == int 7
#guard eval 10 World.empty {} (mkCall "binary-+" [int (-2), int 5]) == int 3
-- + (raw alias)
#guard eval 10 World.empty {} (mkCall "+" [int 10, int 20]) == int 30
-- binary-*
#guard eval 10 World.empty {} (mkCall "binary-*" [int 3, int 7]) == int 21
-- unary-- (negation)
#guard eval 10 World.empty {} (mkCall "unary--" [int 5]) == int (-5)
#guard eval 10 World.empty {} (mkCall "unary--" [int 0]) == int 0
-- - (binary subtraction alias)
#guard eval 10 World.empty {} (mkCall "-" [int 10, int 3]) == int 7
-- < (less than)
#guard eval 10 World.empty {} (mkCall "<" [int 3, int 5]) == SExpr.t
#guard eval 10 World.empty {} (mkCall "<" [int 5, int 3]) == .nil
#guard eval 10 World.empty {} (mkCall "<" [int 3, int 3]) == .nil
-- non-numeric arithmetic coerces to 0
#guard eval 10 World.empty {} (mkCall "binary-+" [.nil, int 5]) == int 5

/-! ### Type predicates -/

#guard eval 10 World.empty {} (mkCall "consp" [mkCall "cons" [int 1, .nil]]) == SExpr.t
#guard eval 10 World.empty {} (mkCall "consp" [.nil]) == .nil
#guard eval 10 World.empty {} (mkCall "consp" [int 5]) == .nil
#guard eval 10 World.empty {} (mkCall "integerp" [int 42]) == SExpr.t
#guard eval 10 World.empty {} (mkCall "integerp" [.nil]) == .nil
#guard eval 10 World.empty {} (mkCall "natp" [int 0]) == SExpr.t
#guard eval 10 World.empty {} (mkCall "natp" [int (-1)]) == .nil
#guard eval 10 World.empty {} (mkCall "zp" [int 0]) == SExpr.t
#guard eval 10 World.empty {} (mkCall "zp" [int 5]) == .nil
#guard eval 10 World.empty {} (mkCall "atom" [int 3]) == SExpr.t
#guard eval 10 World.empty {} (mkCall "atom" [mkCall "cons" [.nil, .nil]]) == .nil
#guard eval 10 World.empty {} (mkCall "symbolp" [mkVar "foo"]) == SExpr.t
#guard eval 10 World.empty {} (mkCall "symbolp" [int 5]) == .nil

/-! ### Core accessors -/

#guard eval 10 World.empty {} (mkCall "car" [mkCall "cons" [int 1, int 2]]) == int 1
#guard eval 10 World.empty {} (mkCall "car" [.nil]) == .nil
#guard eval 10 World.empty {} (mkCall "cdr" [mkCall "cons" [int 1, int 2]]) == int 2
#guard eval 10 World.empty {} (mkCall "cdr" [.nil]) == .nil
#guard eval 10 World.empty {} (mkCall "cons" [int 1, int 2]) == .cons (int 1) (int 2)
#guard eval 10 World.empty {} (mkCall "equal" [int 5, int 5]) == SExpr.t
#guard eval 10 World.empty {} (mkCall "equal" [int 5, int 6]) == .nil
#guard eval 10 World.empty {} (mkCall "not" [SExpr.t]) == .nil
#guard eval 10 World.empty {} (mkCall "not" [.nil]) == SExpr.t

/-! ### Fixers and identity functions -/

#guard eval 10 World.empty {} (mkCall "fix" [int 7]) == int 7
#guard eval 10 World.empty {} (mkCall "fix" [.nil]) == int 0
#guard eval 10 World.empty {} (mkCall "force" [int 42]) == int 42
#guard eval 10 World.empty {} (mkCall "hide" [SExpr.t]) == SExpr.t

/-! ### List operations -/

#guard eval 10 World.empty {} (mkCall "endp" [.nil]) == SExpr.t
#guard eval 10 World.empty {} (mkCall "endp" [mkCall "cons" [.nil, .nil]]) == .nil
#guard eval 10 World.empty {} (mkCall "len" [mkCall "cons" [.nil, mkCall "cons" [.nil, .nil]]]) == int 2
#guard eval 10 World.empty {} (mkCall "len" [.nil]) == int 0

/-! ### Error behavior (wrong arity, unknown function) -/

-- Wrong arity returns nil (total eval, no exceptions)
#guard eval 10 World.empty {} (mkCall "car" []) == .nil
#guard eval 10 World.empty {} (mkCall "cons" [int 1]) == .nil
-- Unknown function returns nil
#guard eval 10 World.empty {} (mkCall "nonexistent-fn" [int 1]) == .nil
-- Unbound variable returns nil
#guard eval 10 World.empty {} (mkVar "unbound") == .nil

/-! ### Variable and symbol evaluation -/

-- T evaluates to itself
#guard eval 10 World.empty {} (mkVar "t") == SExpr.t
-- nil evaluates to nil
#guard eval 10 World.empty {} .nil == .nil
-- Bound variable returns its value
#guard eval 10 World.empty (({} : Env).insert (sym "x") (int 42)) (mkVar "x") == int 42

end Tests

end ACL2
