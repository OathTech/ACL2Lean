import ACL2Lean.Translator

open ACL2

private def sym (n : String) : SExpr := .atom (.symbol { name := n })
private def int (n : Int) : SExpr := .atom (.number (.int n))

-- === Quote translation ===

-- (quote lt) → SExpr.atom literal, NOT Logic.lt
#guard (Translator.translateExpr (SExpr.ofList [sym "quote", sym "lt"])).contains "SExpr.atom"
#guard !(Translator.translateExpr (SExpr.ofList [sym "quote", sym "lt"])).contains "Logic.lt"

-- (quote (a b)) → cons constructors
#guard (Translator.translateExpr (SExpr.ofList [sym "quote", SExpr.ofList [sym "a", sym "b"]])).contains "SExpr.cons"

-- (quote 42) → int literal
#guard (Translator.translateExpr (SExpr.ofList [sym "quote", int 42])).contains ".number (.int"

-- (quote "hi") → string literal
#guard (Translator.translateExpr (SExpr.ofList [sym "quote", .atom (.string "hi")])).contains ".string"

-- === Literal atoms ===

-- Bare nil → "SExpr.nil"
#guard Translator.translateExpr .nil = "SExpr.nil"

-- Bare t → "SExpr.t"
#guard Translator.translateExpr (sym "t") = "SExpr.t"

-- Bare nil symbol → "SExpr.nil"
#guard Translator.translateExpr (sym "nil") = "SExpr.nil"

-- Integer literal
#guard Translator.translateExpr (int 5) = "(SExpr.atom (.number (.int (5))))"

-- Rational literal
#guard (Translator.translateExpr (.atom (.number (.rational 1 3)))).contains "Logic.rational"

-- === Symbol translation ===

#guard Translator.translateSymbol { name := "binary-+" } = "Logic.plus"
#guard Translator.translateSymbol { name := "binary--" } = "Logic.minus"
#guard Translator.translateSymbol { name := "binary-*" } = "Logic.times"
#guard Translator.translateSymbol { name := "<" } = "Logic.lt"
#guard Translator.translateSymbol { name := "car" } = "Logic.car"
#guard Translator.translateSymbol { name := "cdr" } = "Logic.cdr"
#guard Translator.translateSymbol { name := "cons" } = "Logic.cons"
#guard Translator.translateSymbol { name := "equal" } = "Logic.equal"
#guard Translator.translateSymbol { name := "if" } = "Logic.if_"
#guard Translator.translateSymbol { name := "iff" } = "Logic.iff"
#guard Translator.translateSymbol { name := "force" } = "Logic.force"
#guard Translator.translateSymbol { name := "evens" } = "Logic.evens"
#guard Translator.translateSymbol { name := "odds" } = "Logic.odds"
#guard Translator.translateSymbol { name := "string-append" } = "Logic.string_append"
#guard Translator.translateSymbol { name := "true-listp" } = "Logic.trueListp"
#guard Translator.translateSymbol { name := "acl2-count" } = "SExpr.acl2Count"

-- Unmapped symbols: hyphen → underscore
#guard Translator.translateSymbol { name := "my-fun" } = "my_fun"

-- Special character escaping
#guard (Translator.translateSymbol { name := "check!" }).contains "_bang"
#guard (Translator.translateSymbol { name := "valid?" }).contains "_p"

-- === sanitizeName ===

#guard Translator.sanitizeName "my-theorem" = "my_theorem"
#guard Translator.sanitizeName "x=y" = "x_eq_y"
#guard Translator.sanitizeName "x+y" = "x_plus_y"
#guard Translator.sanitizeName "x*y" = "x_times_y"
#guard Translator.sanitizeName "x/y" = "x_div_y"
#guard Translator.sanitizeName "Logic.foo" = "foo"

-- === Expression translation ===

-- (list x y) → cons chain
#guard (Translator.translateExpr (SExpr.ofList [sym "list", sym "x", sym "y"])).contains "Logic.cons"

-- (case x (a 1) (otherwise 2)) → if/equal
#guard (Translator.translateExpr (SExpr.ofList
  [sym "case", sym "x",
   SExpr.ofList [sym "a", int 1],
   SExpr.ofList [sym "otherwise", int 2]])).contains "Logic.equal"

-- (case x ((a b) 1) (otherwise 2)) → or-guard for multi-key
#guard (Translator.translateExpr (SExpr.ofList
  [sym "case", sym "x",
   SExpr.ofList [SExpr.ofList [sym "a", sym "b"], int 1],
   SExpr.ofList [sym "otherwise", int 2]])).contains "Logic.or"

-- (let ((x 5)) (+ x 1)) → let binding
#guard (Translator.translateExpr (SExpr.ofList
  [sym "let",
   SExpr.ofList [SExpr.ofList [sym "x", int 5]],
   SExpr.ofList [sym "+", sym "x", int 1]])).contains "let x"

-- (let* ((x 5)) (+ x 1)) → also handled as let binding
#guard (Translator.translateExpr (SExpr.ofList
  [sym "let*",
   SExpr.ofList [SExpr.ofList [sym "x", int 5]],
   SExpr.ofList [sym "+", sym "x", int 1]])).contains "let x"

-- (cddr x) → cdr (cdr x)
#guard (Translator.translateExpr (SExpr.ofList [sym "cddr", sym "x"])).contains "Logic.cdr (Logic.cdr"

-- (cadr x) → car (cdr x)
#guard (Translator.translateExpr (SExpr.ofList [sym "cadr", sym "x"])).contains "Logic.car (Logic.cdr"

-- (1+ x) → plus x 1
#guard (Translator.translateExpr (SExpr.ofList [sym "1+", sym "x"])).contains "Logic.plus"

-- (1- x) → minus x 1
#guard (Translator.translateExpr (SExpr.ofList [sym "1-", sym "x"])).contains "Logic.minus"

-- (declare ...) → empty string
#guard Translator.translateExpr (SExpr.ofList [sym "declare", sym "anything"]) = ""

-- N-ary folding: (+ a b c) → nested plus
private def naryPlus : SExpr := SExpr.ofList [sym "+", sym "a", sym "b", sym "c"]
#guard (Translator.translateExpr naryPlus).contains "(Logic.plus a (Logic.plus b c))"

-- === Cond translation ===

-- (cond ((consp x) (foo x) (bar x))) → uses last body (bar), not first (foo)
private def condExpr : SExpr := SExpr.ofList
  [sym "cond",
   SExpr.ofList [SExpr.ofList [sym "consp", sym "x"],
                  SExpr.ofList [sym "foo", sym "x"],
                  SExpr.ofList [sym "bar", sym "x"]]]
#guard (Translator.translateExpr condExpr).contains "(bar x)"
#guard !(Translator.translateExpr condExpr).contains "(foo x)"

-- (cond (t val)) → direct translation of val
#guard Translator.translateExpr (SExpr.ofList
  [sym "cond", SExpr.ofList [sym "t", int 42]]) =
  "(SExpr.atom (.number (.int (42))))"

-- === collectVars ===

-- case skips key symbols
#guard !(Translator.collectVars (SExpr.ofList
  [sym "case", sym "x",
   SExpr.ofList [sym "a", int 1],
   SExpr.ofList [sym "otherwise", int 2]])).contains "a"

-- list collects args
#guard (Translator.collectVars (SExpr.ofList [sym "list", sym "x", sym "y"])).contains "x"
#guard (Translator.collectVars (SExpr.ofList [sym "list", sym "x", sym "y"])).contains "y"

-- quote returns []
#guard Translator.collectVars (SExpr.ofList [sym "quote", SExpr.ofList [sym "a", sym "b"]]) = []

-- if collects from all branches
#guard (Translator.collectVars (SExpr.ofList
  [sym "if", sym "c", sym "a", sym "b"])).contains "c"

-- let collects from bindings and body
#guard (Translator.collectVars (SExpr.ofList
  [sym "let", SExpr.ofList [SExpr.ofList [sym "x", sym "y"]], sym "x"])).contains "y"

-- declare returns no vars
#guard Translator.collectVars (SExpr.ofList [sym "declare", sym "anything"]) = []

-- === translateDefun ===

-- Non-recursive function → def, no termination
private def nonRecBody : SExpr := SExpr.ofList [sym "+", sym "x", sym "y"]
private def nonRecDefun := Translator.translateDefun { name := "add" } [{ name := "x" }, { name := "y" }] nonRecBody
#guard nonRecDefun.startsWith "def add"
#guard !nonRecDefun.contains "termination_by"
#guard !nonRecDefun.contains "partial"

-- Single cdr-recursive arg → acl2Count termination
private def cdrRecBody : SExpr := SExpr.ofList
  [sym "if", SExpr.ofList [sym "endp", sym "x"],
   int 0,
   SExpr.ofList [sym "+", int 1, SExpr.ofList [sym "foo", SExpr.ofList [sym "cdr", sym "x"]]]]
private def cdrRecDefun := Translator.translateDefun { name := "foo" } [{ name := "x" }] cdrRecBody
#guard cdrRecDefun.contains "termination_by"
#guard cdrRecDefun.contains "acl2Count"

-- Evens/odds recursion → evens/odds termination annotation
private def evensBody : SExpr := SExpr.ofList
  [sym "if", SExpr.ofList [sym "endp", SExpr.ofList [sym "cdr", sym "x"]],
   sym "x",
   SExpr.ofList [sym "foo", SExpr.ofList [sym "evens", sym "x"]]]
#guard (Translator.translateDefun { name := "foo" } [{ name := "x" }] evensBody).contains "acl2Count_evens_lt"

-- === translateDefthm ===

private def simpleBody : SExpr := SExpr.ofList [sym "equal", sym "x", sym "x"]
private def simpleThm := Translator.translateDefthm { name := "eq-self" } { body := simpleBody }
#guard simpleThm.contains "theorem eq_self"
#guard simpleThm.contains "Logic.toBool"
#guard simpleThm.contains "sorry"

-- === N-ary folding for and/or/times ===

-- (and a b c) → nested Logic.and
private def naryAnd : SExpr := SExpr.ofList [sym "and", sym "a", sym "b", sym "c"]
#guard (Translator.translateExpr naryAnd).contains "(Logic.and a (Logic.and b c))"

-- (or a b c) → nested Logic.or
private def naryOr : SExpr := SExpr.ofList [sym "or", sym "a", sym "b", sym "c"]
#guard (Translator.translateExpr naryOr).contains "(Logic.or a (Logic.or b c))"

-- (* a b c) → nested Logic.times
private def naryTimes : SExpr := SExpr.ofList [sym "*", sym "a", sym "b", sym "c"]
#guard (Translator.translateExpr naryTimes).contains "(Logic.times a (Logic.times b c))"

-- 2 args: no folding needed
#guard (Translator.translateExpr (SExpr.ofList [sym "+", sym "a", sym "b"])) = "(Logic.plus a b)"

-- Malformed if/case now panic! instead of producing sorry (not testable with #guard)

-- === nativeIf toggle ===

-- Default (nativeIf=false): uses Logic.if_
#guard (Translator.translateExpr (SExpr.ofList [sym "if", sym "c", sym "a", sym "b"])).contains "Logic.if_"

-- nativeIf=true: uses Lean's if/then/else
#guard (Translator.translateExpr (SExpr.ofList [sym "if", sym "c", sym "a", sym "b"]) true).contains "if Logic.toBool"
#guard !(Translator.translateExpr (SExpr.ofList [sym "if", sym "c", sym "a", sym "b"]) true).contains "Logic.if_"
