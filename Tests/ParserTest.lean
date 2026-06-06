import ACL2Lean.Parser

open ACL2

private def parseOne (input : String) : Option SExpr :=
  match Parse.parseSExpr input.toList with
  | .ok (sx, rest) =>
    if (Parse.skipWS rest).isEmpty then some sx else none
  | .error _ => none

private def parseAll (input : String) : Option (List SExpr) :=
  match Parse.parseAll input with
  | .ok sxs => some sxs
  | .error _ => none

private def parseFails (input : String) : Bool :=
  match Parse.parseSExpr input.toList with
  | .error _ => true
  | .ok _ => false

-- === Atoms ===

-- nil → SExpr.nil (was .atom (.bool false) before Atom.bool removal)
#guard parseOne "nil" = some SExpr.nil

-- t → SExpr.t (was .atom (.bool true) before Atom.bool removal)
#guard parseOne "t" = some SExpr.t

-- Case-insensitive: NIL and T
#guard parseOne "NIL" = some SExpr.nil
#guard parseOne "T" = some SExpr.t

-- Integers
#guard parseOne "42" = some (.atom (.number (.int 42)))
#guard parseOne "-7" = some (.atom (.number (.int (-7))))
#guard parseOne "0" = some (.atom (.number (.int 0)))

-- Rational literals
#guard parseOne "3/4" = some (.atom (.number (.rational 3 4)))
#guard parseOne "-1/3" = some (.atom (.number (.rational (-1) 3)))

-- String literals
#guard parseOne "\"hello\"" = some (.atom (.string "hello"))
#guard parseOne "\"\"" = some (.atom (.string ""))

-- Keywords
#guard parseOne ":foo" = some (.atom (.keyword "foo"))
#guard parseOne ":SYSTEM" = some (.atom (.keyword "system"))

-- Symbols
#guard parseOne "car" = some (.atom (.symbol { name := "car" }))
#guard parseOne "CAR" = some (.atom (.symbol { name := "car" }))

-- Package-qualified symbols
#guard parseOne "ACL2::CAR" = some (.atom (.symbol { package := "ACL2", name := "car" }))

-- Escaped symbols with pipes
#guard parseOne "|My Symbol|" = some (.atom (.symbol { name := "My Symbol" }))

-- Character literals
#guard (parseOne "#\\a").isSome

-- === Lists ===

-- Empty list
#guard parseOne "()" = some SExpr.nil

-- Simple list
#guard parseOne "(1 2 3)" = some (SExpr.ofList
  [.atom (.number (.int 1)), .atom (.number (.int 2)), .atom (.number (.int 3))])

-- Nested list
#guard parseOne "(a (b c))" = some (SExpr.ofList
  [.atom (.symbol { name := "a" }),
   SExpr.ofList [.atom (.symbol { name := "b" }), .atom (.symbol { name := "c" })]])

-- === Quoting ===

-- 'T → (quote t)
#guard parseOne "'T" = some (SExpr.ofList [.atom (.symbol { name := "quote" }), SExpr.t])

-- '(1 2 3) → quoted cons chain
#guard parseOne "'(1 2 3)" = some (SExpr.ofList
  [ .atom (.symbol { name := "quote" })
  , SExpr.ofList [.atom (.number (.int 1)), .atom (.number (.int 2)), .atom (.number (.int 3))]
  ])

-- Quasiquote
#guard parseOne "`x" = some (SExpr.ofList
  [.atom (.symbol { name := "quasiquote" }), .atom (.symbol { name := "x" })])

-- Unquote
#guard parseOne ",x" = some (SExpr.ofList
  [.atom (.symbol { name := "unquote" }), .atom (.symbol { name := "x" })])

-- Unquote-splicing
#guard parseOne ",@x" = some (SExpr.ofList
  [.atom (.symbol { name := "unquote-splicing" }), .atom (.symbol { name := "x" })])

-- === Comments ===

-- Line comment
#guard parseOne "; comment\n42" = some (.atom (.number (.int 42)))

-- Block comment
#guard parseOne "#| block |# 42" = some (.atom (.number (.int 42)))

-- === parseAll ===

-- Multiple expressions
#guard parseAll "nil t 42" = some [SExpr.nil, SExpr.t, .atom (.number (.int 42))]

-- Empty input
#guard parseAll "" = some []

-- Single expression
#guard parseAll "(+ 1 2)" = some [SExpr.ofList
  [.atom (.symbol { name := "+" }), .atom (.number (.int 1)), .atom (.number (.int 2))]]

-- === Discard syntax ===

-- #- discards the next form, then parses the one after
#guard parseOne "#- foo 42" = some (.atom (.number (.int 42)))

-- #+ discards TWO forms (feature + body), then parses the one after
#guard parseOne "#+ acl2 (do-stuff) 42" = some (.atom (.number (.int 42)))

-- === String escapes ===

-- String with escaped quote
#guard parseOne "\"a\\\"b\"" = some (.atom (.string "a\"b"))

-- === Nested block comments ===

#guard parseOne "#| outer #| inner |# still comment |# 42" = some (.atom (.number (.int 42)))

-- === Error cases ===

-- Unmatched close paren
#guard parseFails ")"

-- Empty input for parseSExpr
#guard parseFails ""

-- Unterminated string
#guard parseFails "\"hello"

-- Unterminated list
#guard parseFails "(1 2"
