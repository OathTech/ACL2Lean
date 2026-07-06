import ACL2Lean.Syntax

open ACL2

private def sym (n : String) : SExpr := .atom (.symbol { name := n })
private def int (n : Int) : SExpr := .atom (.number (.int n))

-- === SExpr.ofList / toList? ===

#guard SExpr.ofList [] = SExpr.nil
#guard SExpr.ofList [int 1, int 2] = SExpr.cons (int 1) (SExpr.cons (int 2) .nil)

#guard SExpr.nil.toList? = some []
#guard (SExpr.ofList [int 1, int 2]).toList? = some [int 1, int 2]
-- Improper list (dotted pair) → none
#guard (SExpr.cons (int 1) (int 2)).toList? = none
-- Atom → none
#guard (int 5).toList? = none

-- === headSymbol? ===

#guard (SExpr.ofList [sym "foo", int 1]).headSymbol? = some { name := "foo" }
#guard SExpr.nil.headSymbol? = none
#guard (int 5).headSymbol? = none
-- Keyword head → none
#guard (SExpr.cons (.atom (.keyword "k")) .nil).headSymbol? = none

-- === SExpr.toString ===

#guard SExpr.nil.toString = "NIL"
#guard SExpr.t.toString = "t"
#guard (SExpr.ofList [sym "a", sym "b"]).toString = "(a b)"
-- Dotted pair
#guard (SExpr.cons (sym "a") (sym "b")).toString = "(a . b)"
#guard (int 42).toString = "42"

-- === Symbol ===

#guard ({ name := "CAR" : Symbol }).normalizedName = "car"
-- isNamed uses direct comparison (kernel-reducible). All symbol names
-- and target strings must be lowercase (parser lowercases symbols).
#guard ({ name := "car" : Symbol }).isNamed "car"
#guard !({ name := "car" : Symbol }).isNamed "cdr"

-- === Event.classify ===

-- defun
#guard match Event.classify (SExpr.ofList [sym "defun", sym "foo", SExpr.ofList [sym "x"], sym "x"]) with
  | .ok (.defun { name := "foo", .. } [{ name := "x", .. }] _ _ _) => true
  | _ => false

-- defthm
#guard match Event.classify (SExpr.ofList [sym "defthm", sym "my-thm",
    SExpr.ofList [sym "equal", sym "x", sym "x"]]) with
  | .ok (.defthm { name := "my-thm", .. } _) => true
  | _ => false

-- in-package
#guard match Event.classify (SExpr.ofList [sym "in-package", .atom (.string "ACL2")]) with
  | .ok (.inPackage "ACL2") => true
  | _ => false

-- include-book
#guard match Event.classify (SExpr.ofList [sym "include-book", .atom (.string "arithmetic")]) with
  | .ok (.includeBook "arithmetic" _) => true
  | _ => false

-- local wrapping
#guard match Event.classify (SExpr.ofList [sym "local",
    SExpr.ofList [sym "defthm", sym "helper",
      SExpr.ofList [sym "equal", sym "x", sym "x"]]]) with
  | .ok (.local (.defthm { name := "helper", .. } _)) => true
  | _ => false

-- defconst
#guard match Event.classify (SExpr.ofList [sym "defconst", sym "*c*", int 42]) with
  | .ok (.defconst { name := "*c*", .. } _) => true
  | _ => false

-- known no-ops produce .skip
#guard match Event.classify (SExpr.ofList [sym "program"]) with
  | .ok (.skip _) => true
  | _ => false

-- malformed forms fail CLOSED (were panic!-defaults before the 2026-07-06
-- fail-closed audit)
#guard match Event.classify (SExpr.ofList [sym "defun", sym "foo"]) with
  | .error _ => true
  | _ => false
#guard match Event.classify (SExpr.ofList [sym "no-such-event", sym "x"]) with
  | .error _ => true
  | _ => false
#guard match Event.classify (SExpr.ofList [sym "defthm", sym "t1",
    SExpr.ofList [sym "equal", sym "x", sym "x"], .atom (.keyword "hints")]) with
  | .error _ => true
  | _ => false

-- === Event.flatten ===

-- local is peeled off
#guard match Event.flatten (.local (.defthm { name := "x" } { body := .nil })) with
  | [.defthm { name := "x", .. } _] => true
  | _ => false

-- mutual-recursion is flattened
#guard (Event.flatten (.mutualRecursion
  [.defun { name := "f" } [] none [] .nil,
   .defun { name := "g" } [] none [] .nil])).length = 2

-- === World.step ===

-- defun populates defs
#guard (World.empty.step (.defun { name := "foo" } [{ name := "x" }] none [] (sym "x"))).defs.contains { name := "foo" }

-- defthm populates theorems
#guard (World.empty.step (.defthm { name := "bar" } { body := .nil })).theorems.contains { name := "bar" }

-- defconst populates consts
#guard (World.empty.step (.defconst { name := "*c*" } (int 42))).consts.contains { name := "*c*" }

-- in-package updates package
#guard (World.empty.step (.inPackage "MY-PKG")).package.current = "MY-PKG"

-- defmacro populates macros
#guard (World.empty.step (.defmacro { name := "m" } [{ name := "x" }] none [] (sym "x"))).macros.contains { name := "m" }

-- defrec populates recs
#guard (World.empty.step (.defrec { name := "r" } [{ name := "f1" }])).recs.contains { name := "r" }

-- defstobj populates stobjs
#guard (World.empty.step (.defstobj { name := "st" } [])).stobjs.contains { name := "st" }

-- table populates tables
#guard (World.empty.step (.table { name := "tbl" } [])).tables.contains { name := "tbl" }

-- inTheory appends to theories
#guard (World.empty.step (.inTheory .nil)).theories.length = 1

-- local unwraps to inner event
#guard (World.empty.step (.local (.defun { name := "loc" } [] none [] .nil))).defs.contains { name := "loc" }

-- mutual-recursion flattens into world
#guard (World.empty.step (.mutualRecursion
  [.defun { name := "f" } [] none [] .nil,
   .defun { name := "g" } [] none [] .nil])).defs.contains { name := "f" }

-- encapsulate flattens into world
#guard (World.empty.step (.encapsulate
  [.defun { name := "enc" } [] none [] .nil])).defs.contains { name := "enc" }

-- skip is no-op
#guard (World.empty.step (.skip .nil)).defs.size = 0

-- include-book is no-op
#guard (World.empty.step (.includeBook "foo" [])).defs.size = 0

-- === TheoremOption ===

#guard match TheoremOption.fromSExprs
    [.atom (.keyword "hints"), .nil, .atom (.keyword "rule-classes"), .nil] with
  | .ok opts => opts.length = 2
  | .error _ => false
-- malformed plist fails closed
#guard match TheoremOption.fromSExprs [.atom (.keyword "hints")] with
  | .error _ => true
  | _ => false

#guard TheoremOption.findValue? [{ key := "hints", value := int 1 }] "hints" = some (int 1)
#guard TheoremOption.findValue? [{ key := "hints", value := int 1 }] "other" = none
