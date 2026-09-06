import ACL2Lean.Syntax

namespace ACL2

/-- The declared input of a VERIFY-GUARDS waterfall. This is execution-guard
metadata, not a logical theorem or a rule offer. Its tree is retained separately;
replaying guard proofs remains unsupported. -/
structure GuardObligation where
  names : List Symbol
  clauses : List (List SExpr)
  deriving Repr, Inhabited

def GuardObligation.parse (names clauses : SExpr) : Except String GuardObligation := do
  let some ns := names.toList? | throw "VERIFY-GUARDS: :NAMES is not a proper list"
  if ns.isEmpty then throw "VERIFY-GUARDS: empty :NAMES"
  let names ← ns.mapM fun
    | .atom (.symbol s) => pure s
    | n => throw s!"VERIFY-GUARDS: non-symbol name {repr n}"
  let some cs := clauses.toList? | throw "VERIFY-GUARDS: :CLAUSES is not a proper list"
  if cs.isEmpty then throw "VERIFY-GUARDS: empty waterfall obligation"
  let clauses ← cs.mapM fun c => match c.toList? with
    | some lits => pure lits
    | none => throw s!"VERIFY-GUARDS: improper clause {repr c}"
  return { names, clauses }

def GuardObligation.label (g : GuardObligation) : String :=
  s!"VERIFY-GUARDS ({String.intercalate " "
    (g.names.map (fun s => (SExpr.atom (.symbol s)).toString))})"

/-- ACL2 induct.lisp's `termify-clause-set`, including axioms.lisp's
`disjoin2` constant folding. The wrapper emits the exact argument from which
ACL2 constructs the waterfall's formula; no proof is inferred here. -/
def GuardObligation.formula (g : GuardObligation) : SExpr :=
  termify g.clauses
where
  quote (v : SExpr) := SExpr.ofList [.atom (.symbol { name := "QUOTE" }), v]
  ite (a b c : SExpr) := SExpr.ofList [.atom (.symbol { name := "IF" }), a, b, c]
  disjoin : List SExpr → SExpr
    | [] => quote .nil
    | [a] => a
    | a :: rest =>
      let b := disjoin rest
      if a == quote .t || b == quote .t then quote .t
      else if a == quote .nil then b
      else if b == quote .nil then a
      else ite a (quote .t) b
  termify : List (List SExpr) → SExpr
    | [] => quote .t
    | [c] => disjoin c
    | c :: rest => ite (disjoin c) (termify rest) (quote .nil)

end ACL2
