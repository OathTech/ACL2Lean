import ACL2Lean.Logic

namespace ACL2

open Logic

/-- The lexorder VIEW of an atomic value: what ACL2's `alphorder` actually
    compares. Symbols AND keywords collapse to (name, package-name) STRING
    pairs — keywords ARE symbols in ACL2, package "KEYWORD" (BUG-006);
    `nil`/`t` are the ordinary COMMON-LISP symbols named "NIL"/"T", NOT
    special "smallest" values (verified: `(lexorder nil 5)` = NIL — see
    docs/notes/2026-07-08_lexorder-semantics.md). The view carries plain
    strings rather than a `Symbol` value because the COMMON-LISP::NIL/T
    identities are deliberately UNREPRESENTABLE as `Symbol`s (`canonSym`,
    BUG-013): `SExpr.nil`/`SExpr.t` are their unique representations, which
    is exactly what makes this view INJECTIVE on SExpr values — the fact the
    order properties (antisymmetry/transitivity) rest on. -/
inductive LexView
  | number (v : Number)
  | char (c : UInt8)
  | string (s : String)
  | sym (name pkg : String)

/-- Ordering among broad view kinds. The number comparator below orders
    rationals before genuine complexes, both before characters. -/
def viewKind : LexView → Nat
  | .number _ => 0
  | .char _ => 1
  | .string _ => 2
  | .sym _ _ => 3

/-- Faithful `symbol<`-style ≤ (axioms.lisp `symbol<`): compare by
    symbol-NAME via `string<`, tie-break by PACKAGE-NAME via `string<`. We
    model ACL2 `string<` with Lean's lexicographic `String.<` (both compare
    char-by-char by code point). -/
def symbolLe (n1 p1 n2 p2 : String) : Bool :=
  if n1 < n2 then true
  else if n1 = n2 then p1 ≤ p2
  else false

/-- ACL2 alphorder on numbers: every rational precedes every genuine
    complex; within complexes compare real parts, then imaginary parts.
    Rational values retain exact cross-multiplication comparison. -/
def numberLe (a b : Number) : Bool :=
  match a, b with
  | .complex ar ai _, .complex br bi _ =>
    decide (ar < br ∨ (ar = br ∧ ai ≤ bi))
  | .complex .., _ => false
  | _, .complex .. => true
  | _, _ =>
    let r1 := Logic.toRat (.atom (.number a))
    let r2 := Logic.toRat (.atom (.number b))
    decide (r1.1 * (Int.ofNat r2.2) ≤ r2.1 * (Int.ofNat r1.2))

/-- The view of an SExpr for `lexorder`; a cons has no view. This map is
    INJECTIVE on SExpr values (proved: `lexView?_inj`, LexorderOrder.lean),
    which rests on the canonicity invariants: `SExpr.nil`/`SExpr.t` are the
    unique representations of the COMMON-LISP `NIL`/`T` views (BUG-013,
    `canonSym`), and `.keyword` is the unique representation of
    KEYWORD-package views (BUG-014, `canonSym`). -/
def lexView? : SExpr → Option LexView
  | .nil => some (.sym "NIL" "COMMON-LISP")
  | .t   => some (.sym "T" "COMMON-LISP")
  | .atom (.symbol s) => some (.sym s.name s.package)
  | .atom (.keyword k) => some (.sym k "KEYWORD")
  | .atom (.number v) => some (.number v)
  | .atom (.char c) => some (.char c)
  | .atom (.string s) => some (.string s)
  | .cons _ _ => none

/-- ACL2 `alphorder` on views (axioms.lisp:26995) as a Bool: order by class
    (`viewKind`: number < character < string < symbol) then within-class
    value.
    Numbers use `numberLe`: rational value order, then genuine complexes
    in component order. There is no separate integer/proper-ratio class. -/
def alphLe (a b : LexView) : Bool :=
  if viewKind a < viewKind b then true
  else if viewKind a > viewKind b then false
  else -- same kind
    match a, b with
    | .number v1, .number v2 => numberLe v1 v2
    | .char c1, .char c2 => decide (c1 ≤ c2)  -- by char-code
    | .string s1, .string s2 => decide (s1 ≤ s2)
    | .sym n1 p1, .sym n2 p2 => symbolLe n1 p1 n2 p2
    | _, _ => false -- unreachable (same kind guarantees same constructor)

/-- `lexorder x y` — total ordering on SExpr values, faithful to ACL2's
    `lexorder`/`alphorder` (axioms.lisp:27041/26995): atoms are ordered by
    their views (`alphLe`), conses are LARGER than any atom and compared
    lexicographically (car then cdr). `nil`/`t` are ordinary symbols
    (`lexView?`), not special. The order properties ACL2 admits as
    ground-zero rules (LEXORDER-REFLEXIVE, LEXORDER-ANTI-SYMMETRIC,
    LEXORDER-TRANSITIVE, LEXORDER-TOTAL — axioms.lisp:27154ff) are PROVED
    about this implementation in LexorderOrder.lean. -/
def lexorder (x y : SExpr) : SExpr :=
  match lexView? x, lexView? y with
  | some a, some b => if alphLe a b then .t else .nil
  | some _, none => .t  -- atom < cons
  | none, some _ => .nil -- cons > atom
  | none, none => -- both conses
    match x, y with
    | .cons a1 b1, .cons a2 b2 =>
      if a1 == a2 then lexorder b1 b2
      else lexorder a1 a2
    | _, _ => .nil -- unreachable (lexView? none ⟹ cons)


end ACL2
