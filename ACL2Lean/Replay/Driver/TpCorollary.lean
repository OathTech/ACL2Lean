import ACL2Lean.Syntax

namespace ACL2.Replay.Driver
open ACL2

/-- The EMITTED type-prescription corollary's CLASS — the shape of the
    value predicate `P` the TP prover builds from it. A return-path
    PRIMITIVE can only be admitted for a recognized class, because the
    Lean-side content of such a step is exactly that class's value-CLOSURE
    lemma (`tpClosure2`); an unrecognized corollary keeps the honest
    frontier. -/
inductive TpCorClass where
  /-- `(IF (INTEGERP (f …)) (NOT (< (f …) '0)) 'NIL)` — ACL2's
      `*ts-non-negative-integer*` (the emitted `:BASICTS 7`). -/
  | nonNegInt
  /-- `(ACL2-NUMBERP (f …))` — all seven numeric bits, `:BASICTS 127`. -/
  | acl2Numberp
  /-- `(CONSP (f …))` — ACL2's `*ts-cons*` (the emitted `:BASICTS 3072`). -/
  | consp
  /-- `(TRUE-LISTP (f …))` — ACL2's `*ts-true-list*` (`:BASICTS 1152`). -/
  | trueListp
  /-- `(IF (CONSP (f …)) 'T (EQUAL (f …) 'NIL))` — ACL2's
      `*ts-cons*` ∪ `*ts-nil*` (the emitted `:BASICTS 3200`), the
      "a list, possibly empty" prescription of a list-returning
      recursion (TP-replay arc increment 3). -/
  | conspOrNil
  /-- `(IF (CONSP (f …)) 'T (EQUAL (f …) <formal>))` — the ARGS-VALUED
      class (TP-replay arc increment 5): ACL2's prescription for
      `BINARY-APPEND`/`APP`, whose else-disjunct names a FORMAL, so the
      lifted predicate is indexed by that argument's VALUE
      (`mkTpHypTypeAv`'s hypothesis shape). The emitted `:BASICTS` is
      `*ts-cons*` (3072) — the corollary's TYPE-SET part; the equality
      disjunct is what covers the residue leaf (verdict `-1`), and it is
      carried by `tpArgLeafFact`, never by a mask. Which formal it is
      comes from `tpCorArgVar?`, off the emitted corollary. -/
  | conspOrArg
  deriving BEq, Repr, Inhabited

/-- ACL2's basic type-set MASK the class covers (`acl2/type-set-a.lisp`'s
    `def-basic-type-sets` bit order: 2^0 `*ts-zero*`, 2^1 `*ts-one*`, 2^2
    `*ts-integer>1*`, 2^3 positive-ratio, 2^4 negative-integer, 2^5
    negative-ratio, 2^6 complex-rational, 2^7 `*ts-nil*`, 2^8 `*ts-t*`,
    2^9 non-t-non-nil-symbol, 2^10 `*ts-proper-cons*`, 2^11
    `*ts-improper-cons*`, 2^12 string, 2^13 character). A leaf whose
    EMITTED verdict has a bit outside the mask is not covered by the
    corollary — frontier. Each mask is the ACL2 constant the corollary's
    recognizer names: `*ts-non-negative-integer*` = 0|1|2 = 7,
    `*ts-cons*` = proper|improper = 1024|2048 = 3072, `*ts-true-list*` =
    nil|proper-cons = 128|1024 = 1152, and the consp-or-nil `IF` =
    `*ts-cons*`|`*ts-nil*` = 3072|128 = 3200. -/
def TpCorClass.tsMask : TpCorClass → Int
  | .nonNegInt => 7
  | .acl2Numberp => 127
  | .consp => 3072
  | .trueListp => 1152
  | .conspOrNil => 3200
  | .conspOrArg => 3072

/-- Does the class's lifted predicate mention an ARGUMENT value (the
    args-valued corollaries — `mkTpHypTypeAv`'s shape)? Such a class's
    closure/leaf facts take that value as their leading parameter, and its
    hypothesis shape binds the argument values alongside the
    application's. -/
def TpCorClass.argIndexed : TpCorClass → Bool
  | .conspOrArg => true
  | _ => false

/-- Is the emitted leaf verdict `ts` inside the class's type-set `mask`?
    A NEGATIVE `ts` is a complement type-set (ACL2's `-1` = every type) and
    is never inside a finite mask. -/
def tsSubsumed (ts mask : Int) : Bool :=
  0 ≤ ts && (Nat.land ts.toNat mask.toNat == ts.toNat)

/-- The RESIDUE ARGUMENT of an args-valued corollary (TP-replay arc
    increment 5): the bare variable `Y` in
    `(IF (CONSP (f …)) 'T (EQUAL (f …) Y))`. The single matcher for that
    shape — `tpCorClass?` recognizes the class through it, and the walk
    reads the variable through it, so the two can never disagree. A
    QUOTED else-argument (`'NIL`) does not match here: it is the
    value-only `.conspOrNil` class. -/
def tpCorArgVar? (appPat cor : SExpr) : Option Symbol :=
  let app1 (f : String) (a : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := f })) (.cons a .nil)
  match cor with
  | .cons (.atom (.symbol ifS))
      (.cons c (.cons th (.cons (.cons (.atom (.symbol eqS))
        (.cons l (.cons (.atom (.symbol v)) .nil))) .nil))) =>
    if ifS.name == "IF" && eqS.name == "EQUAL" && c == app1 "CONSP" appPat
        && th == app1 "QUOTE" SExpr.t && l == appPat then some v
    else none
  | _ => none

/-- Recognize the EMITTED corollary's class. `appPat` is the fn's own
    application `(f formal…)` — the corollary's only non-constant part
    (except the args-valued class's residue formal, `tpCorArgVar?`).
    Exact-shape match: a corollary ACL2 emits in any other shape is
    unrecognized (frontier), never approximated. -/
def tpCorClass? (appPat cor : SExpr) : Option TpCorClass :=
  let app1 (f : String) (a : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := f })) (.cons a .nil)
  let app2 (f : String) (a b : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := f })) (.cons a (.cons b .nil))
  let quo (v : SExpr) : SExpr := app1 "QUOTE" v
  let ifE (c th e : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := "IF" }))
      (.cons c (.cons th (.cons e .nil)))
  if cor == ifE (app1 "INTEGERP" appPat)
      (app1 "NOT" (app2 "<" appPat (quo (.atom (.number (.int 0))))))
      (quo .nil) then some .nonNegInt
  else if cor == app1 "CONSP" appPat then some .consp
  else if cor == app1 "ACL2-NUMBERP" appPat then some .acl2Numberp
  else if cor == app1 "TRUE-LISTP" appPat then some .trueListp
  else if cor == ifE (app1 "CONSP" appPat) (quo SExpr.t)
      (app2 "EQUAL" appPat (quo .nil)) then some .conspOrNil
  else if (tpCorArgVar? appPat cor).isSome then some .conspOrArg
  else none

end ACL2.Replay.Driver
