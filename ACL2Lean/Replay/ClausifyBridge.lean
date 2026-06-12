/-
  G3 Fragment B — the clausify bridge as a once-proved lemma.

  `clausifyPure` is the PURE fragment of ACL2's `clausify-input1` (the
  recompute-and-validate twin of the recorded checkpoints — validation
  stays in the driver); `disjoinTerm` is ACL2's `disjoin`. The bridge
  lemma `clausifyPure_sound` (to come, built on Fragment A's `dpLiftF`)
  replaces the per-leaf `peelClause`/`walkPosT`/`val*` walkers: ONE mutual
  structural induction proving that the output clause's truth gives the
  input's truth (pos) / falsity (neg).

  Fragment-local per invariant L1; world-parametric per L3. Design:
  docs/plans/2026-06-12_g3-consolidations.md (D-B1..3).
-/
import ACL2Lean.Replay.DpLift

namespace ACL2.Replay

open ACL2

/-- `(quote t)`, the result an equal-self literal reduces to. -/
def quoteT : SExpr := .cons (.atom (.symbol { name := "quote" })) (.cons SExpr.t .nil)

/-- `(quote nil)`. -/
def quoteNil : SExpr := .cons (.atom (.symbol { name := "quote" })) (.cons .nil .nil)

/-- ACL2's `disjoin` of a literal list: `(if l₁ 't (if l₂ 't … lₖ))`; a singleton
    is the literal itself; the empty clause is `'nil` (false). -/
def disjoinTerm : List SExpr → SExpr
  | [] => .cons (.atom (.symbol { name := "quote" })) (.cons .nil .nil)
  | [l] => l
  | l :: rest =>
    .cons (.atom (.symbol { name := "if" }))
      (.cons l (.cons quoteT (.cons (disjoinTerm rest) .nil)))

/-- ACL2's `dumb-negate-lit` (the pure fragment: strip a `not`, else wrap). -/
def dumbNegateLit (t : SExpr) : SExpr :=
  match t with
  | .cons (.atom (.symbol ns)) (.cons _ .nil) =>
    if ns.name == "not" then
      match t with
      | .cons _ (.cons inner .nil) => inner
      | _ => t
    else .cons (.atom (.symbol { name := "not" })) (.cons t .nil)
  | _ => .cons (.atom (.symbol { name := "not" })) (.cons t .nil)

/-- The PURE fragment of `clausify-input1` (no `expand-and-or`): `pos` is
    ACL2's `bool`. Recomputed for the walk and VALIDATED against the recorded
    checkpoints — divergence (an expansion fired) hard-fails upstream. -/
def clausifyPure (t : SExpr) (pos : Bool) : List SExpr :=
  if t == (if pos then quoteNil else quoteT) then []
  else match t with
  | .cons (.atom (.symbol ifS)) (.cons t1 (.cons t2 (.cons t3 .nil))) =>
    if ifS.name == "if" then
      if pos then
        if t3 == quoteT then clausifyPure t1 false ++ clausifyPure t2 true
        else if t2 == quoteT then clausifyPure t1 true ++ clausifyPure t3 true
        else [t]
      else
        if t3 == quoteNil then clausifyPure t1 false ++ clausifyPure t2 false
        else if t2 == quoteNil then clausifyPure t1 true ++ clausifyPure t3 false
        else [dumbNegateLit t]
    else if pos then [t] else [dumbNegateLit t]
  | _ => if pos then [t] else [dumbNegateLit t]

end ACL2.Replay
