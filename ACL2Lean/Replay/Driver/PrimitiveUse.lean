import ACL2Lean.Replay.Driver.NodeCore
import ACL2Lean.NumericRational
import ACL2Lean.NumericPositive

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

private theorem rationalReconstructionTrue (v : SExpr) :
    Logic.implies (Logic.rationalp v)
      (Logic.equal (Logic.times (Logic.reciprocal (Logic.denominator v)) (Logic.numerator v)) v) ≠
        SExpr.nil :=
  (Logic.implies_ne_nil_iff _ _).mpr fun h =>
    (Logic.equal_ne_nil_iff _ _).mpr (Logic.rational_reconstruct v h)

open Logic in
private theorem positiveSchema (a b : SExpr) :
    (bif toBool (implies (bif toBool (lt (.atom (.number (.int 0))) a)
        then lt (.atom (.number (.int 0))) b else .nil)
      (lt (.atom (.number (.int 0))) (plus a b))) then
      implies (bif toBool (rationalp a) then
        (bif toBool (rationalp b) then
          (bif toBool (lt (.atom (.number (.int 0))) a)
            then lt (.atom (.number (.int 0))) b else .nil) else .nil) else .nil)
        (lt (.atom (.number (.int 0))) (times a b)) else .nil) ≠ SExpr.nil := by
  apply ACL2.Replay.and_value_ne_nil
  · apply (ACL2.Replay.Logic.implies_ne_nil_iff _ _).mpr
    intro h
    exact Logic.positiveAdd a b (ACL2.Replay.cond_tnil_ne_nil_test h)
      (ACL2.Replay.cond_tnil_ne_nil_then h)
  · apply (ACL2.Replay.Logic.implies_ne_nil_iff _ _).mpr
    intro h
    have h1 := ACL2.Replay.cond_tnil_ne_nil_then h
    have h2 := ACL2.Replay.cond_tnil_ne_nil_then h1
    exact Logic.positiveTimes a b (ACL2.Replay.cond_tnil_ne_nil_test h)
      (ACL2.Replay.cond_tnil_ne_nil_test h1)
      (ACL2.Replay.cond_tnil_ne_nil_test h2) (ACL2.Replay.cond_tnil_ne_nil_then h2)

private def primitiveEqualityTrue (lhs rhs law : Expr) : MetaM Expr := do
  mkAppM ``Iff.mpr #[← mkAppM ``Logic.equal_ne_nil_iff #[lhs, rhs], law]

/-- A named primitive axiom used through :USE rather than a rewrite rune.
Its source schema is instantiated with the recorded translated substitution
and checked verbatim against :HYPS. The ordinary USE consumer still replays
the application clause; this supplies only the cited axiom premise. -/
def primitiveUseInstance? (cfg : ReplayConfig) (ctx : ReplayCtx) (name : String)
    (subst : List (Symbol × SExpr)) (hyp : SExpr) : MetaM (Option (Expr × ReplayCtx)) := do
  -- The exact translated schemas from axioms.lisp. Only these named
  -- primitive axioms are supplied here; book theorems remain dependencies.
  let sym := fun n => SExpr.atom (.symbol { name := n })
  let app := fun n xs => SExpr.cons (sym n) (SExpr.ofList xs)
  let x := sym "X"
  let y := sym "Y"
  let z := sym "Z"
  let distLhs := app "BINARY-*" [x, app "BINARY-+" [y, z]]
  let distRhs := app "BINARY-+" [app "BINARY-*" [x, y], app "BINARY-*" [x, z]]
  let assocLhs := app "BINARY-*" [app "BINARY-*" [x, y], z]
  let assocRhs := app "BINARY-*" [x, app "BINARY-*" [y, z]]
  let den := app "DENOMINATOR" [x]
  let denRhs := app "IF" [app "RATIONALP" [x], den,
    app "QUOTE" [.atom (.number (.int 1))]]
  let zero := app "QUOTE" [.atom (.number (.int 0))]
  let both := fun a b => app "IF" [a, b, quoteNil]
  let positiveXY := both (app "<" [zero, x]) (app "<" [zero, y])
  let positive := both
    (app "IMPLIES" [positiveXY, app "<" [zero, app "BINARY-+" [x, y]]])
    (app "IMPLIES" [both (app "RATIONALP" [x]) (both (app "RATIONALP" [y]) positiveXY),
      app "<" [zero, app "BINARY-*" [x, y]]])
  let schema? := match name with
    | "POSITIVE" => some positive
    | "DISTRIBUTIVITY" => some (app "EQUAL" [distLhs, distRhs])
    | "ASSOCIATIVITY-OF-*" => some (app "EQUAL" [assocLhs, assocRhs])
    | "RATIONAL-IMPLIES2" => some (app "IMPLIES" [app "RATIONALP" [x],
        app "EQUAL" [app "BINARY-*" [app "UNARY-/" [den], app "NUMERATOR" [x]], x]])
    | "COMPLETION-OF-DENOMINATOR" => some (app "EQUAL" [den, denRhs])
    | _ => none
  let some schema := schema? | return none
  let instantiate := substTerm (subst.map (·.1)) (subst.map (·.2))
  unless instantiate schema == hyp do
    throwError "primitive use:{name}: recorded substitution disagrees with :HYPS"
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx hyp
  let vx ← ctxValExpr cfg ctx (instantiate x)
  let hne ← match name with
    | "POSITIVE" => mkAppM ``positiveSchema #[vx, ← ctxValExpr cfg ctx (instantiate y)]
    | "DISTRIBUTIVITY" => do
      let law ← mkAppM ``Logic.times_add #[vx,
        ← ctxValExpr cfg ctx (instantiate y), ← ctxValExpr cfg ctx (instantiate z)]
      primitiveEqualityTrue (← ctxValExpr cfg ctx (instantiate distLhs))
        (← ctxValExpr cfg ctx (instantiate distRhs)) law
    | "ASSOCIATIVITY-OF-*" => do
      let law ← mkAppM ``Logic.times_assoc #[vx,
        ← ctxValExpr cfg ctx (instantiate y), ← ctxValExpr cfg ctx (instantiate z)]
      primitiveEqualityTrue (← ctxValExpr cfg ctx (instantiate assocLhs))
        (← ctxValExpr cfg ctx (instantiate assocRhs)) law
    | "RATIONAL-IMPLIES2" => mkAppM ``rationalReconstructionTrue #[vx]
    | "COMPLETION-OF-DENOMINATOR" => do
      let law ← mkAppM ``Logic.denominator_completion #[vx]
      primitiveEqualityTrue (← ctxValExpr cfg ctx (instantiate den))
        (← ctxValExpr cfg ctx (instantiate denRhs)) law
    | _ => throwError "primitive USE schema has no proof handler: {name}"
  let pf ← mkAppM ``evtrue_of_conv_ne_nil #[← ctxValProof cfg ctx hyp, hne]
  return some (pf, ctx)

end ACL2.Replay.Driver
