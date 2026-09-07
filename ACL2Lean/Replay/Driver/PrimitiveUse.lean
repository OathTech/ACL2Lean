import ACL2Lean.Replay.Driver.NodeCore
import ACL2Lean.NumericRational
import ACL2Lean.NumericPositive
import ACL2Lean.NumericComplexAxioms
import ACL2Lean.NumericAdditionCompletion

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

private theorem rationalReconstructionTrue (v : SExpr) :
    Logic.implies (Logic.rationalp v)
      (Logic.equal (Logic.times (Logic.reciprocal (Logic.denominator v)) (Logic.numerator v)) v) ≠
        SExpr.nil :=
  (Logic.implies_ne_nil_iff _ _).mpr fun h =>
    (Logic.equal_ne_nil_iff _ _).mpr (Logic.rational_reconstruct v h)

private theorem rationalPairImplicationTrue (x y consequence : SExpr)
    (h : Logic.rationalp x ≠ .nil → Logic.rationalp y ≠ .nil → consequence ≠ .nil) :
    Logic.implies (bif Logic.toBool (Logic.rationalp x) then Logic.rationalp y else .nil)
      consequence ≠ .nil :=
  (Logic.implies_ne_nil_iff _ _).mpr fun hg =>
    h (cond_tnil_ne_nil_test hg) (cond_tnil_ne_nil_then hg)

private theorem complexDefinitionTrue (x y : SExpr) :
    Logic.implies (bif Logic.toBool (Logic.rationalp x) then Logic.rationalp y else .nil)
      (Logic.equal (Logic.complex x y)
        (Logic.plus x (Logic.times (.atom (.number (.complex 0 1 (by decide)))) y))) ≠ .nil :=
  rationalPairImplicationTrue x y _ fun hx hy =>
    (Logic.equal_ne_nil_iff _ _).mpr (Logic.complex_definition x y hx hy)

private theorem realpartComplexTrue (x y : SExpr) :
    Logic.implies (bif Logic.toBool (Logic.rationalp x) then Logic.rationalp y else .nil)
      (Logic.equal (Logic.realpart (Logic.complex x y)) x) ≠ .nil :=
  rationalPairImplicationTrue x y _ fun hx _ =>
    (Logic.equal_ne_nil_iff _ _).mpr (Logic.realpart_complex_of_rational x y hx)

private theorem imagpartComplexTrue (x y : SExpr) :
    Logic.implies (bif Logic.toBool (Logic.rationalp x) then Logic.rationalp y else .nil)
      (Logic.equal (Logic.imagpart (Logic.complex x y)) y) ≠ .nil :=
  rationalPairImplicationTrue x y _ fun _ hy =>
    (Logic.equal_ne_nil_iff _ _).mpr (Logic.imagpart_complex_of_rational x y hy)

private theorem completionOrderLaw (x y : SExpr) : Logic.lt x y =
    (bif Logic.toBool (bif Logic.toBool (Logic.rationalp x) then Logic.rationalp y else .nil)
      then Logic.lt x y else
      let x1 := bif Logic.toBool (Logic.acl2Numberp x) then x else .atom (.number (.int 0))
      let y1 := bif Logic.toBool (Logic.acl2Numberp y) then y else .atom (.number (.int 0))
      bif Logic.toBool (Logic.lt (Logic.realpart x1) (Logic.realpart y1)) then
        Logic.lt (Logic.realpart x1) (Logic.realpart y1) else
        (bif Logic.toBool (Logic.equal (Logic.realpart x1) (Logic.realpart y1)) then
          Logic.lt (Logic.imagpart x1) (Logic.imagpart y1) else .nil)) := by
  simpa only [gz_def_fix] using Logic.lt_completion x y

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
and transported through its recorded ground folds, then checked exactly
against :HYPS. The ordinary USE consumer still replays
the application clause; this supplies only the cited axiom premise. -/
def primitiveUseInstance? (cfg : ReplayConfig) (ctx : ReplayCtx) (name : String)
    (subst : List (Symbol × SExpr)) (hyp : SExpr)
    (folds : List SubstitutionFold := []) : MetaM (Option (Expr × ReplayCtx)) := do
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
  let complexSchema := app "IMPLIES" [both (app "RATIONALP" [x]) (app "RATIONALP" [y]),
    app "EQUAL" [app "COMPLEX" [x, y], app "BINARY-+" [x,
      app "BINARY-*" [app "QUOTE" [.atom (.number (.complex 0 1 (by decide)))], y]]]]
  let complexLhs := app "COMPLEX" [x, y]
  let rationalCompleted := fun t => app "IF" [app "RATIONALP" [t], t, zero]
  let complexRhs := app "COMPLEX" [rationalCompleted x, rationalCompleted y]
  let componentSchema := fun projection result => app "IMPLIES"
    [both (app "RATIONALP" [x]) (app "RATIONALP" [y]),
     app "EQUAL" [app projection [complexLhs], result]]
  let plusLhs := app "BINARY-+" [x, y]
  let plusRhs := app "IF" [app "ACL2-NUMBERP" [x],
    app "IF" [app "ACL2-NUMBERP" [y], plusLhs, x],
    app "IF" [app "ACL2-NUMBERP" [y], y, zero]]
  let x1 := sym "X1"
  let y1 := sym "Y1"
  let realLt := app "<" [app "REALPART" [x1], app "REALPART" [y1]]
  let componentBody := app "IF" [realLt, realLt,
    both (app "EQUAL" [app "REALPART" [x1], app "REALPART" [y1]])
      (app "<" [app "IMAGPART" [x1], app "IMAGPART" [y1]])]
  let completed := fun t => app "IF" [app "ACL2-NUMBERP" [t], t, zero]
  let orderLhs := app "<" [x, y]
  let orderRhs := app "IF" [both (app "RATIONALP" [x]) (app "RATIONALP" [y]), orderLhs,
    .cons (app "LAMBDA" [SExpr.ofList [x1, y1], componentBody])
      (SExpr.ofList [completed x, completed y])]
  let schema? := match name with
    | "POSITIVE" => some positive
    | "DISTRIBUTIVITY" => some (app "EQUAL" [distLhs, distRhs])
    | "ASSOCIATIVITY-OF-*" => some (app "EQUAL" [assocLhs, assocRhs])
    | "RATIONAL-IMPLIES2" => some (app "IMPLIES" [app "RATIONALP" [x],
        app "EQUAL" [app "BINARY-*" [app "UNARY-/" [den], app "NUMERATOR" [x]], x]])
    | "COMPLETION-OF-DENOMINATOR" => some (app "EQUAL" [den, denRhs])
    | "COMPLEX-DEFINITION" => some complexSchema
    | "COMPLETION-OF-COMPLEX" => some (app "EQUAL" [complexLhs, complexRhs])
    | "REALPART-COMPLEX" => some (componentSchema "REALPART" x)
    | "IMAGPART-COMPLEX" => some (componentSchema "IMAGPART" y)
    | "COMPLETION-OF-+" => some (app "EQUAL" [plusLhs, plusRhs])
    | "COMPLETION-OF-<" => some (app "EQUAL" [orderLhs, orderRhs])
    | _ => none
  let some schema := schema? | return none
  let instantiate := substTerm (subst.map (·.1)) (subst.map (·.2))
  let plain := instantiate schema
  unless !folds.isEmpty || plain == hyp do
    throwError "primitive use:{name}: recorded substitution disagrees with :HYPS"
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx plain
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
    | "COMPLEX-DEFINITION" => mkAppM ``complexDefinitionTrue #[vx, ← ctxValExpr cfg ctx (instantiate y)]
    | "REALPART-COMPLEX" => mkAppM ``realpartComplexTrue #[vx, ← ctxValExpr cfg ctx (instantiate y)]
    | "IMAGPART-COMPLEX" => mkAppM ``imagpartComplexTrue #[vx, ← ctxValExpr cfg ctx (instantiate y)]
    | "COMPLETION-OF-+" => do
      let law ← mkAppM ``Logic.plus_completion #[vx, ← ctxValExpr cfg ctx (instantiate y)]
      primitiveEqualityTrue (← ctxValExpr cfg ctx (instantiate plusLhs))
        (← ctxValExpr cfg ctx (instantiate plusRhs)) law
    | "COMPLETION-OF-COMPLEX" => do
      let law ← mkAppM ``Logic.complex_completion #[vx, ← ctxValExpr cfg ctx (instantiate y)]
      primitiveEqualityTrue (← ctxValExpr cfg ctx (instantiate complexLhs))
        (← ctxValExpr cfg ctx (instantiate complexRhs)) law
    | "COMPLETION-OF-<" => do
      let law ← mkAppM ``completionOrderLaw #[vx, ← ctxValExpr cfg ctx (instantiate y)]
      primitiveEqualityTrue (← ctxValExpr cfg ctx (instantiate orderLhs))
        (← ctxValExpr cfg ctx (instantiate orderRhs)) law
    | "COMPLETION-OF-DENOMINATOR" => do
      let law ← mkAppM ``Logic.denominator_completion #[vx]
      primitiveEqualityTrue (← ctxValExpr cfg ctx (instantiate den))
        (← ctxValExpr cfg ctx (instantiate denRhs)) law
    | _ => throwError "primitive USE schema has no proof handler: {name}"
  let pf ← mkAppM ``evtrue_of_conv_ne_nil #[← ctxValProof cfg ctx plain, hne]
  let pf ← foldUseInstanceProof cfg plain hyp folds pf
  return some (pf, ctx)

end ACL2.Replay.Driver
