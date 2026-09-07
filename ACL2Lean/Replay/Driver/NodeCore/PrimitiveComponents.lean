import ACL2Lean.Replay.Driver.NodeCore.PrimitiveConditional
import ACL2Lean.NumericComplexAxioms

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- REALPART-IMAGPART-ELIM is a primitive axiom in axioms.lisp. Its rewrite
use consumes the recorded numeric hypothesis and RHS, using the same model
law as the destructor-elimination processor. -/
def replayPrimitiveComponentReconstruction (rec : NodeRec) (cfg : ReplayConfig)
    (ctx : ReplayCtx) (n : ProofNode) : MetaM Expr := do
  let .node _ lhs rhs kids prov := n
  let some (constructor, [real, imag]) := asApp lhs
    | throwError "component reconstruction: expected binary constructor"
  let some (projection, [a]) := asApp real
    | throwError "component reconstruction: expected realpart argument"
  let app := fun name args => SExpr.ofList (.atom (.symbol {name}) :: args)
  unless constructor.name == "COMPLEX" && projection.name == "REALPART" &&
      imag == app "IMAGPART" [a] && prov.subst == [(.atom (.symbol {name := "X"}), a)] do
    throwError "component reconstruction: primitive schema/substitution mismatch"
  let hyp := app "ACL2-NUMBERP" [a]
  let (prems, rhsNodes) ← replayPrimitivePremises rec cfg ctx "REALPART-IMAGPART-ELIM"
    [hyp] kids prov.runes
  let #[premise] := prems | throwError "component reconstruction: expected one checked hypothesis"
  let hn ← mkAppM ``ne_nil_of_evtrue_conv #[premise, ← ctxValProof cfg ctx hyp]
  let law ← mkAppM ``Logic.complex_realpart_imagpart #[hn]
  replayPrimitiveEquation rec cfg ctx lhs a rhs law rhsNodes

/-- The two primitive constructor projections consume both recorded rational
hypotheses, in the axiom's order, and every RHS continuation record. -/
def replayPrimitiveComponentProjection (rec : NodeRec) (cfg : ReplayConfig)
    (ctx : ReplayCtx) (n : ProofNode) : MetaM Expr := do
  let .node rune lhs rhs kids prov := n
  let (projection, lemmaName, real) ← match rune.name with
    | "REALPART-COMPLEX" => pure ("REALPART", ``Logic.realpart_complex_of_rational, true)
    | "IMAGPART-COMPLEX" => pure ("IMAGPART", ``Logic.imagpart_complex_of_rational, false)
    | _ => throwError "component projection: unregistered primitive axiom"
  let some (op, [arg]) := asApp lhs
    | throwError "component projection: expected unary projection"
  let some (constructor, [x, y]) := asApp arg
    | throwError "component projection: expected binary constructor"
  let app := fun name args => SExpr.ofList (.atom (.symbol {name}) :: args)
  unless op.name == projection && constructor.name == "COMPLEX" &&
      prov.subst == [(.atom (.symbol {name := "Y"}), y), (.atom (.symbol {name := "X"}), x)] do
    throwError "component projection: primitive schema/substitution mismatch"
  let hyps := [app "RATIONALP" [x], app "RATIONALP" [y]]
  let (prems, rhsNodes) ← replayPrimitivePremises rec cfg ctx rune.name hyps kids prov.runes
  let #[hx, hy] := prems | throwError "component projection: expected both checked hypotheses"
  let h ← mkAppM ``ne_nil_of_evtrue_conv
    #[if real then hx else hy, ← ctxValProof cfg ctx (if real then hyps[0]! else hyps[1]!)]
  let law ← mkAppM lemmaName #[← ctxValExpr cfg ctx x, ← ctxValExpr cfg ctx y, h]
  replayPrimitiveEquation rec cfg ctx lhs (if real then x else y) rhs law rhsNodes

end ACL2.Replay.Driver
