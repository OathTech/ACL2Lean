import ACL2Lean.Replay.Driver.NodeCore.PrimitiveConditional
import ACL2Lean.NumericComponents

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

end ACL2.Replay.Driver
