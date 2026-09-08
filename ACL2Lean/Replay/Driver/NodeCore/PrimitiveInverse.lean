import ACL2Lean.Replay.Driver.NodeCore.PrimitiveConditional
import ACL2Lean.NumericInverse

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- INVERSE-OF-* is a primitive conditional axiom. Consume the actual HYP
blocks through the same relief walker as stored rules, then its RHS chain. -/
def replayPrimitiveInverse (rec : NodeRec) (cfg : ReplayConfig) (ctx : ReplayCtx)
    (n : ProofNode) : MetaM Expr := do
  let .node _ lhs rhs kids prov := n
  let some [.atom (.symbol op), a, invA] := lhs.toList?
    | throwError "inverse-of-*: expected a binary application"
  let app := fun name args => SExpr.ofList (.atom (.symbol { name }) :: args)
  unless op.name == "BINARY-*" && invA == app "UNARY-/" [a] do
    throwError "inverse-of-*: expected (binary-* a (unary-/ a))"
  unless prov.subst == [(.atom (.symbol { name := "X" }), a)] do
    throwError "inverse-of-*: stored substitution does not match the primitive axiom"
  let zero := app "QUOTE" [.atom (.number (.int 0))]
  let one := app "QUOTE" [.atom (.number (.int 1))]
  let hyps := [app "ACL2-NUMBERP" [a], app "NOT" [app "EQUAL" [a, zero]]]
  let (prems, rhsNodes) ← replayPrimitivePremises rec cfg ctx "INVERSE-OF-*" hyps kids prov.runes
  let hn ← mkAppM ``ne_nil_of_evtrue_conv #[prems[0]!, ← ctxValProof cfg ctx hyps[0]!]
  let hNot ← mkAppM ``ne_nil_of_evtrue_conv #[prems[1]!, ← ctxValProof cfg ctx hyps[1]!]
  let hNil ← mkAppM ``nil_of_logic_not_ne_nil #[hNot]
  let va ← ctxValExpr cfg ctx a
  let vz := reflectSExpr (.atom (.number (.int 0)))
  let hz ← withLocalDeclD `heq (← mkEq va vz) fun heq => do
    let hNe ← mkAppM ``Iff.mpr #[← mkAppM ``Logic.equal_ne_nil_iff #[va, vz], heq]
    mkLambdaFVars #[heq] (mkApp hNe hNil)
  let law ← mkAppM ``Logic.times_reciprocal #[va, hn, hz]
  replayPrimitiveEquation rec cfg ctx lhs one rhs law rhsNodes

end ACL2.Replay.Driver
