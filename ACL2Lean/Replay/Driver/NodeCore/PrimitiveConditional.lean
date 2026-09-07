import ACL2Lean.Replay.Driver.NodeCore.HypRelief
import ACL2Lean.Replay.Driver.NodeCore.PrimitiveEquation

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

private def primitiveBlockKind (n : ProofNode) : String :=
  let .node _ _ _ _ p := n
  if p.blockKind.isEmpty then p.innerKind else p.blockKind

private def primitiveEmptyChain (cfg : ReplayConfig) (t : SExpr) : MetaM Expr := do
  let evalFn ← withLocalDeclD `fuel (mkConst ``Nat) fun f =>
    mkLambdaFVars #[f] (mkAppN (mkConst ``evalOpt) #[f, cfg.worldExpr, cfg.envExpr, reflectSExpr t])
  mkAppM ``fuel_eq_refl #[evalFn]

/-- Conditional primitive axioms share the stored-rule hypothesis walker.
Every child belongs to a HYP or RHS block; return the RHS records intact
for the primitive equation consumer. -/
def replayPrimitivePremises (rec : NodeRec) (cfg : ReplayConfig) (ctx : ReplayCtx)
    (name : String) (hyps : List SExpr) (kids : List ProofNode) (runes : List Rune) :
    MetaM (Array Expr × List ProofNode) := do
  unless kids.all (fun k => primitiveBlockKind k == "hyp" || primitiveBlockKind k == "rhs") do
    throwError "primitive axiom {name}: child outside HYP/RHS blocks"
  let prems ← replayRuleHypotheses rec cfg ctx name hyps [] []
    (kids.filter (fun k => primitiveBlockKind k == "hyp")) runes (primitiveEmptyChain cfg)
  return (prems, kids.filter (fun k => primitiveBlockKind k == "rhs"))

end ACL2.Replay.Driver
