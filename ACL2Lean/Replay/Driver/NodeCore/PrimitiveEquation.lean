import ACL2Lean.Replay.Driver.NodeCore.Recognizer

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- Apply a primitive equation, then replay all recorded children from its
intermediate term. Both convergence proofs carry the world's no-shadow facts. -/
def replayPrimitiveEquation (rec : NodeRec) (cfg : ReplayConfig) (ctx : ReplayCtx)
    (lhs intermediate rhs : SExpr) (valueEq : Expr) (children : List ProofNode) : MetaM Expr := do
  let pl ← ctxValProof cfg ctx lhs
  let pr ← ctxValProof cfg ctx intermediate
  let step ← mkAppM ``fuel_eq_of_conv #[pl, pr, valueEq]
  let (chainOpt, finalTerm) ← rec.rewrites cfg ctx intermediate children
  let chainOpt ← chainReqEq chainOpt
  unless finalTerm == rhs do
    throwError "primitive equation: children reached {repr finalTerm}, expected {repr rhs}"
  match chainOpt with
  | none => pure step
  | some chain => mkAppM ``fuel_chain_eq #[step, chain]

end ACL2.Replay.Driver
