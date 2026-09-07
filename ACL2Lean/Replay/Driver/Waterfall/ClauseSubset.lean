import ACL2Lean.Replay.Driver.Waterfall

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- Transport a recorded clause inclusion through the existing generic
membership theorem. Each surviving literal and its convergence is checked. -/
def liftClauseSubset (cfg : ReplayConfig) (ctx : ReplayCtx)
    (full reduced : List SExpr) (p : Expr) : MetaM Expr := do
  let convP ← withLocalDeclD `u (mkConst ``SExpr) fun u => do
    let pred ← withLocalDeclD `v (mkConst ``SExpr) fun v => do
      mkLambdaFVars #[v] (← mkValConvPropEx cfg.worldExpr cfg.envExpr u v)
    mkLambdaFVars #[u] (← mkAppM ``Exists #[pred])
  let entries ← full.mapM fun t => do
    let pred ← withLocalDeclD `v (mkConst ``SExpr) fun v => do
      mkLambdaFVars #[v] (← mkValConvPropEx cfg.worldExpr cfg.envExpr (reflectSExpr t) v)
    let proof := mkAppN (mkConst ``Exists.intro [1])
      #[mkConst ``SExpr, pred, ← ctxValExpr cfg ctx t, ← ctxValProof cfg ctx t]
    pure (reflectSExpr t, proof)
  let (fullE, hconv) ← mkForallMemProof (mkConst ``SExpr) convP entries
  let memP ← withLocalDeclD `u (mkConst ``SExpr) fun u => do
    mkLambdaFVars #[u] (← mkAppM ``Membership.mem #[fullE, u])
  let subEntries ← reduced.mapM fun t => do
    let te := reflectSExpr t
    pure (te, ← mkDecideProof (mkApp memP te).headBeta)
  let (reducedE, hsub) ← mkForallMemProof (mkConst ``SExpr) memP subEntries
  mkAppM ``evtrue_disjoin_of_sublist
    #[cfg.worldExpr, cfg.envExpr, reducedE, fullE, hconv, hsub, p]

end ACL2.Replay.Driver
