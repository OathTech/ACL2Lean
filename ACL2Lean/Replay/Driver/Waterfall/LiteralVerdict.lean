import ACL2Lean.Replay.Driver.Discharge

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- Consume rewrite-atm's recorded positive type-set verdict on the current
literal. This is a verdict-only leaf; no rewrite children may be bypassed.
The obligation retains the checked falsity facts in the enclosing clause
context. Unproved opaque-function properties remain frontiers.

First consumer: the reciprocal equality's nonnumber branch, decided before
rewriting. Its hypothesis-relief nodes use their separate structural walker. -/
def replayLiteralTypeSetVerdict (cfg : ReplayConfig) (ctx : ReplayCtx)
    (lp : LiteralProof) : MetaM (Expr × ReplayCtx) := do
  let [.node r lhs rhs kids prov] := lp.nodes
    | throwError "literal verdict: expected one recorded node"
  unless r.ty == "type-set" && lhs == lp.literal &&
      rhs == .atom (.keyword "TRUE") && kids.isEmpty &&
      prov.literalNotFlg == some false && !lp.notFlg && lp.result == quoteT do
    throwError "literal verdict: node term/polarity/children mismatch"
  let tests := ((ctx.litFacts.map (·.2.1)) ++ ctx.segFacts.map (·.1)).eraseDups
  let terms := tests ++ [lp.literal]
  let mut ctx := ctx
  for t in terms do ctx ← pinTermOpaques cfg cfg.envExpr ctx t
  let facts ← tests.mapM fun t => do
    let ty ← mkEq (← ctxValExpr cfg ctx t) (mkConst ``SExpr.nil)
    let some h ← ctx.litFactByTermChecked? t ty
      | throwError "literal verdict: stale branch fact"
    return h
  let vars := (terms.flatMap freeVars).eraseDups
  let opaques := (terms.flatMap collectOpaques).eraseDups
  let stmt ← dpFactStmt tests lp.literal vars opaques []
  let p ← proveDpFact stmt (vars.length + opaques.length)
    (dpConeIndices tests lp.literal vars opaques [])
  let values ← vars.mapM fun v => ctxValExpr cfg ctx (.atom (.symbol v))
  let opValues ← opaques.mapM fun op => do
    let some (v, _) := ctx.val? op | throwError "literal verdict: unpinned opaque"
    return v
  let fact := mkAppN p (values ++ opValues ++ facts).toArray
  let expected ← mkAppM ``Ne #[← ctxValExpr cfg ctx lp.literal, mkConst ``SExpr.nil]
  unless ← isDefEq (← inferType fact) expected do
    throwError "literal verdict: value instantiation differs"
  return (fact, ctx)

end ACL2.Replay.Driver
