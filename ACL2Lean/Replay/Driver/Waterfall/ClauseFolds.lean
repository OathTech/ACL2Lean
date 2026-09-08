import ACL2Lean.Replay.Driver.Waterfall
import ACL2Lean.Replay.Driver.Waterfall.ClauseReplacement

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- The adequate older postpass records place executable folds directly in
the continuation. Replay that exact node and lift its equality through the
clause. A fold on an unrecorded temporary construction remains a frontier. -/
def replayClauseExecutableFold (cfg : ReplayConfig) (ctx : ReplayCtx)
    (clause : List SExpr) (n : ProofNode) : MetaM (List SExpr × Option Expr) := do
  let .node rune lhs rhs _ _ := n
  unless rune.ty == "executable-counterpart" do
    throwError "clause fold: recorded node is not an executable counterpart"
  let (stepEq, relation) ← replayNode cfg ctx n
  unless relation.isNone do throwError "clause fold: executable step is not equality"
  let next := clause.map (replaceTermOcc lhs rhs)
  unless next != clause do throwError "clause fold: executable step changes no literal"
  let chain ← diffCollapse cfg.worldExpr cfg.envExpr lhs rhs stepEq
    (disjoinTerm clause) (disjoinTerm next)
  return (next, chain)

/-- Compose the existing checked NIL-removal steps at the source-selected
cleanup boundary. Linear and residual postpasses choose different boundaries;
both preserve the same ordered transport and updated opaque context. -/
def cleanupClauseFoldNils (cfg : ReplayConfig) (ctx : ReplayCtx) (idStr : String)
    (clause : List SExpr) (chain : Option Expr) :
    MetaM (ReplayCtx × List SExpr × Option Expr) := do
  let (ctx, reduced, drops) ← dropFoldedNilLiterals cfg ctx idStr
    (clause.zipIdx.map (fun (lit, i) => (i + 1, lit)))
  let mut chain := chain
  for drop in drops do chain := some (← chainAfter chain drop)
  return (ctx, reduced.map (·.2), chain)

end ACL2.Replay.Driver
