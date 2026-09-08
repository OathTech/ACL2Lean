import ACL2Lean.Replay.Driver.Waterfall.LinearEquation
import ACL2Lean.Replay.Driver.Waterfall.ClauseConstruction
import ACL2Lean.Replay.Driver.Waterfall.SubstitutionDuplicates
import ACL2Lean.Replay.Driver.Waterfall.ClauseEdits

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- The recorded postpass following linear equation insertion. The shared
edit judgment handles the selected literal's retention/deletion. This lane
ends only at the exact recorded child clause. -/
partial def replayLinearSubstitutions (rec : ClauseRec) (cfg : ReplayConfig)
    (ctx : ReplayCtx) (idStr : String) (clause : List SExpr)
    (items : List ClauseItem) (children : List ClauseNode) : MetaM Expr := do
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx (disjoinTerm clause)
  match items with
  | [] =>
    let [child] := children | throwError "linear substitution: expected exactly one child at {idStr}"
    unless child.inputClause == clause do
      throwError "linear substitution: recorded child differs from the resulting clause at {idStr}"
    rec.clause cfg { ctx with litFacts := [], dedupDrops := [] } child
  | .dedupDrop _ :: _ =>
    replaySubstitutionDuplicates cfg ctx idStr clause items fun next rest =>
      replayLinearSubstitutions rec cfg ctx idStr next rest children
  | .step n :: rest =>
    let .node rune lhs rhs childNodes prov := n
    unless childNodes.isEmpty do throwError "linear substitution: unexpected step children"
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx lhs
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx rhs
    if rune.ty == "branch-substitution" then
      if let some raw := prov.branchSubstitutionBasis then
        if (← selectedClauseSubstitution raw).constructions.isSome then
          return ← replayConstructedClauseEdits rec cfg ctx idStr clause items children
      let (next, edit) ← certifySelectedClauseSubstitution cfg ctx clause n
      let p ← replayLinearSubstitutions rec cfg
        { ctx with litFacts := [], dedupDrops := [] } idStr next rest children
      return mkApp edit p
    if rune.ty == "executable-counterpart" && prov.origin == "scons-term/exec" then
      let (stepEq, relation) ← replayNode cfg ctx n
      unless relation.isNone do throwError "linear substitution: non-equality executable fold"
      let next := clause.map (replaceTermOcc lhs rhs)
      unless next != clause do throwError "linear substitution: fold changes no literal"
      let chain ← diffCollapse cfg.worldExpr cfg.envExpr lhs rhs stepEq
        (disjoinTerm clause) (disjoinTerm next)
      let (ctx, reduced, drops) ← dropFoldedNilLiterals cfg ctx idStr
        (next.zipIdx.map fun (lit, i) => (i + 1, lit))
      let mut chain := chain
      for drop in drops do chain := some (← chainAfter chain drop)
      let p ← replayLinearSubstitutions rec cfg ctx idStr (reduced.map (·.2)) rest children
      return ← evtrueWith chain p
    throwFrontier m!"linear substitution: unsupported {rune.ty}/{prov.origin}"
  | _ => throwFrontier m!"linear substitution: unsupported continuation item"

/-- Select the recorded postpass only when its first step carries the new
source decision. Earlier captures retain their existing continuation route. -/
def replayLinearInsertion (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx)
    (idStr : String) (clause : List SExpr) (info : LinearEquationInsertion)
    (rest : List ClauseItem) (children : List ClauseNode)
    (continueAt : List SExpr → MetaM Expr) : MetaM Expr :=
  replayLinearEquation cfg ctx clause info fun output => do
    if rest.isEmpty then
      return ← replayLinearSubstitutions rec cfg ctx idStr output [] children
    if let .step (.node rune _ _ _ prov) :: _ := rest then
      if rune.ty == "branch-substitution" && prov.branchSubstitutionBasis.isSome then
        return ← replayLinearSubstitutions rec cfg ctx idStr output rest children
    continueAt output

end ACL2.Replay.Driver
