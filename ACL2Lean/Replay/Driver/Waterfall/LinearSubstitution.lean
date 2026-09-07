import ACL2Lean.Replay.Driver.Waterfall.LinearEquation
import ACL2Lean.Replay.Driver.Waterfall.ResidualPostpass
import ACL2Lean.Replay.Driver.Waterfall.SubstitutionDuplicates

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- The recorded postpass following linear equation insertion. Each selected
quote equality is retained at its actual position, while substitution affects
the other literals. This lane ends only at the exact recorded child clause. -/
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
      unless prov.equivTerm == some (.atom (.symbol {name := "EQUAL"})) do
        throwFrontier m!"linear substitution: unsupported relation"
      let some basis := prov.branchSubstitutionBasis
        | throwError "linear substitution: missing selected literal decision"
      let fs ← tsQueryRead (TsQueryCapture.fields basis
        ["INPUT-CLAUSE", "LITERAL-POSITION", "LITERAL", "DELETE-LITERAL"])
      let input ← tsQueryRead (TsQueryCapture.asList (← tsQueryRead (TsQueryCapture.required fs "INPUT-CLAUSE")))
      let position ← tsQueryRead (TsQueryCapture.asInt (← tsQueryRead (TsQueryCapture.required fs "LITERAL-POSITION")))
      let literal ← tsQueryRead (TsQueryCapture.required fs "LITERAL")
      unless input == clause && position ≥ 0 && clause[position.toNat]? == some literal do
        throwError "linear substitution: selected literal/input position mismatch"
      unless (← tsQueryRead (TsQueryCapture.required fs "DELETE-LITERAL")) == .nil do
        throwFrontier m!"linear substitution: deletion requires its own continuation"
      let some (a, b) := notEqualSides? literal
        | throwError "linear substitution: selected literal is not a negated equality"
      unless (a == lhs && b == rhs) || (a == rhs && b == lhs) do
        throwError "linear substitution: selected equality differs from substitution"
      let next := clause.zipIdx.map fun (lit, i) =>
        if i == position.toNat then lit else replaceTermOcc lhs rhs lit
      let goal ← mkAppM ``EvTrue
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr (disjoinTerm clause)]
      let contradiction ← withLocalDeclD `hInputFalse (← mkAppM ``Not #[goal]) fun hf => do
        let (_, hLiteral) ← clauseLiteralFalsity cfg ctx clause hf position.toNat
        let hEq ← mkAppM ``logic_not_equal_nil_eq
          #[← ctxValExpr cfg ctx a, ← ctxValExpr cfg ctx b, hLiteral]
        let hEq ← if a == lhs then pure hEq else mkAppM ``Eq.symm #[hEq]
        let stepEq ← mkAppM ``fuel_eq_of_conv
          #[← ctxValProof cfg ctx lhs, ← ctxValProof cfg ctx rhs, hEq]
        let chain ← diffCollapse cfg.worldExpr cfg.envExpr lhs rhs stepEq
          (disjoinTerm clause) (disjoinTerm next)
        let p ← replayLinearSubstitutions rec cfg ctx idStr next rest children
        let p ← evtrueWith chain p
        mkLambdaFVars #[hf] (mkApp hf p)
      return ← mkAppM ``Classical.byContradiction #[contradiction]
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
    if let .step (.node rune _ _ _ prov) :: _ := rest then
      if rune.ty == "branch-substitution" && prov.branchSubstitutionBasis.isSome then
        return ← replayLinearSubstitutions rec cfg ctx idStr output rest children
    continueAt output

end ACL2.Replay.Driver
