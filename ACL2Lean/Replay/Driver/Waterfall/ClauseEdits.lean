import ACL2Lean.Replay.Driver.Waterfall.ClauseSubset
import ACL2Lean.Replay.Driver.Waterfall.ClauseFalsity
import ACL2Lean.Replay.Driver.Waterfall.ClauseReplacement
import ACL2Lean.Replay.Driver.TypeSetQuery

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- The open clause-edit judgment. Deletion needs implication, while
individual replacement steps may carry stronger equality conversions. -/
def ClauseEditSound (w : World) (env : Env) (before after : List SExpr) : Prop :=
  EvTrue w env (disjoinTerm after) → EvTrue w env (disjoinTerm before)

/-- The source selection, distinct from the checked implication it directs. -/
structure SelectedClauseSubstitution where
  input : List SExpr
  position : Nat
  literal : SExpr
  deleteLiteral : Bool
  constructions : Option SExpr
  resultClause : Option (List SExpr)

def selectedClauseSubstitution (raw : SExpr) : MetaM SelectedClauseSubstitution := do
  let fs ← tsQueryRead (TsQueryCapture.fields raw
    ["INPUT-CLAUSE", "LITERAL-POSITION", "LITERAL", "DELETE-LITERAL", "CONSTRUCTIONS", "RESULT-CLAUSE"])
  let input ← tsQueryRead (TsQueryCapture.asList (← tsQueryRead (TsQueryCapture.required fs "INPUT-CLAUSE")))
  let position ← tsQueryRead (TsQueryCapture.asInt (← tsQueryRead (TsQueryCapture.required fs "LITERAL-POSITION")))
  let literal ← tsQueryRead (TsQueryCapture.required fs "LITERAL")
  unless position ≥ 0 && input[position.toNat]? == some literal do
    throwError "clause edit: selected literal/input position mismatch"
  let deletion ← tsQueryRead (TsQueryCapture.required fs "DELETE-LITERAL")
  let deleteLiteral ← if deletion == SExpr.t then pure true
    else if deletion == .nil then pure false
    else throwError "clause edit: malformed deletion decision"
  let constructions := fs.lookup "CONSTRUCTIONS"
  let resultClause ← (fs.lookup "RESULT-CLAUSE").mapM fun raw => tsQueryRead (TsQueryCapture.asList raw)
  unless constructions.isSome == resultClause.isSome do
    throwError "clause edit: incomplete construction/result record"
  pure { input, position := position.toNat, literal, deleteLiteral, constructions, resultClause }

/-- The selected literal supplies the recorded EQUAL value equation.
ACL2 treats a variable literal as its equality to NIL; other supported
selections are explicit negated equalities, in either source orientation. -/
def selectedClauseEquation (cfg : ReplayConfig) (ctx : ReplayCtx)
    (selection : SelectedClauseSubstitution) (lhs rhs : SExpr) (hLiteral : Expr) : MetaM Expr := do
  if let some (a, b) := notEqualSides? selection.literal then
    unless (a == lhs && b == rhs) || (a == rhs && b == lhs) do
      throwError "clause edit: selected equality differs from the recorded substitution"
    let h ← mkAppM ``logic_not_equal_nil_eq
      #[← ctxValExpr cfg ctx a, ← ctxValExpr cfg ctx b, hLiteral]
    return ← if a == lhs then pure h else mkAppM ``Eq.symm #[h]
  let .atom (.symbol s) := selection.literal
    | throwFrontier m!"clause edit: unsupported selected literal"
  unless s.name != "T" && lhs == selection.literal && rhs == quoteNil do
    throwError "clause edit: selected variable does not justify the recorded NIL substitution"
  mkExpectedTypeHint hLiteral (← mkEq (← ctxValExpr cfg ctx lhs) (← ctxValExpr cfg ctx rhs))

/-- Certify the recorded selected EQUAL edit. The selected literal is skipped
while replacing other literals. Its falsity justifies the equality inside
the parent-clause contradiction; deleting it then uses clause inclusion.
No selected equality is added to the child's assumptions. -/
def certifySelectedClauseSubstitution (cfg : ReplayConfig) (ctx : ReplayCtx)
    (clause : List SExpr) (n : ProofNode) : MetaM (List SExpr × Expr) := do
  let .node rune lhs rhs children prov := n
  unless rune.ty == "branch-substitution" && children.isEmpty &&
      prov.equivTerm == some (.atom (.symbol { name := "EQUAL" })) do
    throwFrontier m!"clause edit: unsupported substitution relation or children"
  let some raw := prov.branchSubstitutionBasis
    | throwError "clause edit: missing selected input/literal decision"
  let selection ← selectedClauseSubstitution raw
  unless selection.input == clause do
    throwError "clause edit: recorded input differs from the current clause"
  unless selection.constructions.isNone do
    throwError "clause edit: construction record requires the construction consumer"
  let retained := clause.zipIdx.map fun (lit, i) =>
    if i == selection.position then lit else replaceTermOcc lhs rhs lit
  let after := if selection.deleteLiteral then retained.eraseIdx selection.position else retained
  let mut ctx := ctx
  for t in lhs :: rhs :: clause ++ retained do
    ctx ← pinTermOpaques cfg cfg.envExpr ctx t
  let editCtx := ctx
  let resultType ← mkAppM ``EvTrue
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr (disjoinTerm after)]
  let inputType ← mkAppM ``EvTrue
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr (disjoinTerm clause)]
  let proof ← withLocalDeclD `hEdited resultType fun hEdited => do
    let contradiction ← withLocalDeclD `hInputFalse (← mkAppM ``Not #[inputType]) fun hf => do
      let (_, hLiteral) ← clauseLiteralFalsity cfg editCtx clause hf selection.position
      let hEq ← selectedClauseEquation cfg editCtx selection lhs rhs hLiteral
      let stepEq ← mkAppM ``fuel_eq_of_conv
        #[← ctxValProof cfg editCtx lhs, ← ctxValProof cfg editCtx rhs, hEq]
      let chain ← diffCollapse cfg.worldExpr cfg.envExpr lhs rhs stepEq
        (disjoinTerm clause) (disjoinTerm retained)
      let hRetained ← if selection.deleteLiteral then
          liftClauseSubset cfg editCtx retained after hEdited
        else pure hEdited
      let p ← evtrueWith chain hRetained
      mkLambdaFVars #[hf] (mkApp hf p)
    mkLambdaFVars #[hEdited] (← mkAppM ``Classical.byContradiction #[contradiction])
  let judgment ← mkAppM ``ClauseEditSound
    #[cfg.worldExpr, cfg.envExpr, ← mkListLit (mkConst ``SExpr) (clause.map reflectSExpr),
      ← mkListLit (mkConst ``SExpr) (after.map reflectSExpr)]
  pure (after, ← mkExpectedTypeHint proof judgment)

end ACL2.Replay.Driver
