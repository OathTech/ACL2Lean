import ACL2Lean.Replay.Driver.Waterfall
import ACL2Lean.Replay.Driver.Waterfall.ClauseReplacement
import ACL2Lean.Replay.Driver.Waterfall.ClauseConstruction
import ACL2Lean.Replay.Driver.Waterfall.ClauseFolds

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- Replay the recorded remove-trivial-equivalences postpass on a residual
    clause. Unlike the scan's in-clause substitution, this pass retains the
    negative equality that justified the substitution. Its falsity is already
    proved on the selected segment. Every recorded operation is checked, and
    only the resulting exact clause can be handed to a pushed child.

    First witness: EQUAL-DENOMINATOR-1, Goal', whose denominator substitution
    and reciprocal constant fold change an earlier accumulated literal. -/
def replayResidualPostpass (rec : ClauseRec) (cfg : ReplayConfig)
    (ctx : ReplayCtx) (idStr : String) (clause : List SExpr)
    (items : List ClauseItem) (children : List ClauseNode) : MetaM Expr := do
  if let .step (.node rune _ _ _ prov) :: _ := items then
    if rune.ty == "branch-substitution" then
      if let some raw := prov.branchSubstitutionBasis then
        let selection ← selectedClauseSubstitution raw
        if selection.constructions.isSome then
          let p ← replayConstructedClauseEdits rec cfg ctx idStr selection.input items children (crunched := true)
          return ← constructedResidualToCurrent cfg ctx selection.input clause p
  let mut ctx := ctx
  let mut current := clause
  let mut chain : Option Expr := none
  for (item, idx) in items.zipIdx do
    if let .literal lp := item then
      -- add-literal can rebuild the segment as *true-clause*. Crunch
      -- then returns that singleton as its unrewritten side, and ACL2
      -- records one final scan of 'T. First prove the same structural
      -- constant/complement collapse, then consume that actual scan.
      unless lp.literal == quoteT && idx + 1 == items.length do
        throwError "residual postpass: non-final/non-'T literal continuation at {idStr} (frontier)"
      let pCurrent ← match ← groundConstClose cfg ctx current [] [] with
        | some p => pure p
        | none => tautClauseClose cfg ctx current s!"residual postpass at {idStr}"
      let collapse ← mkAppM ``evrel_siff_qt_of_evtrue #[pCurrent]
      let pRecorded ← rec.clauseSpine cfg ctx idStr [(lp.index, lp.literal)] [item] [] []
      let p ← mkAppM ``evtrue_of_evrel_siff #[collapse, pRecorded]
      return ← evtrueWith chain p
    let .step n := item
      | throwError "residual postpass: non-step continuation at {idStr} (frontier)"
    let .node rune lhs rhs childNodes prov := n
    if rune.ty == "context-subst" then
      unless childNodes.isEmpty do
        throwError "residual postpass: context substitution has children at {idStr}"
      ctx := { ctx with contextSubsts := ctx.contextSubsts ++ [(lhs, rhs)] }
      continue
    ctx ← pinTermOpaques cfg cfg.envExpr ctx lhs
    ctx ← pinTermOpaques cfg cfg.envExpr ctx rhs
    let (next, lifted) ←
      if rune.ty == "branch-substitution" then do
        unless prov.equivTerm == some (.atom (.symbol { name := "EQUAL" })) &&
            childNodes.isEmpty do
          throwError "residual postpass: substitution relation/children at {idStr} (frontier)"
        let some (a, b, hf, truthy) := (inScopeEquations ctx).find? fun (a, b, _, _) =>
            (a == lhs && b == rhs) || (a == rhs && b == lhs)
          | throwError "residual postpass: no equation justifies {repr lhs} => {repr rhs} at {idStr}"
        let some hEq ← composeEqChain cfg ctx [(a, b, hf, truthy, a != lhs)]
          | throwError "residual postpass: empty equation at {idStr}"
        unless ← isDefEq (← inferType hEq)
            (← mkEq (← ctxValExpr cfg ctx lhs) (← ctxValExpr cfg ctx rhs)) do
          throwError "residual postpass: equation has the wrong value type at {idStr}"
        let stepEq ← mkAppM ``fuel_eq_of_conv
          #[← ctxValProof cfg ctx lhs, ← ctxValProof cfg ctx rhs, hEq]
        let next := current.map fun L =>
          match notEqualSides? L with
          | some (a, b) =>
            if (a == lhs && b == rhs) || (a == rhs && b == lhs) then L
            else replaceTermOcc lhs rhs L
          | none => replaceTermOcc lhs rhs L
        pure (next, ← diffCollapse cfg.worldExpr cfg.envExpr lhs rhs stepEq
          (disjoinTerm current) (disjoinTerm next))
      else if rune.ty == "executable-counterpart" then do
        replayClauseExecutableFold cfg ctx current n
      else
        throwError "residual postpass: unsupported {rune.ty}/{nodeOrigin n} at {idStr}"
    if let some lifted := lifted then
      chain := some (← chainAfter chain lifted)
    current := next
    ctx ← pinTermOpaques cfg cfg.envExpr ctx (disjoinTerm current)
  -- subst-equiv-and-maybe-delete-lit rebuilds through add-literal-and-pt,
  -- which removes quoted NIL after the recorded constant folds.
  let (finalCtx, finalClause, finalChain) ← cleanupClauseFoldNils cfg ctx idStr current chain
  let [child] := children.filter (·.inputClause == finalClause)
    | throwError "residual postpass: no unique pushed child matches {repr finalClause} at {idStr}"
  let p ← rec.clause cfg { finalCtx with litFacts := [], dedupDrops := [] } child
  evtrueWith finalChain p

end ACL2.Replay.Driver
