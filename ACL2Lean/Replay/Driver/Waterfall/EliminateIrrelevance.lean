/-
  Driver/Waterfall/EliminateIrrelevance — split from Driver/Core (WP2 Stage 3a, 2026-07-17;
  see docs/plans/2026-07-18_driver-modular-refactor.md).

  The ELIMINATE-IRRELEVANCE processor.
-/
import ACL2Lean.Replay.Driver.Waterfall

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- Replay an ELIMINATE-IRRELEVANCE node: the child clause `C'` is an
    order-preserving SUBSET of this clause `C` (recompute-and-check).
    `EvTrue (disjoin C')` closes `EvTrue (disjoin C)`: value-walk `C'` —
    a nil literal peels off (`evtrue_extract_else`); the first truthy
    literal is IN `C`, closing the parent disjunction (`evtrueOfLitTrue`);
    the last literal's `EvTrue` is its own truthy fact. -/
partial def replayEliminateIrrelevance (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx)
    (cn : ClauseNode) : MetaM Expr := do
  for s in cn.steps do
    unless s.processor.toLower == "eliminate-irrelevance-clause" ||
           s.processor.toLower == "settled-down-clause" do
      throwError "replayEliminateIrrelevance: processor {s.processor} \
                  alongside eliminate-irrelevance at {cn.idStr} (frontier)"
  for (_, lp) in flattenLiterals (cn.steps.flatMap (·.items)) do
    unless lp.nodes.isEmpty && lp.result == lp.literal do
      throwError "replayEliminateIrrelevance: non-identity literal item at \
                  {cn.idStr} (frontier): {repr lp.literal}"
  let [child] := cn.children
    | throwError "replayEliminateIrrelevance: {cn.children.length} children \
                  at {cn.idStr} (frontier)"
  -- recompute-and-check: C' is an order-preserving sublist of C
  let rec isSublist : List SExpr → List SExpr → Bool
    | [], _ => true
    | _, [] => false
    | x :: xs, y :: ys => if x == y then isSublist xs ys else isSublist (x :: xs) ys
  unless isSublist child.inputClause cn.inputClause do
    throwError "replayEliminateIrrelevance: child clause is not an \
                order-preserving subset of {cn.idStr}'s clause"
  let mut ctx := ctx
  for tm in child.inputClause do
    ctx ← pinTermOpaques cfg cfg.envExpr ctx tm
  let pChild ← rec.clause cfg { ctx with litFacts := [] } child
  let nilC := mkConst ``SExpr.nil
  let closeAt (ctxW : ReplayCtx) (l : SExpr) (hne : Expr) : MetaM Expr := do
    let some m := cn.inputClause.findIdx? (· == l)
      | throwError "replayEliminateIrrelevance: internal — surviving literal \
                    {repr l} not in the parent clause"
    evtrueOfLitTrue cfg ctxW cn.inputClause m l hne
  let rec goSub (ctxW : ReplayCtx) (pCur : Expr) : List SExpr → MetaM Expr
    | [] => throwError "replayEliminateIrrelevance: empty child clause walk"
    | [l] => do
      let pL ← ctxValProof cfg ctxW l
      let hne ← mkAppM ``ne_nil_of_evtrue_conv #[pCur, pL]
      closeAt ctxW l hne
    | l :: restL => do
      let vL ← ctxValExpr cfg ctxW l
      let pL ← ctxValProof cfg ctxW l
      let negB ← withLocalDeclD `hnil (← mkEq vL nilC) fun hNil => do
        let pNil ← mkAppM ``re_val_cast
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr l, vL, nilC, pL, hNil]
        let pRest ← mkAppM ``evtrue_extract_else #[pNil, pCur]
        mkLambdaFVars #[hNil] (← goSub ctxW pRest restL)
      let posB ← withLocalDeclD `hne (← mkAppM ``Ne #[vL, nilC]) fun hNe => do
        mkLambdaFVars #[hNe] (← closeAt ctxW l hNe)
      mkAppM ``Classical.byCases #[negB, posB]
  goSub ctx pChild child.inputClause

end ACL2.Replay.Driver
