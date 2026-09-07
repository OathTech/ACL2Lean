import ACL2Lean.Replay.Driver.Waterfall

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- The selected edit in `simplify-clause1` after an unchanged rewrite pass.
    Only the recorded position changes; no add-literal normalization occurs.
    The caller has already replayed every literal and its continuation. -/
def replaySelectedUnhide (rec : ClauseRec) (cfg : ReplayConfig)
    (ctx : ReplayCtx) (idStr : String) (clause : List SExpr)
    (info : UnhideLiteralSelection) (children : List ClauseNode) : MetaM Expr := do
  unless info.inputClause == clause do
    throwError "UNHIDE-LITERAL: recorded input differs from the scanned clause at {idStr}"
  unless clause[info.position]? == some info.oldLiteral do
    throwError "UNHIDE-LITERAL: selected position/old literal mismatch at {idStr}"
  let some (notFn, [hidden]) := asApp info.oldLiteral
    | throwError "UNHIDE-LITERAL: expected a negative hidden literal at {idStr}"
  let some (hideFn, [body]) := asApp hidden
    | throwError "UNHIDE-LITERAL: expected a unary HIDE at {idStr}"
  unless notFn.isNamed "NOT" && hideFn.isNamed "HIDE" do
    throwError "UNHIDE-LITERAL: wrong NOT/HIDE symbols at {idStr}"
  let some (_, [_, _]) := asApp body
    | throwError "UNHIDE-LITERAL: expected the recorded binary relation at {idStr}"
  unless info.newLiteral == SExpr.cons (.atom (.symbol notFn)) (.cons body .nil) do
    throwError "UNHIDE-LITERAL: new literal is not the selected HIDE removal at {idStr}"
  let output := clause.take info.position ++ info.newLiteral :: clause.drop (info.position + 1)
  let [child] := children.filter (·.inputClause == output)
    | throwError "UNHIDE-LITERAL: no unique child matches the selected edit at {idStr}"
  -- ctxValProof's existing HIDE route uses the checked gz_def_hide model
  -- equation, including package/arity/no-shadow checks. Both literal values
  -- are definitionally identical; no book theorem or verdict is substituted.
  let oldProof ← ctxValProof cfg ctx info.oldLiteral
  let newProof ← ctxValProof cfg ctx info.newLiteral
  let valueEq ← mkEqRefl (← ctxValExpr cfg ctx info.newLiteral)
  let edit ← mkAppM ``fuel_eq_of_conv #[oldProof, newProof, valueEq]
  let some lifted ← diffCollapse cfg.worldExpr cfg.envExpr
      info.oldLiteral info.newLiteral edit (disjoinTerm clause) (disjoinTerm output)
    | throwError "UNHIDE-LITERAL: recorded edit changes no literal at {idStr}"
  let pChild ← rec.clause cfg { ctx with litFacts := [], dedupDrops := [] } child
  let pOld ← evtrueWith (some lifted) pChild
  vacuousResidualClose cfg ctx clause pOld quoteNil fun lit => do
    let some fact := ctx.litFactByTerm? lit
      | throwError "UNHIDE-LITERAL: no scanned falsity fact at {idStr}: {repr lit}"
    pure fact

end ACL2.Replay.Driver
