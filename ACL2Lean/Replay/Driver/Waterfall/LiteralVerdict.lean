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

/-- A successful rewrite-atm boundary type-set proof replaces the attempted
rewrite. Replay the retained prefix (IMPLIES expansion, when present), then
prove the exact verdict in isolation: ACL2 calls type-set with an empty
clause/type-alist. NOT-FLG finally negates that truthy atom to NIL. The
preceding chain must reach the verdict input exactly; no child is skipped. -/
def replayNegatedAtomBoundary (cfg : ReplayConfig) (ctx : ReplayCtx)
    (lp : LiteralProof) : MetaM (Expr × SExpr) := do
  let [st] := lp.boundaryVerdicts | throwError "atom boundary: expected one verdict"
  unless lp.notFlg && lp.result == quoteNil && st.origin == "atm/try-type-set" &&
      st.rune.ty == "fake-rune-for-type-set" && st.equiv == "iff" && st.rhs == quoteT do
    throwError "atom boundary: verdict or literal polarity differs"
  let some (ns, [atm]) := asApp lp.literal | throwError "atom boundary: malformed literal"
  unless ns.name == "NOT" do throwError "atom boundary: literal is not negated"
  let ctx := literalReplayCtx ctx lp
  let (atomChain, mid) ← replayRewrites cfg ctx atm lp.nodes
  let atomChain ← chainReqEq atomChain
  unless mid == st.lhs do throwError "atom boundary: atomChain does not reach verdict input"
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx mid
  -- try-type-set-and-clause calls TYPE-SET with an empty type-alist.
  let vars := freeVars mid
  let ops := collectOpaques mid
  let stmt ← dpFactStmt [] mid vars ops []
  let p ← proveDpFact stmt (vars.length + ops.length) (dpConeIndices [] mid vars ops [])
  let vs ← vars.mapM fun s => ctxValExpr cfg ctx (.atom (.symbol s))
  let os ← ops.mapM fun op => ctxValExpr cfg ctx op
  let h := mkAppN p (vs ++ os).toArray
  let expected ← mkAppM ``Ne #[← ctxValExpr cfg ctx mid, mkConst ``SExpr.nil]
  unless ← isDefEq (← inferType h) expected do throwError "atom boundary: wrong value instantiation"
  let hMid ← mkAppM ``evtrue_of_conv_ne_nil #[← ctxValProof cfg ctx mid, h]
  let hAtm ← match atomChain with
    | none => pure hMid
    | some p => mkAppM ``evtrue_of_fuel_eq #[p, hMid]
  let pNot ← mkAppM ``conv_not_nil_of_evtrue #[← proveNoShadow cfg ns, hAtm]
  let pNil ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, mkConst ``SExpr.nil]
  let eq ← mkAppM ``fuel_eq_of_conv #[pNot, pNil, ← mkEqRefl (mkConst ``SExpr.nil)]
  return (eq, quoteNil)

end ACL2.Replay.Driver
