import ACL2Lean.Replay.Driver.TypeSetQuery.Decision

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- Replay TYPE-SET-REC's executed IF arm. Decision queries precede the
selected branch queries. Each branch gets only its checked test premise;
its recorded type-alist is validated separately as a selection snapshot. -/
def replayConditionalQuery (replay : ReplayCtx → SExpr → SExpr → MetaM Expr)
    (cfg : ReplayConfig) (ctx : ReplayCtx) (q : TsQueryCapture.Query) : MetaM Expr := do
  let some (fn, [test, yes, no]) := asApp q.term | throwError "IF query: malformed application"
  unless fn.name == "IF" && q.comparison == .nil && q.recognizer == .nil &&
      q.lookup == SExpr.ofList [.nil, .nil] do
    throwFrontier m!"IF query: unsupported lookup/intersection or computation"
  let route ← tsQueryRead (TsQueryCapture.ifRoute q.route)
  let (decisionRaw, branchRaw) ← tsQueryRead (TsQueryCapture.splitIfQueries q route)
  if route.mustTrue && route.mustFalse then
    throwFrontier m!"IF query: contradictory decision requires its recorded contradiction proof"
  let decisionProofs ← decisionRaw.mapM fun raw => do
    pure (← tsQueryRead (TsQueryCapture.query raw), ← replay ctx raw .nil)
  let branches ← branchRaw.mapM (fun raw => tsQueryRead (TsQueryCapture.query raw))
  let resultMask ← match branches with
    | [a, b] => pure (-tsAnd (-a.result - 1) (-b.result - 1) - 1)
    | [a] => pure a.result
    | _ => throwError "IF query: executed branch count mismatch"
  unless q.result == resultMask do throwError "IF query: returned mask differs from executed branch union"
  let evidence ← tsQueryRead (queryTtreeEntries route.decisionTtree)
  let decisionEvidence ← decisionProofs.flatMapM fun (d, _) => tsQueryRead (queryTtreeEntries d.ttree)
  unless evidence.all decisionEvidence.contains do
    throwFrontier m!"IF query: decision evidence is not carried by its executed queries"
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx q.term
  let value ← ctxValExpr cfg ctx test
  let boolean ← mkAppM ``Logic.toBool #[value]
  let decision ← replayIfQueryDecision cfg ctx test route decisionProofs
  let branch (sense : Bool) (term : SExpr) (raw : Option SExpr) : MetaM Expr := do
    withLocalDeclD `hQueryBranch (← mkEq boolean (toExpr sense)) fun hb => do
      let result ← if let some raw := raw then do
          let branchCtx ← if sense then do
              let hne ← mkAppM ``Iff.mp #[← mkAppM ``Logic.toBool_eq_true #[value], hb]
              installBranchTrueFacts cfg ctx test value hne
            else do
              let hn ← mkAppM ``nil_of_toBool_false #[hb]
              pure {ctx with branchFacts := ctx.branchFacts ++ [(test, value, false, hn)]}
          let child ← tsQueryRead (TsQueryCapture.query raw)
          unless child.term == term do throwError "IF query: branch term differs from selected argument"
          let p ← replay branchCtx raw .nil
          mkAppM ``inTs_weaken #[← tsSubsumedProofM child.result q.result, p]
        else do
          let some hd := decision | throwError "IF query: absent branch has no checked pruning decision"
          let hf ← if sense then mkAppM ``bool_value_conflict #[hb, hd]
            else mkAppM ``bool_value_conflict #[hd, hb]
          mkFalseElim (← mkAppM ``InTs #[toExpr q.result, ← ctxValExpr cfg ctx term]) hf
      mkLambdaFVars #[hb] result
  let yesRaw := if route.mustFalse then none else branchRaw.head?
  let noRaw := if route.mustTrue then none else branchRaw.getLast?
  let ht ← branch true yes yesRaw
  let hf ← branch false no noRaw
  let mut result ← mkExpectedTypeHint (← mkAppM ``inTs_cond #[ht, hf]) (← tsQueryType cfg ctx q)
  for (_, p) in decisionProofs.reverse do result ← retainQueryChild p result
  return result

end ACL2.Replay.Driver
