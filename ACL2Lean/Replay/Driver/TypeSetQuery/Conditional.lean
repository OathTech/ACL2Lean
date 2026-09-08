import ACL2Lean.Replay.Driver.TypeSetQuery.Common
import ACL2Lean.Replay.Lemmas.TsQueryCells

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
  let decision ← if route.mustTrue || route.mustFalse then do
      let (d, p) :: _ := decisionProofs | throwError "IF query: pruning lacks its decision query"
      unless d.term == test do
        throwFrontier m!"IF query: pruning of a composite test needs its scoped decision derivation"
      if route.mustTrue then
        unless !tsMember d.result 7 do throwError "IF query: selected decision does not prove truth"
        let hn ← mkAppM ``ne_nil_of_inTs #[← mkDecideProof
          (← mkEq (← mkAppM ``tsMember #[toExpr d.result, toExpr (7 : Nat)]) (toExpr false)), p]
        pure (some (← mkAppM ``toBool_true_of_ne_nil #[hn]))
      else
        unless tsSubsumedM d.result 128 do throwError "IF query: selected decision does not prove falsity"
        let hn ← mkAppM ``nil_of_inTs128 #[← mkAppM ``inTs_weaken
          #[← tsSubsumedProofM d.result 128, p]]
        pure (some (← mkAppM ``Iff.mpr #[← mkAppM ``Logic.toBool_eq_false #[value], hn]))
    else do
      unless route.decisionTtree == .nil do throwError "IF query: both-branch decision carries a verdict"
      pure none
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
