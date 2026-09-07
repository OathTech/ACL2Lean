import ACL2Lean.Replay.Driver.TypeSetQuery

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

private partial def queryParents (raw : SExpr) : MetaM (List Nat) := do
  let q ← tsQueryRead (TsQueryCapture.query raw)
  let mut parents := []
  for tree in [q.ttree, q.inputTtree] do
    for tag in ← tsQueryRead (TsQueryCapture.asList tree) do
      if let some (fn, args) := asApp tag then
        if fn.name == "PT" then
          for p in args do
            let n ← tsQueryRead (TsQueryCapture.asInt p)
            unless n ≥ 0 do throwError "linear numeric query: negative PT"
            parents := parents ++ [n.toNat]
  return (parents ++ (← q.children.mapM queryParents).flatten).eraseDups

/-- Replay the actual ADD-LINEAR-ASSUMPTION queries. Only their recorded
PTs are installed from the input-clause falsity proof. No numeric flag or
type-alist snapshot becomes a Lean assumption. -/
def replayLinearNumericBasis (cfg : ReplayConfig) (ctx : ReplayCtx)
    (info : LinearEquationInsertion) (a b : SExpr)
    (parentFalse : Nat → MetaM (SExpr × Expr)) : MetaM (Option (Expr × Expr)) := do
  let some raw := info.numericBasis | return none
  let fs ← tsQueryRead (TsQueryCapture.fields raw ["OPERANDS", "TYPE-ALIST", "QUERIES"])
  unless (← tsQueryRead (TsQueryCapture.asList (← tsQueryRead (TsQueryCapture.required fs "OPERANDS")))) == [a, b] do
    throwFrontier m!"linear numeric query: original operands differ from the inserted equation"
  let ta ← tsQueryRead (TsQueryCapture.typeAlist (← tsQueryRead (TsQueryCapture.required fs "TYPE-ALIST")))
  let [qa, qb] ← tsQueryRead (TsQueryCapture.asList (← tsQueryRead (TsQueryCapture.required fs "QUERIES")))
    | throwError "linear numeric query: expected both executed calls"
  let proveNumber (term query : SExpr) : MetaM Expr := do
    let q ← tsQueryRead (TsQueryCapture.query query)
    let expected := SExpr.ofList [.atom (.symbol {name := "ACL2-NUMBERP"}), term]
    unless q.term == expected || (quotedInt? term == some 0 && q.term == quoteT) do
      throwError "linear numeric query: root differs from the actual operand test"
    unless q.result == 256 do throwFrontier m!"linear numeric query: non-T result"
    checkTsQueryLookups ta query
    let mut queryCtx := ctx
    for k in ← queryParents query do
      let (lit, h) ← parentFalse k
      queryCtx := {queryCtx with litFacts := queryCtx.litFacts ++
        [(info.inputClause.length - info.parentClause.length + k, lit, h)]}
    let p ← replayTsQuery cfg queryCtx query
    let h ← mkAppM ``t_of_inTs256 #[p]
    let number ← mkAppM ``Logic.acl2Numberp #[← ctxValExpr cfg ctx term]
    let h ← mkExpectedTypeHint h (← mkEq number (mkConst ``SExpr.t))
    let hn ← mkDecideProof (← mkAppM ``Ne #[mkConst ``SExpr.t, mkConst ``SExpr.nil])
    mkAppM ``ne_of_eq_of_ne #[h, hn]
  return some (← proveNumber a qa, ← proveNumber b qb)

end ACL2.Replay.Driver
