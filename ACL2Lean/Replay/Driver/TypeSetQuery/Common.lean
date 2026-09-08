import ACL2Lean.Replay.Driver.TypeSetQuery.Rules

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

def tsQueryRead (x : Except String α) : MetaM α :=
  match x with
  | .ok a => pure a
  | .error e => throwError e

/-- Validate selected context entries in their recorded IF branch scopes.
The snapshots select evidence; they introduce no assumed Lean facts. -/
partial def checkTsQueryLookups (ta : List (SExpr × Int × SExpr)) (raw : SExpr) : MetaM Unit := do
  let q ← tsQueryRead (TsQueryCapture.query raw)
  if q.route == .atom (.keyword "LOOKUP") then
    let some (_, mask, tt) := ta.find? (fun (t, _, _) => t == q.term)
      | throwError "type-set query: lookup term absent from recorded type-alist"
    unless q.lookup == SExpr.ofList [.atom (.number (.int mask)), tt] do
      throwError "type-set query: lookup differs from recorded type-alist entry"
  if let some [.atom (.keyword "CONSTANT-BOUND"), .atom (.keyword "RESULT"), _,
      .atom (.keyword "ENTRY"), entry, .atom (.keyword "DERIVATION"), _] := q.comparison.toList? then
    let [selected] ← tsQueryRead (TsQueryCapture.typeAlist (SExpr.ofList [entry]))
      | throwError "type-set query: malformed selected bound entry"
    unless ta.contains selected do
      throwError "type-set query: selected bound entry absent from recorded type-alist"
  if let .cons (.atom (.keyword "IF")) _ := q.route then
    let route ← tsQueryRead (TsQueryCapture.ifRoute q.route)
    let (decisions, branches) ← tsQueryRead (TsQueryCapture.splitIfQueries q route)
    for child in decisions do checkTsQueryLookups ta child
    let branchContexts := (if route.mustFalse then [] else [route.trueContext]) ++
      (if route.mustTrue then [] else [route.falseContext])
    for (child, context) in branches.zip branchContexts do checkTsQueryLookups context child
  else
    for child in q.children do checkTsQueryLookups ta child

def tsQueryType (cfg : ReplayConfig) (ctx : ReplayCtx)
    (q : TsQueryCapture.Query) : MetaM Expr := do
  mkAppM ``InTs #[toExpr q.result, ← ctxValExpr cfg ctx q.term]

/-- Preserve an executed child whose premise is unnecessary for a range law. -/
def retainQueryChild (child result : Expr) : MetaM Expr := do
  withLetDecl `hQueryArgument (← inferType child) child fun h =>
    mkLetFVars #[h] result (usedLetOnly := false)

/-- Apply a primitive recognizer's recorded partition to checked argument
membership. Both a recursive query and an explicit rewrite use this boundary.
Ordinary compound recognizers use their replayed source theorem instead. -/
def primitiveRecognizerQueryVerdict (term verdict : SExpr)
    (argTs trueTs falseTs : Int) (strong : Bool) (argument : Expr) : MetaM Expr := do
  let some (fn, [_]) := asApp term | throwError "recognizer query: unary application required"
  unless ["ACL2-NUMBERP", "INTEGERP", "RATIONALP", "COMPLEX-RATIONALP", "CONSP"].contains fn.name do
    throwFrontier m!"recognizer query: ordinary predicate requires its replayed source"
  let entries := if verdict == .t then tsRecogTrue else if verdict == .nil then tsRecogNil else []
  let some (_, mask, rule) := entries.find? (fun (name, _, _) => name == fn.name)
    | throwFrontier m!"recognizer query: unsupported primitive verdict"
  unless trueTs == mask && falseTs == -mask - 1 && strong do
    throwError "recognizer query: primitive partition differs from recorded tuple"
  let inclusion ← if verdict == .t then tsSubsumedProofM argTs mask else
    mkDecideProof (← mkEq (← mkAppM ``tsDisjointM #[toExpr argTs, toExpr mask]) (toExpr true))
  mkAppM rule #[inclusion, argument]

end ACL2.Replay.Driver
