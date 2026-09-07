import ACL2Lean.Replay.Driver.Waterfall.ClauseSubset

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- ADD-LITERAL-AND-PT rebuilds a substituted clause from its tail. A
recorded duplicate drop removes the earlier occurrence, including when
other literals separate it from the retained occurrence. Consume each
record in order and replay the exact remaining continuation. -/
def replaySubstitutionDuplicates (cfg : ReplayConfig) (ctx : ReplayCtx)
    (idStr : String) (clause : List SExpr) (items : List ClauseItem)
    (continueAt : List SExpr → List ClauseItem → MetaM Expr) : MetaM Expr := do
  let mut current := clause
  let mut remaining := items
  let mut removed : List (List SExpr × List SExpr) := []
  repeat
    let adjacent := (List.range (current.length - 1)).any fun i =>
      i + 2 < current.length && current[i]! == current[i+1]!
    match remaining with
    | .dedupDrop lit :: rest =>
      unless (current.filter (· == lit)).length ≥ 2 do
        throwError "replayClauseSpine: recorded removal has no duplicate {repr lit} at {idStr}"
      let next := current.erase lit
      removed := (current, next) :: removed
      current := next
      remaining := rest
    | _ =>
      if adjacent then
        throwError "replayClauseSpine: adjacent duplicate has no recorded removal at {idStr}"
      break
  let mut p ← continueAt current remaining
  for (full, reduced) in removed do
    p ← liftClauseSubset cfg ctx full reduced p
  return p

end ACL2.Replay.Driver
