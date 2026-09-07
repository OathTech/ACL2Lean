import ACL2Lean.Replay.Driver.Waterfall.ClauseSubset

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- Replay a clause-level reflexivity record. The substitution traversal
can discover this true literal before rebuilding the tail with add-literal.
Consume any recorded duplicate removals in that tail, then close with the
same reflexive literal. Any other trailing operation remains a frontier. -/
def replayClauseReflexivity (cfg : ReplayConfig) (ctx : ReplayCtx) (idStr : String)
    (clause : List SExpr) (n : ProofNode) (rest : List ClauseItem) : MetaM Expr := do
  let (lhs, rhs) := nodeLhsRhs n
  unless rhs == quoteT do
    throwError "replayClauseSpine: clause-level equal-self with rhs {repr rhs} at {idStr}"
  let some X := asEqualSelf lhs
    | throwError "replayClauseSpine: clause-level equal-self lhs {repr lhs} is not (equal X X) at {idStr}"
  unless clause.contains lhs do
    throwError "replayClauseSpine: equal-self literal {repr lhs} not in the clause at {idStr}"
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx lhs
  let hEqT ← mkAppM ``Logic.equal_self #[← ctxValExpr cfg ctx X]
  let tNeNil ← proveByDecide
    (← mkAppM ``Ne #[mkConst ``SExpr.t, mkConst ``SExpr.nil]) "t ≠ nil"
  let hne ← mkAppM ``ne_of_eq_of_ne #[hEqT, tNeNil]
  let mut current := clause
  let mut removed : List (List SExpr × List SExpr) := []
  for item in rest do
    let .dedupDrop lit := item
      | throwError "replayClauseSpine: non-duplicate item after clause-level equal-self at {idStr} (frontier)"
    unless (current.filter (· == lit)).length ≥ 2 do
      throwError "replayClauseSpine: equal-self trailing dedup has no duplicate {repr lit} at {idStr}"
    let next := current.erase lit
    removed := (current, next) :: removed
    current := next
  let some k := current.findIdx? (· == lhs)
    | throwError "replayClauseSpine: reflexive literal lost after duplicate removal at {idStr}"
  let mut p ← evtrueOfLitTrue cfg ctx current k lhs hne
  for (full, reduced) in removed do
    -- The checked removal is transported through the existing disjunction
    -- membership lemma; the result consumes the actual duplicate record.
    p ← liftClauseSubset cfg ctx full reduced p
  return p

end ACL2.Replay.Driver
