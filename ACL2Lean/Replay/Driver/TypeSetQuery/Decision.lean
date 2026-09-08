import ACL2Lean.Replay.Driver.TypeSetQuery.Common
import ACL2Lean.Replay.Lemmas.TsQueryCells

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- Apply the observed root recognizer decision to its already checked
argument query, then transport the verdict through the source's recorded
NOT/IF-NIL-T normalization. Neither flags nor context snapshots are proofs. -/
private def replayIfRecognizerDecision (cfg : ReplayConfig) (ctx : ReplayCtx)
    (test : SExpr) (route : TsQueryCapture.IfRoute)
    (queries : List (TsQueryCapture.Query × Expr)) : MetaM (Option Expr) := do
  let d ← tsQueryRead (TsQueryCapture.ifRecognizerDecision route.decisionBasis)
  unless d.strengthening == .nil do
    throwFrontier m!"IF decision: selected strengthening requires its recorded derivation"
  let some (fn, [arg]) := asApp d.term | throwFrontier m!"IF decision: unsupported selected recognizer"
  unless arg == d.argument do throwError "IF decision: selected argument differs from recognizer"
  let some (q, hp) := queries[d.queryIndex]? | throwError "IF decision: selected query index out of range"
  unless q.term == arg && q.result == d.argumentTs do
    throwError "IF decision: indexed argument query differs from recorded selection"
  let some rune := ProofLog.parseRune? d.runes | throwError "IF decision: malformed selected primitive rune"
  unless rune.ty == "fake-rune-for-anonymous-enabled-rule" && rune.name == "NIL" && rune.idx.isNone do
    throwFrontier m!"IF decision: ordinary recognizer requires its replayed source derivation"
  unless ["ACL2-NUMBERP", "INTEGERP", "RATIONALP", "COMPLEX-RATIONALP", "CONSP"].contains fn.name do
    throwFrontier m!"IF decision: unsupported primitive recognizer"
  let some (_, mask, _) := (tsRecogTrue ++ tsRecogNil).find? (fun (name, _, _) => name == fn.name)
    | throwFrontier m!"IF decision: no primitive partition contract"
  unless d.trueTs == mask && d.falseTs == -mask - 1 && d.strong do
    throwError "IF decision: primitive partition differs from selected tuple"
  let isNot := (asApp test).any (fun (f, xs) => f.name == "NOT" && xs == [d.term])
  let isIfNot := (asApp test).any (fun (f, xs) =>
    f.name == "IF" && xs == [d.term, quoteNil, quoteT])
  unless if d.notFlag then isNot || isIfNot else test == d.term do
    throwError "IF decision: normalization differs from recorded test"
  let predTrue := tsDisjointM d.argumentTs d.falseTs
  let predFalse := tsDisjointM d.argumentTs d.trueTs
  unless route.mustTrue == (if d.notFlag then predFalse else predTrue) &&
      route.mustFalse == (if d.notFlag then predTrue else predFalse) do
    throwError "IF decision: selected flags differ from recorded partition intersections"
  if !route.mustTrue && !route.mustFalse then return none
  let mut fact ← primitiveRecognizerQueryVerdict d.term (if predTrue then .t else .nil)
    d.argumentTs d.trueTs d.falseTs d.strong hp
  if d.notFlag then
    fact ← mkCongrArg (mkConst ``Logic.not) fact
    if isIfNot then
      let hdef ← mkAppM ``gz_def_not #[← ctxValExpr cfg ctx d.term]
      fact ← mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[hdef], fact]
  fact ← mkExpectedTypeHint fact (← mkEq (← ctxValExpr cfg ctx test)
    (reflectSExpr (if route.mustTrue then SExpr.t else SExpr.nil)))
  let result ← mkCongrArg (mkConst ``Logic.toBool) fact
  return some (← mkExpectedTypeHint result (← mkEq
    (← mkAppM ``Logic.toBool #[← ctxValExpr cfg ctx test]) (toExpr route.mustTrue)))

/-- Shared checked decision for IF query pruning. Older captures are
adequate only when an executed query directly proves the entire test. -/
def replayIfQueryDecision (cfg : ReplayConfig) (ctx : ReplayCtx) (test : SExpr)
    (route : TsQueryCapture.IfRoute) (queries : List (TsQueryCapture.Query × Expr)) :
    MetaM (Option Expr) := do
  if route.decisionBasis != .nil then
    return ← replayIfRecognizerDecision cfg ctx test route queries
  if route.mustTrue || route.mustFalse then
    let (d, p) :: _ := queries | throwError "IF query: pruning lacks its decision query"
    unless d.term == test do
      throwFrontier m!"IF query: pruning of a composite test needs its scoped decision derivation"
    if route.mustTrue then
      unless !tsMember d.result 7 do throwError "IF query: selected decision does not prove truth"
      let hn ← mkAppM ``ne_nil_of_inTs #[← mkDecideProof
        (← mkEq (← mkAppM ``tsMember #[toExpr d.result, toExpr (7 : Nat)]) (toExpr false)), p]
      return some (← mkAppM ``toBool_true_of_ne_nil #[hn])
    else
      unless tsSubsumedM d.result 128 do throwError "IF query: selected decision does not prove falsity"
      let hn ← mkAppM ``nil_of_inTs128 #[← mkAppM ``inTs_weaken
        #[← tsSubsumedProofM d.result 128, p]]
      return some (← mkAppM ``Iff.mpr #[← mkAppM ``Logic.toBool_eq_false
        #[← ctxValExpr cfg ctx test], hn])
  unless route.decisionTtree == .nil do throwError "IF query: both-branch decision carries a verdict"
  return none

end ACL2.Replay.Driver
