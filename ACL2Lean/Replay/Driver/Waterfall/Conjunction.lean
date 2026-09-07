import ACL2Lean.Replay.Driver.Waterfall.Compose

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- Check the recorded two-leaf strip-branches union whose false conjunct
produces an empty segment. The recorded subsumption pass absorbs the other
segment into that empty one. Every leaf is checked; the caller then replays
the one actual continuation through its ordinary literal-spine composer.

This introduces no context fact. A `segment-false` verdict must already have
a checked falsity proof in this clause context. Other conjunction shapes
remain frontiers. Driven by the weak multiplication helper's Subgoal 9'. -/
def checkSubsumedConjunction (cfg : ReplayConfig) (ctx : ReplayCtx)
    (lp : LiteralProof) (segment : SExpr) : MetaM Unit := do
  let [(left, right)] := lp.conjunctions
    | throwError "conjunction union: expected one recorded strip-branches call"
  let result := SExpr.ofList [.atom (.symbol { name := "IF" }), left, right, quoteNil]
  unless lp.result == result && segment == .nil do
    throwError "conjunction union: result or surviving empty segment changed"
  unless lp.splitReshaped == ["subsumption-loop"] do
    throwError "conjunction union: missing recorded segment subsumption"
  let [a, b] := lp.splitTrace
    | throwError "conjunction union: expected both recorded conjunct leaves"
  let mut falseCount := 0
  for (term, decision) in [(left, a), (right, b)] do
    let .leaf value outcome path emittedSegment calls _ := decision
      | throwError "conjunction union: conjunct has an unhandled decision tree"
    unless calls.isEmpty do throwError "conjunction: call assumptions require the split composer"
    unless value == term && path.isEmpty do
      throwError "conjunction union: conjunct value or path changed"
    if outcome == "segment-open" then
      unless emittedSegment == some [term] do
        throwError "conjunction union: open conjunct segment changed"
    else if outcome == "segment-false" then
      unless emittedSegment == some [] do
        throwError "conjunction union: false conjunct segment changed"
      let ctx ← pinTermOpaques cfg cfg.envExpr ctx term
      let v ← ctxValExpr cfg ctx term
      let some _ ← ctx.litFactByTermChecked? term (← mkEq v (mkConst ``SExpr.nil))
        | throwError "conjunction union: no checked falsity for the recorded false conjunct"
      falseCount := falseCount + 1
    else
      throwError "conjunction union: unsupported conjunct outcome {outcome}"
  unless falseCount > 0 do
    throwError "conjunction union: no false segment licenses the recorded subsumption"

end ACL2.Replay.Driver
