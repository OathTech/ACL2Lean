import ACL2Lean.Replay.Driver.TypeSetQuery.Common

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- Strict adapter for the existing definitional TP proof channel. The
record cites the function's sole stored, unconditional, value-only rule;
its pattern and corollary must be the same ones the checked world proof
binds. With no hypotheses, argument-valued union, lookup intersection, or
executed children, that application returns exactly the basic mask. Other
TYPE-SET-WITH-RULES derivations require their own recorded evidence. -/
def replayDefinitionalTpQuery? (cfg : ReplayConfig) (ctx : ReplayCtx)
    (q : TsQueryCapture.Query) : MetaM (Option (Rune × Expr)) := do
  if q.route != .nil || q.comparison != .nil || q.recognizer != .nil then return none
  let some (fn, args) := asApp q.term | return none
  let some (formals, _) := cfg.worldVal.defs.get? fn | return none
  let some rules := cfg.tpAllTps.lookup fn.name | return none
  let [rule] := rules
    | throwFrontier m!"type-set query: multiple stored TP rules need an application record"
  let entries ← tsQueryRead (queryTtreeEntries q.ttree)
  unless entries.any (fun (tag, entry) => tag == "LEMMA" &&
      ProofLog.parseRune? entry == some rule.rune) do return none
  unless rule.rune.ty == "type-prescription" && rule.rune.name == fn.name &&
      rule.rune.idx.isNone && rule.hyps.isEmpty && q.children.isEmpty &&
      q.lookup == SExpr.ofList [.nil, .nil] && formals.length == args.length do
    throwFrontier m!"type-set query: unsupported definitional TP application"
  let [(_, cor, _)] := ctx.tpHyps.filter (fun (name, _, _) => name == fn.name)
    | throwFrontier m!"type-set query: missing or ambiguous checked TP proof"
  let pattern := SExpr.ofList (.atom (.symbol fn) :: formals.map (.atom ∘ .symbol))
  unless rule.term == pattern && rule.corollary == cor do
    throwError "type-set query: stored TP differs from the checked source/world corollary"
  let some cls := tpCorClass? pattern cor
    | throwFrontier m!"type-set query: unsupported constant TP corollary"
  unless !cls.argIndexed && cls.tsMask == rule.basicTs && rule.basicTs == q.result do
    throwFrontier m!"type-set query: TP result differs from the constant corollary mask"
  let some (mask, proof) ← inTsFromCitedTp cfg ctx [fn.name] q.term (← ctxValExpr cfg ctx q.term)
    | throwFrontier m!"type-set query: checked TP corollary has no membership adapter"
  unless mask == q.result do throwError "type-set query: checked TP membership mask mismatch"
  return some (rule.rune, ← mkExpectedTypeHint proof (← tsQueryType cfg ctx q))

end ACL2.Replay.Driver
