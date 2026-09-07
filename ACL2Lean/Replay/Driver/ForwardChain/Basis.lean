import ACL2Lean.Replay.Driver.TypeSetQuery.Basis

namespace ACL2.Replay.Driver.FcCapture
open ACL2 TsQueryCapture

def substitution (s : SExpr) : Except String (List (Symbol × SExpr)) := do
  let xs ← asList s
  let pairs ← xs.mapM fun
    | .cons (.atom (.symbol v)) t => pure (v, t)
    | _ => throw "FC basis: malformed substitution binding"
  unless (pairs.map (·.1)).eraseDups.length == pairs.length do
    throw "FC basis: repeated substitution variable"
  pure pairs

structure Source where
  rune : Rune
  concl : SExpr
  trigger : SExpr
  subst : List (Symbol × SExpr)
  round : Nat
  parents : List SExpr
  supports : List SExpr
  rule : FcRuleSpec
  reliefs : List SExpr

def source (s : SExpr) : Except String Source := do
  let fs ← fields s ["RUNE", "CONCL", "TRIGGER", "SUBST", "FC-ROUND", "PARENTS",
    "SUPPORTS", "RULE-BASIS", "HYP-RELIEFS"]
  let some rune := ProofLog.parseRune? (← required fs "RUNE")
    | throw "FC basis: malformed rune"
  unless rune.ty == "forward-chaining" && rune.idx.isNone do
    throw "FC basis: unsupported rune class or indexed FC rule"
  let rf ← fields (← required fs "RULE-BASIS") ["RUNE", "TRIGGER", "HYPS", "CONCLS", "MATCH-FREE"]
  unless ProofLog.parseRune? (← required rf "RUNE") == some rune do
    throw "FC basis: source and stored rule runes differ"
  let matchFree ← match ← required rf "MATCH-FREE" with
    | .nil => pure none
    | .atom (.keyword k) => pure (some (k.map Char.toLower))
    | _ => throw "FC basis: malformed match-free"
  let round ← asInt (← required fs "FC-ROUND")
  unless round ≥ 0 do throw "FC basis: negative round"
  return {
    rune, round := round.toNat, concl := ← required fs "CONCL",
    trigger := ← required fs "TRIGGER", subst := ← substitution (← required fs "SUBST"),
    parents := ← asList (← required fs "PARENTS"), supports := ← asList (← required fs "SUPPORTS"),
    reliefs := ← asList (← required fs "HYP-RELIEFS"),
    rule := {
      name := rune.name, trigger := ← required rf "TRIGGER",
      hyps := ← asList (← required rf "HYPS"), concls := ← asList (← required rf "CONCLS"), matchFree } }

structure Context where
  accumulator : List SExpr
  tail : List SExpr
  literals : List SExpr
  selected : List SExpr
  currentParents : List SExpr
  ttree : SExpr

def context (s : SExpr) : Except String Context := do
  let fs ← fields s ["ACC-CLAUSE", "TAIL", "FC-LITERALS", "SELECTED-FC", "CURRENT-PARENTS", "TTREE"]
  return {
    accumulator := ← asList (← required fs "ACC-CLAUSE"),
    tail := ← asList (← required fs "TAIL"), literals := ← asList (← required fs "FC-LITERALS"),
    selected := ← asList (← required fs "SELECTED-FC"),
    currentParents := ← asList (← required fs "CURRENT-PARENTS"), ttree := ← required fs "TTREE" }

end ACL2.Replay.Driver.FcCapture
