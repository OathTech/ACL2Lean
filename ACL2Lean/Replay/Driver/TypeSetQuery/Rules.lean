import ACL2Lean.Replay.Driver.TypeSetQuery.Basis
import ACL2Lean.Replay.Driver.NodeCore.TypeSetWalk
import ACL2Lean.Replay.Lemmas.TsQueryRecognizer

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

private def readQueryRule (x : Except String α) : MetaM α :=
  match x with
  | .ok a => pure a
  | .error e => throwError e

/-- Ttrees accumulate citations. Split them into tagged entries so inherited
evidence can be compared with incoming evidence without treating it as a new
inference. Unsupported new entries are still refused by the consumer. -/
def queryTtreeEntries (raw : SExpr) : Except String (List (String × SExpr)) := do
  (← TsQueryCapture.asList raw).flatMapM fun entry => do
    let .cons (.atom (.symbol tag)) xs := entry
      | throw "query ttree: malformed tagged entry"
    return (← TsQueryCapture.asList xs).map (tag.name, ·)

def queryTtreeCrRunes (raw : SExpr) : Except String (List Rune) := do
  let mut result := []
  for (tag, entry) in ← queryTtreeEntries raw do
    if tag == "LEMMA" then
      let some r := ProofLog.parseRune? entry | throw "query ttree: malformed lemma rune"
      if r.ty == "compound-recognizer" then result := result ++ [r]
  return result

private partial def queryRuleNames (raw : SExpr) : MetaM (List String) := do
  let q ← readQueryRule (TsQueryCapture.query raw)
  let rs ← readQueryRule (queryTtreeCrRunes q.ttree)
  return rs.map (·.name) ++ (← q.children.flatMapM queryRuleNames)

private partial def nodeQueryRuleNames : ProofNode → MetaM (List String)
  | .node _ _ _ children p => do
    let mut names := []
    for basis in p.hypTypeSetBasis.toList ++ p.operandTypeBasis.toList do
      unless basis == .nil do
        let fs ← readQueryRule (TsQueryCapture.fields basis ["TYPE-ALIST", "QUERIES"])
        let roots ← readQueryRule (TsQueryCapture.asList
          (← readQueryRule (TsQueryCapture.required fs "QUERIES")))
        names := names ++ (← roots.flatMapM queryRuleNames)
    return names ++ (← children.flatMapM nodeQueryRuleNames)

private partial def itemQueryRuleNames : ClauseItem → MetaM (List String)
  | .step n => nodeQueryRuleNames n
  | .literal lp => lp.nodes.flatMapM nodeQueryRuleNames
  | .branch _ items => items.flatMapM itemQueryRuleNames
  | .linearEquation _ | .unhideLiteral _ | .clausify _ | .useHint .. |
      .fcDerivations _ | .complementClose _ | .dedupDrop _ | .taSubst .. => pure []

private partial def clauseQueryRuleNames (cn : ClauseNode) : MetaM (List String) := do
  return (← cn.steps.flatMapM (fun s => s.items.flatMapM itemQueryRuleNames)) ++
    (← cn.children.flatMapM clauseQueryRuleNames)

private def classesNameCr : Option SExpr → Bool
  | some (.atom (.keyword "COMPOUND-RECOGNIZER")) => true
  | some raw => (raw.toList?).any fun xs => xs.any fun
    | .atom (.keyword "COMPOUND-RECOGNIZER") | .cons (.atom (.keyword "COMPOUND-RECOGNIZER")) _ => true
    | _ => false
  | none => false

/-- An ordinary query rule uses the existing whole-formula offer type and
dependency transport, with a separate condition class. Never offer self,
later same-book rules, absent source trees, or ambiguous formulas. -/
def recordedQueryRuleSpecs (cp : ClauseProof) (depProofs sameBook : List (String × ClauseProof))
    (earlier : List String) : MetaM (List UseSpec) := do
  let names := (← cp.root.toList.flatMapM clauseQueryRuleNames).eraseDups
  let mut specs := []
  for name in names do
    unless name == cp.name || (sameBook.any (fun (n, _) => n == name) && !earlier.contains name) do
      let formulas := (depProofs.filterMap fun (n, dcp) =>
        if n != name || !classesNameCr dcp.classes then none else
        match dcp.root with
        | some root => match root.inputClause with
          | [formula] => some formula
          | _ => none
        | none => none).eraseDups
      match formulas with
      | [] => pure () -- The consumer fails if this missing source is selected.
      | [formula] => specs := specs ++ [{ name := name, formula := formula }]
      | _ => throwFrontier m!"query rule: ambiguous source formulas for {name}"
  return specs

/-- Instantiate the source theorem whose RHS is the translated Boolean
cell test. The predicate head and formal come from that source, while the
cited rune selects the theorem. Neither a theorem name nor a primitive
predicate implementation supplies the equivalence. -/
def queryBooleanRecognizerEquivalence (cfg : ReplayConfig) (ctx : ReplayCtx)
    (rune : Rune) (argument : SExpr) : MetaM (SExpr × Expr × ReplayCtx) := do
  unless rune.ty == "compound-recognizer" && rune.idx.isNone do
    throwFrontier m!"query recognizer: unsupported cited rule class/index {rune}"
  let [(spec, hp)] := ctx.queryRuleHyps.filter (fun (s, _) => s.name == rune.name)
    | throwFrontier m!"query recognizer: absent or ambiguous ordinary source proof for {rune}"
  let some (eqFn, [pred, rhs]) := asApp spec.formula
    | throwFrontier m!"query recognizer: source is not an equivalence"
  let some (_, [formal@(.atom (.symbol formalVar))]) := asApp pred
    | throwFrontier m!"query recognizer: source predicate is not unary on a formal"
  let app (f : String) (args : List SExpr) := SExpr.ofList (.atom (.symbol {name := f}) :: args)
  let et := app "EQUAL" [formal, quoteT]
  unless eqFn.name == "EQUAL" && rhs == app "IF" [et, et, app "EQUAL" [formal, quoteNil]] &&
      formalVar.name != "T" do
    throwFrontier m!"query recognizer: unsupported source cell-test equivalence"
  let (p, ctx) ← instantiateEvTrueHypAt cfg ctx hp [formalVar] [argument] spec.formula
  let formula := substTerm [formalVar] [argument] spec.formula
  let predicate := substTerm [formalVar] [argument] pred
  let hne ← mkAppM ``ne_nil_of_evtrue_conv #[p, ← ctxValProof cfg ctx formula]
  let heq ← mkAppM ``Logic.eq_of_equal_ne_nil #[hne]
  let want ← mkEq (← ctxValExpr cfg ctx predicate)
    (← mkAppM ``booleanCellTest #[← ctxValExpr cfg ctx argument])
  return (predicate, ← mkExpectedTypeHint heq want, ctx)

/-- A lookup citing an ordinary recognizer obtains its argument membership
from a checked predicate premise and the instantiated replayed theorem. -/
def queryRecognizerLookup (cfg : ReplayConfig) (ctx : ReplayCtx)
    (term : SExpr) (mask : Int) (runes : List Rune) : MetaM Expr := do
  let [rune] := runes | throwFrontier m!"query lookup: multiple ordinary recognizer sources"
  let (predicate, heq, ctx) ← queryBooleanRecognizerEquivalence cfg ctx rune term
  let some hp ← typeSetWalk cfg ctx (.isTruthy predicate)
    | throwFrontier m!"query lookup: no checked premise for {repr predicate}"
  let hm ← mkAppM ``inTs_of_recognizer_equivalence #[heq, hp]
  unless tsSubsumedM 384 mask do
    throwFrontier m!"query lookup: ordinary Boolean premise does not establish mask {mask}"
  return ← mkAppM ``inTs_weaken #[← tsSubsumedProofM 384 mask, hm]

end ACL2.Replay.Driver
