import ACL2Lean.Replay.Driver.Waterfall

namespace ACL2.Replay
open ACL2

/-- One recorded case is true (consume its negated-case child), or false
(peel it from the remaining-cases child). The remaining cases stay explicit. -/
theorem evtrue_recorded_case {w : World} {env : Env} {c vc rest goal : SExpr}
    (hNot : w.defs.get? { name := "NOT" } = none)
    (pc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some vc)
    (pos : EvTrue w env (.cons (.atom (.symbol { name := "IF" }))
      (.cons c (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
        (.cons SExpr.t .nil)) (.cons rest .nil)))))
    (neg : EvTrue w env (.cons (.atom (.symbol { name := "IF" }))
      (.cons (.cons (.atom (.symbol { name := "NOT" })) (.cons c .nil))
        (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
          (.cons SExpr.t .nil)) (.cons goal .nil)))))
    (next : EvTrue w env rest → EvTrue w env goal) : EvTrue w env goal := by
  by_cases hc : vc = .nil
  · subst vc
    exact next (evtrue_extract_else pc pos)
  · exact evtrue_extract_else
      (conv_not_nil_of_evtrue hNot (evtrue_of_conv_ne_nil pc hc)) neg

end ACL2.Replay

namespace ACL2.Replay.Driver
open ACL2 Lean Lean.Meta

partial def composeRecordedCases (cfg : ReplayConfig) (ctx : ReplayCtx)
    (cases goal : List SExpr) (pos : Expr) (negs : List Expr) : MetaM Expr := do
  match cases, negs with
  | [], [] => pure pos
  | c :: cs, neg :: ns =>
    let rest := disjoinTerm (cs ++ goal)
    let restTy := mkAppN (mkConst ``EvTrue)
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr rest]
    let next ← withLocalDeclD `hRemainingCases restTy fun hr => do
      mkLambdaFVars #[hr] (← composeRecordedCases cfg ctx cs goal hr ns)
    mkAppM ``ACL2.Replay.evtrue_recorded_case
      #[← proveNoShadow cfg { name := "NOT" }, ← ctxValProof cfg ctx c, pos, neg, next]
  | _, _ => throwError "cases-hint: case/child arity mismatch"

/-- Validate the recorded clause-set transformation before consuming any child.
The source algorithm is apply-cases-hint-clause (prove.lisp). This initial
consumer requires all generated clauses to survive unchanged; deduplicated
or tautology-dropped branches remain explicit frontiers. -/
def recordedCases (cn : ClauseNode) : Except String (List SExpr) := do
  let [step] := cn.steps | throw "cases-hint: expected one processor step"
  unless step.processor.toLower == "apply-top-hints-clause" && step.items.isEmpty &&
      step.extraFields.isEmpty && step.runes.isEmpty do
    throw "cases-hint: processor has additional content"
  unless !cn.inputClause.isEmpty do throw "cases-hint: empty input clause"
  let clauses ← step.newClauses.mapM fun x =>
    match x.toList? with
    | some cl => pure cl
    | none => throw "cases-hint: improper output clause"
  let first :: rest := clauses | throw "cases-hint: no output clause"
  unless first.length > cn.inputClause.length do throw "cases-hint: no case prefix"
  let count := first.length - cn.inputClause.length
  let cases := first.take count
  unless first.drop count == cn.inputClause do throw "cases-hint: input suffix changed"
  let expected := cases.map fun c =>
    SExpr.cons (.atom (.symbol { name := "NOT" })) (.cons c .nil) :: cn.inputClause
  unless rest == expected do throw "cases-hint: negated branches differ from recorded cases"
  unless cn.children.map (·.inputClause) == clauses do
    throw "cases-hint: child clauses differ from processor outputs"
  return cases

/-- Replay every recorded child, then compose the case partition. -/
def replayRecordedCases (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx)
    (cn : ClauseNode) : MetaM Expr := do
  let .ok cases := recordedCases cn
    | throwFrontier m!"apply-top-hints: unsupported recorded case partition at {cn.idStr}: {repr (recordedCases cn)}"
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx (disjoinTerm (cases ++ cn.inputClause))
  let childCtx := { ctx with litFacts := [], dedupDrops := [] }
  let proofs ← cn.children.mapM (rec.clause cfg childCtx)
  let pos :: negs := proofs | throwError "cases-hint: missing recorded child proofs"
  let p ← composeRecordedCases cfg ctx cases cn.inputClause pos negs
  mkExpectedTypeHint p (← mkAppM ``EvTrue
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr (disjoinTerm cn.inputClause)])

end ACL2.Replay.Driver
