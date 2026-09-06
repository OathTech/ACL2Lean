import ACL2Lean.Replay.Runner
import ACL2Lean.DevLoad

/-! The two actual comparison-table hypotheses in the quotient upper-bound
proof. Context premises are drawn from that node's clause and branch path;
these fragment checks do not assert a complete quotient statement or mirror. -/
open ACL2 ACL2.Replay ACL2.Replay.Driver Lean Lean.Meta Lean.Elab
namespace ACL2.Tests.Ns1Comparison
private def capture : String := include_str "../acl2_samples/ns1/nonnegative-integer-quotient.proof-log"
private def capturedDev : Development := load_development% capture
private partial def comparisonNodes : ProofNode → List ProofNode
  | n@(.node _ _ _ children prov) =>
    (if prov.comparisonBasis.isSome then [n] else []) ++ children.flatMap comparisonNodes
private partial def itemComparisons (facts : List SExpr) : List ClauseItem → List (List SExpr × ProofNode)
  | [] => []
  | .branch seg items :: rest =>
    itemComparisons (facts ++ (match seg.toList? with | some fs => fs | none => panic! "malformed actual segment")) items ++ itemComparisons facts rest
  | .literal lp :: rest => (lp.nodes.flatMap comparisonNodes).map (facts, ·) ++ itemComparisons facts rest
  | .step n :: rest => (comparisonNodes n).map (facts, ·) ++ itemComparisons facts rest
  | _ :: rest => itemComparisons facts rest
private partial def clauseComparisons (cn : ClauseNode) : List (List SExpr × ProofNode) :=
  cn.steps.flatMap (fun s => itemComparisons cn.inputClause s.items) ++ cn.children.flatMap clauseComparisons
private def refuse (label needle : String) (act : MetaM (Option Expr)) : MetaM Unit := do
  let msg ← try let _ ← act; pure none catch e => pure (some (← e.toMessageData.toString))
  let some msg := msg | throwError "{label}: accepted"
  unless (msg.splitOn needle).length > 1 do throwError "{label}: wrong refusal: {msg}"
  logInfo m!"{label}: rejected by consuming check"
private partial def withFalseFacts (cfg : ReplayConfig) (facts : List SExpr) (ctx : ReplayCtx)
    (k : ReplayCtx → MetaM Expr) : MetaM Expr := do
  match facts with
  | [] => k ctx
  | f :: rest =>
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx f
    withLocalDeclD `hFact (← mkEq (← ctxValExpr cfg ctx f) (mkConst ``SExpr.nil)) fun h => do
      let p ← withFalseFacts cfg rest { ctx with segFacts := ctx.segFacts ++ [(f,h)] } k
      mkLambdaFVars #[h] p
elab "checkComparisons" : command => Command.liftTermElabM do
  let dev := capturedDev
  let some cp := findThm dev "NONNEGATIVE-INTEGER-QUOTIENT-UPPER-BOUND-LINEAR" | throwError "theorem"
  let some cn := cp.root | throwError "root"
  let ms := clauseComparisons cn
  unless ms.length == 2 do throwError "actual comparison count: {ms.length}"
  let w ← reflectWorld dev.toWorld
  for ((facts, marker), i) in ms.zipIdx do
    let .node rune hyp rhs kids prov := marker
    let some basis := prov.comparisonBasis | throwError "basis"
    let some (_, [_, b]) := asApp hyp | throwError "comparison"
    let vars := freeVars b
    let facts := facts.filter fun f =>
      (freeVars f).all vars.contains && (collectOpaques f).isEmpty
    logInfo m!"actual marker {i}: retained clause/branch facts {facts}"
    let p ← withLocalDeclD `env (mkConst ``Env) fun env => do
      let cfg := Runner.mkBookConfig dev dev.toWorld w env
      let p ← withFalseFacts cfg facts {} fun ctx => do
        let some p ← replayKnownTrueComparison? cfg ctx hyp [marker] | throwError "actual marker failed"
        let badResult := .node rune hyp rhs kids { prov with comparisonBasis := some { basis with resultTs := 128 } }
        refuse "changed result" "unsupported or inconsistent table masks" (replayKnownTrueComparison? cfg ctx hyp [badResult])
        let badProjection := .node rune hyp rhs kids { prov with comparisonBasis := some { basis with route := .nil } }
        refuse "removed selected route" "unsupported recorded route" (replayKnownTrueComparison? cfg ctx hyp [badProjection])
        let some parts := basis.route.toList? | throwError "actual table route is not a list"
        let numericBasis := { basis with
          route := SExpr.ofList (parts.modify 8 fun _ => .atom (.number (.int 1))) }
        let badNumeric := .node rune hyp rhs kids { prov with comparisonBasis := some numericBasis }
        refuse "changed numeric projection" "unsupported or inconsistent table masks"
          (replayKnownTrueComparison? cfg ctx hyp [badNumeric])
        refuse "removed context" "cannot establish recorded right mask" (replayKnownTrueComparison? cfg {} hyp [marker])
        unless (← replayKnownTrueComparison? cfg ctx hyp
            [.node rune hyp rhs kids { prov with comparisonBasis := none }]).isNone do
          throwError "removed basis accepted"
        let .error _ := ProofLog.parseHypComparisonBasis
            (some (SExpr.ofList [.atom (.keyword "RESULT"), quoteT,
              .atom (.keyword "ROUTE"), basis.route]))
          | throwError "non-integer comparison result parsed"
        let .error _ := ProofLog.parseHypComparisonBasis
            (some (SExpr.ofList [.atom (.keyword "RESULT"),
              .atom (.number (.int basis.resultTs))]))
          | throwError "missing comparison route parsed"
        return p
      mkLambdaFVars #[env] p
    Meta.checkWithKernel p
    let axioms ← Runner.collectProofAxioms p
    unless axioms.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "axioms: {axioms}"
    logInfo m!"actual marker {i}: kernel checked with accepted axioms"
checkComparisons

end ACL2.Tests.Ns1Comparison
