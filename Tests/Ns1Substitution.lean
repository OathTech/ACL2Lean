import ACL2Lean.Replay.Runner
import ACL2Lean.DevLoad

/-! Actual NIQ and P6 hypothesis-instantiation folds and mutations of those
records. These checks certify captured computations; the whole quotient
bound and P6 still have separate replay/dependency frontiers. -/
open ACL2 ACL2.Replay ACL2.Replay.Driver Lean Lean.Meta Lean.Elab

namespace ACL2.Tests.Ns1Substitution
private def capture : String := include_str "../acl2_samples/ns1/nonnegative-integer-quotient.proof-log"
private def capturedDev : Development := load_development% capture
private def p6Capture : String := include_str "../acl2_samples/pattern-tests/p6-or-collapse-arith.proof-log"
private def p6Dev : Development := load_development% p6Capture

private partial def markers : ProofNode → List (SExpr × HypSubstitutionBasis)
  | .node _ lhs _ children prov =>
    (match prov.substBasis with
      | some b => if b.folds.isEmpty then [] else [(lhs, b)]
      | none => []) ++ children.flatMap markers
private partial def itemMarkers : ClauseItem → List (SExpr × HypSubstitutionBasis)
  | .literal lp => lp.nodes.flatMap markers
  | .step n => markers n
  | .branch _ items => items.flatMap itemMarkers
  | _ => []
private partial def clauseMarkers (cn : ClauseNode) : List (SExpr × HypSubstitutionBasis) :=
  (cn.steps.flatMap (·.items)).flatMap itemMarkers ++ cn.children.flatMap clauseMarkers
private def reject (label needle : String) (act : MetaM α) : MetaM Unit := do
  let msg ← try let _ ← act; pure none catch e => pure (some (← e.toMessageData.toString))
  let some msg := msg | throwError "{label}: accepted"
  unless (msg.splitOn needle).length > 1 do throwError "{label}: wrong refusal: {msg}"
  logInfo m!"{label}: refused by consuming check"

elab "checkActualSubstitutionFolds" : command => Command.liftTermElabM do
  for (label, dev) in [("NIQ", capturedDev), ("P6", p6Dev)] do
    let ms := (Runner.bookTrees dev).flatMap fun (_, cp) => cp.root.toList.flatMap clauseMarkers
    unless !ms.isEmpty do throwError "no actual substitution folds"
    let w ← reflectWorld dev.toWorld
    for ((target, basis), i) in ms.zipIdx do
      let p ← withLocalDeclD `env (mkConst ``Env) fun env => do
        let cfg := Runner.mkBookConfig dev dev.toWorld w env
        let some p ← replayHypSubstitution cfg basis target | throwError "actual folds produced no proof"
        mkLambdaFVars #[env] p
      Meta.checkWithKernel p
      let axioms ← Runner.collectProofAxioms p
      unless axioms.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
        throwError "unexpected fold proof axioms: {axioms}"
      logInfo m!"{label} substitution {i}: kernel-checked; {basis.folds.length} recorded folds"
    let some (target, basis) := ms.head? | throwError "first marker absent"
    withLocalDeclD `env (mkConst ``Env) fun env => do
      let cfg := Runner.mkBookConfig dev dev.toWorld w env
      reject "deleted fold" "recorded folds end at"
        (replayHypSubstitution cfg { basis with folds := [] } target)
      reject "changed fold result" "executable-counterpart: evalOpt computes"
        (replayHypSubstitution cfg { basis with folds := basis.folds.map fun f => { f with rhs := quoteNil } } target)
      reject "changed fold position" "expected redex"
        (replayHypSubstitution cfg { basis with folds := basis.folds.map fun f => { f with path := [0] } } target)
      reject "missing primitive guard" "no emitted cons-term guard"
        (replayHypSubstitution { cfg with consTermGuards := [] } basis target)
    -- These are negative-only payloads derived from the actual first record.
    let .error _ := ProofLog.parseHypSubstitutionBasis (some basis.input) none
      | throwError "unpaired substitution fields accepted"
    let some first := basis.folds.head? | throwError "actual first fold absent"
    let malformedPath := SExpr.ofList [
      .atom (.keyword "PATH"), SExpr.ofList [quoteT],
      .atom (.keyword "LHS"), first.lhs, .atom (.keyword "RHS"), first.rhs]
    let .error _ := ProofLog.parseHypSubstitutionBasis
        (some basis.input) (some (SExpr.ofList [malformedPath]))
      | throwError "non-integer substitution path accepted"
    logInfo m!"{label}: checked all {ms.length} actual nonempty substitution markers; malformed fields rejected"

checkActualSubstitutionFolds

end ACL2.Tests.Ns1Substitution
