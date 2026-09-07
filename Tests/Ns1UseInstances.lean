import ACL2Lean.Imported.Waypoints.Macro
import ACL2Lean.DevLoad

/-! BUG-042: the actual macro-instance capture retains source and translated
LMIs. The second theorem consumes the recorded USE of the earlier theorem.
Negative controls modify only parsed records in memory. -/
open ACL2 ACL2.Replay ACL2.Replay.Driver Lean
namespace ACL2.Tests.Ns1UseInstances

private def capture : String := include_str "../acl2_samples/ns1/use-instances.proof-log"
def dev : Development := load_development% capture
derive_world world from dev

replayed_theorem headReplayed := driver_replayed% dev world "NS1-USE-HEAD"
replayed_theorem instanceReplayed := driver_replayed% dev world "NS1-USE-MACRO-PRODUCT"

private def sym (s : String) : SExpr := .atom (.symbol { name := s })
private def app (s : String) (xs : List SExpr) : SExpr := .cons (sym s) (SExpr.ofList xs)

example (env : Env) : EvTrue world env
    (app "EQUAL" [app "CAR" [app "CONS" [
      app "BINARY-*" [sym "X", app "UNARY--" [sym "Y"]], sym "Z"]],
      app "BINARY-*" [sym "X", app "UNARY--" [sym "Y"]]]) := instanceReplayed env

/-- info: 'ACL2.Tests.Ns1UseInstances.instanceReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instanceReplayed

elab "ns1_use_instance_controls%" : command => Elab.Command.liftTermElabM do
  let .ok log := ProofLog.parse capture | throwError "USE controls: capture parse failed"
  for kind in ["missing", "wrong-term", "misaligned"] do
    let changed ← IO.mkRef (0 : Nat)
    let events ← log.events.mapM fun
      | .step s => do
        let traceEvents ← s.traceEvents.mapM fun
          | .useHint hyps ccl appC raw translated folds => do
            let some [cooked] := translated
              | throwError "USE controls: actual translated instance missing"
            unless raw.length == 1 && raw != [cooked] do
              throwError "USE controls: source macro translation was not captured"
            changed.modify (· + 1)
            let tr ← if kind == "missing" then pure none
              else if kind == "misaligned" then pure (some [])
              else do
                let some [tag, name, first, second] := cooked.toList?
                  | throwError "USE controls: unexpected actual LMI shape"
                let some [formal, _] := first.toList?
                  | throwError "USE controls: unexpected actual binding shape"
                pure (some [SExpr.ofList [tag, name,
                  SExpr.ofList [formal, quoteNil], second]])
            pure (.useHint hyps ccl appC raw tr folds)
          | ev => pure ev
        pure (.step { s with traceEvents })
      | ev => pure ev
    unless (← changed.get) == 1 do throwError "USE controls: did not change one actual instance"
    let .ok bad := ClauseTree.buildDevelopment { log with events }
      | throwError "USE controls: reconstruction failed before the consuming check"
    let some cp := findThm bad "NS1-USE-MACRO-PRODUCT"
      | throwError "USE controls: target missing"
    let deps := (developmentTheoremsWithRules bad).map (fun (p, _) => (p.name, p))
    Meta.withLocalDeclD `env (mkConst ``Env) fun env => do
      let cfg : ReplayConfig := {
        worldExpr := mkConst ``world, envExpr := env, worldVal := bad.toWorld,
        gzDefs := bad.groundZeroSnapshotDefs, justs := bad.justifications }
      let failure ← try
        let _ ← replayProofConditional cfg bad.typePrescriptions cp bad.justifications
          (rulesBefore bad cp.name) deps
        pure none
      catch e => pure (some (← e.toMessageData.toString))
      let some failure := failure | throwError "USE controls: {kind} instance was accepted"
      let expected := if kind == "misaligned" then "invalid translated instance records"
        else "≠ the emitted :HYPS"
      unless (failure.splitOn expected).length > 1 do
        throwError "USE controls: unexpected {kind} failure: {failure}"
      logInfo m!"USE {kind} rejected at the recorded-instance check"

ns1_use_instance_controls%

end ACL2.Tests.Ns1UseInstances
