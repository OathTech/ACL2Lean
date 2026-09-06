import ACL2Lean.Imported.Waypoints.Macro
import ACL2Lean.DevLoad

/-! Actual captures for NS1's indexed binding relief and inherited LOCAL
provenance repairs. Source-statement pins below are independent of the log.
These are replay regressions, not native mirror products.
-/

open ACL2 ACL2.Replay ACL2.Replay.Driver Lean
namespace ACL2.Tests.Ns1Ingestion

private def bindingLog : String :=
  include_str "../acl2_samples/pattern-tests/cov-binding-hyp.proof-log"
private def includeLog : String :=
  include_str "../acl2_samples/pattern-tests/cov-local-include.proof-log"
private def foldLog : String :=
  include_str "../acl2_samples/pattern-tests/cov-cons-term-fold.proof-log"
private def quotedLog : String :=
  include_str "../acl2_samples/pattern-tests/cov-quoted-snapshot.proof-log"

def bindingDev : Development := load_development% bindingLog
def includeDev : Development := load_development% includeLog
def foldDev : Development := load_development% foldLog
def quotedDev : Development := load_development% quotedLog
derive_world bindingWorld from bindingDev
derive_world includeWorld from includeDev
derive_world foldWorld from foldDev
derive_world quotedWorld from quotedDev

replayed_theorem ruleReplayed := driver_replayed% bindingDev bindingWorld "bind-probe-rule"
replayed_theorem bindingReplayed := driver_replayed% bindingDev bindingWorld "bind-probe-result"
replayed_theorem includeReplayed := driver_replayed% includeDev includeWorld "ns1-local-include-result"
replayed_theorem exptReplayed := driver_replayed% foldDev foldWorld "expt-choice"
replayed_theorem carReplayed := driver_replayed% foldDev foldWorld "car-choice"
replayed_theorem quotedApplyReplayed := driver_replayed% quotedDev quotedWorld "quoted-apply-name"
replayed_theorem quotedEvReplayed := driver_replayed% quotedDev quotedWorld "quoted-ev-name"
replayed_theorem nulReplayed := driver_replayed% quotedDev quotedWorld "quoted-nul-data"
replayed_theorem diagnosticReplayed := driver_replayed% quotedDev quotedWorld "quoted-diagnostic-data"

private def sym (s : String) : SExpr := .atom (.symbol { name := s })
private def app (s : String) (args : List SExpr) : SExpr := .cons (sym s) (SExpr.ofList args)
private def quote (v : SExpr) : SExpr := app "QUOTE" [v]
private def x : SExpr := sym "X"
private def y : SExpr := sym "Y"
private def p : SExpr := sym "P"
private def num (k : Int) : SExpr := quote (.atom (.number (.int k)))

example (env : Env) : EvTrue bindingWorld env
    (app "IMPLIES" [app "IF" [app "INTEGERP" [x],
      app "EQUAL" [y, app "CDR" [app "CONS" [quote (.atom (.number (.int 0))), x]]],
      quote .nil], app "EQUAL" [app "BIND-PROBE" [x], y]]) := ruleReplayed env

example (env : Env) : EvTrue bindingWorld env
    (app "IMPLIES" [app "INTEGERP" [x],
      app "EQUAL" [app "BIND-PROBE" [x], x]]) := bindingReplayed env

example (env : Env) : EvTrue includeWorld env
    (app "EQUAL" [app "CAR" [app "NS1-INCLUDED-FN" [x]], x]) := includeReplayed env

example (env : Env) : EvTrue foldWorld env
    (app "EQUAL" [app "EXPT" [num 2, app "IF" [p, num 0, num 1]],
      app "IF" [p, num 1, num 2]]) := exptReplayed env

example (env : Env) : EvTrue foldWorld env
    (app "EQUAL" [app "CAR" [app "IF" [p, num 0,
      quote (SExpr.ofList [.atom (.number (.int 3))])]],
      app "IF" [p, quote .nil, num 3]]) := carReplayed env

example (env : Env) : EvTrue quotedWorld env
    (app "EQUAL" [app "CAR" [quote (SExpr.ofList [sym "APPLY$"])],
      quote (sym "APPLY$")]) := quotedApplyReplayed env

-- Pin actual character values after Latin-1 → UTF-8 capture conversion.
example (env : Env) : EvTrue quotedWorld env
    (app "EQUAL" [app "CAR" [app "CONS" [x,
      quote (.atom (.string (String.ofList ['H', Char.ofNat 0, Char.ofNat 255])))]],
      x]) := nulReplayed env

example (env : Env) : EvTrue quotedWorld env
    (app "EQUAL" [app "CAR" [app "CONS" [x,
      quote (.atom (.string "HARD ACL2 ERROR"))]], x]) := diagnosticReplayed env

#guard (quotedDev.toWorld.defs.get? { name := "APPLY$" }).isNone
#guard (quotedDev.toWorld.defs.get? { name := "EV$" }).isNone

/-- info: 'ACL2.Tests.Ns1Ingestion.ruleReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ruleReplayed
/-- info: 'ACL2.Tests.Ns1Ingestion.bindingReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bindingReplayed
/-- info: 'ACL2.Tests.Ns1Ingestion.includeReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms includeReplayed
/-- info: 'ACL2.Tests.Ns1Ingestion.exptReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exptReplayed
/-- info: 'ACL2.Tests.Ns1Ingestion.carReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms carReplayed
/-- info: 'ACL2.Tests.Ns1Ingestion.quotedApplyReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quotedApplyReplayed
/-- info: 'ACL2.Tests.Ns1Ingestion.quotedEvReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quotedEvReplayed
/-- info: 'ACL2.Tests.Ns1Ingestion.nulReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nulReplayed
/-- info: 'ACL2.Tests.Ns1Ingestion.diagnosticReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms diagnosticReplayed

/-- Corrupt only the hypothesis index in the parsed real capture. No generated
    artifact is written; this negative test pins ownership of recorded steps. -/
elab "check_binding_index_rejection%" : command => Lean.Elab.Command.liftTermElabM do
  let log ← match ProofLog.parse bindingLog with
    | .ok log => pure log
    | .error e => throwError "binding capture parse: {e}"
  let changed ← IO.mkRef (0 : Nat)
  let events ← log.events.mapM fun
    | .step s => do
      let traceEvents ← s.traceEvents.mapM fun
        | .rewriteStep rs => do
          let path ← rs.path.mapM fun
            | .bindingRhs i fn => do
              changed.modify (· + 1)
              pure (.bindingRhs (i + 1) fn)
            | p => pure p
          pure (.rewriteStep { rs with path })
        | t => pure t
      pure (.step { s with traceEvents })
    | e => pure e
  unless (← changed.get) > 0 do throwError "binding index test mutated no recorded boundary"
  let dev ← match ClauseTree.buildDevelopment { log with events } with
    | .ok dev => pure dev
    | .error e => throwError "binding index test failed before replay: {e}"
  let some cp := findThm dev "bind-probe-result"
    | throwError "binding index test: target absent"
  Lean.Meta.withLocalDeclD `env (mkConst ``Env) fun env => do
    let cfg : ReplayConfig := {
      worldExpr := mkConst ``bindingWorld, envExpr := env,
      worldVal := bindingDev.toWorld, gzDefs := bindingDev.groundZeroSnapshotDefs,
      justs := bindingDev.justifications }
    let failure ← try
      let _ ← replayProofConditional cfg dev.typePrescriptions cp dev.justifications
        (rulesBefore dev "bind-probe-result")
      pure none
    catch e => pure (some (← e.toMessageData.toString))
    let some failure := failure
      | throwError "binding index test: malformed index replayed"
    unless (failure.splitOn "binding-RHS index 3 outside its 2 hypotheses").length > 1 do
      throwError "binding index test: unexpected rejection: {failure}"
    logInfo "binding index rejected at recorded hypothesis ownership check"

check_binding_index_rejection%

end ACL2.Tests.Ns1Ingestion
