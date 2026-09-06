import ACL2Lean.Imported.Waypoints.Macro
import ACL2Lean.DevLoad

/-! Arithmetic admission regression from a real captured book. The statements
below force convergence of FLOOR and MOD through their emitted definitions. -/

open ACL2 ACL2.Replay ACL2.Replay.Driver Lean
namespace ACL2.Tests.Ns1NumericAdmission

private def sourceLog : String :=
  include_str "../acl2_samples/pattern-tests/cov-numeric-admission.proof-log"
def dev : Development := load_development% sourceLog
derive_world world from dev

replayed_theorem floorReplayed := driver_replayed% dev world "numeric-floor-opener"
replayed_theorem modReplayed := driver_replayed% dev world "numeric-mod-opener"

private def sym (s : String) : SExpr := .atom (.symbol { name := s })
private def app (s : String) (args : List SExpr) : SExpr := .cons (sym s) (SExpr.ofList args)

example (env : Env) : EvTrue world env
    (app "EQUAL" [app "NUMERIC-FLOOR" [sym "X", sym "Y"],
      app "FLOOR" [sym "X", sym "Y"]]) := floorReplayed env

example (env : Env) : EvTrue world env
    (app "EQUAL" [app "NUMERIC-MOD" [sym "X", sym "Y"],
      app "MOD" [sym "X", sym "Y"]]) := modReplayed env

/-- info: 'ACL2.Tests.Ns1NumericAdmission.floorReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms floorReplayed
/-- info: 'ACL2.Tests.Ns1NumericAdmission.modReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms modReplayed

end ACL2.Tests.Ns1NumericAdmission
