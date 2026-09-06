import ACL2Lean.Imported.Waypoints.Macro
import ACL2Lean.DevLoad

/-! Pins from unchanged, scoped community-book captures. These replayed
statements are dependency regressions, not native mirror products. -/

open ACL2 ACL2.Replay ACL2.Replay.Driver
namespace ACL2.Tests.Ns1Arithmetic

private def timesLog : String := include_str "../acl2_samples/ns1/times.proof-log"
def timesDev : Development := load_development% timesLog
derive_world timesWorld from timesDev

private def floorLog : String := include_str "../acl2_samples/ns1/floor.proof-log"
def floorDev : Development := load_development% floorLog
derive_world floorWorld from floorDev

private def modLog : String := include_str "../acl2_samples/ns1/mod.proof-log"
def modDev : Development := load_development% modLog
derive_world modWorld from modDev

replayed_theorem timesZeroReplayed :=
  driver_replayed% timesDev timesWorld "*-OF-0"
replayed_theorem floorZeroReplayed :=
  driver_replayed% floorDev floorWorld "FLOOR-OF-0-ARG1" deps [timesDev]
replayed_theorem modZeroReplayed :=
  driver_replayed% modDev modWorld "MOD-OF-0-ARG1" deps [timesDev, floorDev]

-- Independent source-formula pin: ACL2 multiplication completes nonnumbers
-- as well as rational/complex inputs. The actual proof is one recorded DP leaf.
private def sym (s : String) : SExpr := .atom (.symbol { name := s })
private def app (s : String) (xs : List SExpr) : SExpr := .cons (sym s) (SExpr.ofList xs)
private def zero : SExpr := app "QUOTE" [.atom (.number (.int 0))]
example (env : Env) : EvTrue timesWorld env
    (app "EQUAL" [app "BINARY-*" [zero, sym "X"], zero]) := timesZeroReplayed env

example (env : Env) : EvTrue floorWorld env
    (app "EQUAL" [app "FLOOR" [zero, sym "J"], zero]) := floorZeroReplayed env

example (env : Env) : EvTrue modWorld env
    (app "EQUAL" [app "MOD" [zero, sym "Y"], zero]) := modZeroReplayed env

/-- info: 'ACL2.Tests.Ns1Arithmetic.modZeroReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms modZeroReplayed

/-- info: 'ACL2.Tests.Ns1Arithmetic.floorZeroReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms floorZeroReplayed

/-- info: 'ACL2.Tests.Ns1Arithmetic.timesZeroReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms timesZeroReplayed

end ACL2.Tests.Ns1Arithmetic
