import ACL2Lean.Imported.Waypoints.Macro
import ACL2Lean.DevLoad

/-! Ordinary bootstrap theorems are captured from their original source
proofs. They enter the same dependency registry as ordinary book theorems;
being declared in axioms.lisp gives them no primitive-rule exemption. -/
open ACL2 ACL2.Replay ACL2.Replay.Driver
namespace ACL2.Tests.Ns1Bootstrap

private def reciprocalLog : String :=
  include_str "../acl2_samples/ns1/bootstrap/reciprocal-default.proof-log"
def reciprocalDev : Development := load_development% reciprocalLog
derive_world reciprocalWorld from reciprocalDev

private def negationLog : String :=
  include_str "../acl2_samples/ns1/bootstrap/negation-distributivity.proof-log"
def negationDev : Development := load_development% negationLog
derive_world negationWorld from negationDev

-- BUG-060: the snapshot must not offer the newly proved rule before its
-- theorem. It must still retain the ordered, post-proof stored rule.
#guard (rulesBefore reciprocalDev "DEFAULT-UNARY-/").all (·.name != "DEFAULT-UNARY-/")
#guard (rulesBefore negationDev "DISTRIBUTIVITY-OF-MINUS-OVER-+").all
  (·.name != "DISTRIBUTIVITY-OF-MINUS-OVER-+")
#guard reciprocalDev.groundZeroRuleSpecs.all (·.name != "DEFAULT-UNARY-/")
#guard negationDev.groundZeroRuleSpecs.all (·.name != "DISTRIBUTIVITY-OF-MINUS-OVER-+")

#guard (ACL2.Replay.Runner.allBookRules reciprocalDev).any (·.name == "DEFAULT-UNARY-/")
#guard (ACL2.Replay.Runner.allBookRules negationDev).any
  (·.name == "DISTRIBUTIVITY-OF-MINUS-OVER-+")

replayed_theorem reciprocalDefaultReplayed :=
  driver_replayed% reciprocalDev reciprocalWorld "DEFAULT-UNARY-/"
replayed_theorem negationDistributivityReplayed :=
  driver_replayed% negationDev negationWorld "DISTRIBUTIVITY-OF-MINUS-OVER-+"

private def sym (s : String) : SExpr := .atom (.symbol {name := s})
private def app (s : String) (xs : List SExpr) : SExpr := SExpr.ofList (sym s :: xs)
private def x : SExpr := sym "X"
private def y : SExpr := sym "Y"
private def zero : SExpr := app "QUOTE" [.atom (.number (.int 0))]

example (env : Env) : EvTrue reciprocalWorld env
    (app "IMPLIES" [app "IF" [app "NOT" [app "ACL2-NUMBERP" [x]],
      app "NOT" [app "ACL2-NUMBERP" [x]], app "EQUAL" [x, zero]],
      app "EQUAL" [app "UNARY-/" [x], zero]]) := reciprocalDefaultReplayed env

example (env : Env) : EvTrue negationWorld env
    (app "EQUAL" [app "UNARY--" [app "BINARY-+" [x, y]],
      app "BINARY-+" [app "UNARY--" [x], app "UNARY--" [y]]]) :=
  negationDistributivityReplayed env

/-- info: 'ACL2.Tests.Ns1Bootstrap.reciprocalDefaultReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalDefaultReplayed
/-- info: 'ACL2.Tests.Ns1Bootstrap.negationDistributivityReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negationDistributivityReplayed

end ACL2.Tests.Ns1Bootstrap
