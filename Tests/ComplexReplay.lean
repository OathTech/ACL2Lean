import ACL2Lean.Imported.Waypoints.Macro
import ACL2Lean.DevLoad

/-! NS1 end-to-end regressions from actual ACL2 captures. These books
exercise closed executable arithmetic, a verdict-only parts leaf, and the
emitted numeric type prescription of a function returning a complex value.
The source statements are pinned independently below; none are mirrors.
-/

open ACL2 ACL2.Replay ACL2.Replay.Driver Lean Lean.Elab

namespace ACL2.Tests.ComplexReplay

private def arithmeticLog : String :=
  include_str "../acl2_samples/pattern-tests/cov-complex.proof-log"
private def functionLog : String :=
  include_str "../acl2_samples/pattern-tests/cov-complex-defun.proof-log"

def arithmeticDev : Development := load_development% arithmeticLog
def functionDev : Development := load_development% functionLog
derive_world arithmeticWorld from arithmeticDev
derive_world functionWorld from functionDev

replayed_theorem addReplayed := driver_replayed% arithmeticDev arithmeticWorld "complex-add"
replayed_theorem partsReplayed := driver_replayed% arithmeticDev arithmeticWorld "complex-parts"
replayed_theorem typeReplayed := driver_replayed% functionDev functionWorld "cplus-type"

private def sym (s : String) : SExpr := .atom (.symbol { name := s })
private def app (s : String) (args : List SExpr) : SExpr := .cons (sym s) (SExpr.ofList args)
private def quote (v : SExpr) : SExpr := app "QUOTE" [v]
private def num (n : Int) : SExpr := .atom (.number (.int n))
private def cx (r i : Int) : SExpr := Logic.mkParts (mkRat r 1) (mkRat i 1)

example (env : Env) : EvTrue arithmeticWorld env
    (app "EQUAL" [app "BINARY-+" [quote (cx 1 2), quote (cx 3 4)], quote (cx 4 6)]) :=
  addReplayed env

example (env : Env) : EvTrue arithmeticWorld env
    (app "IF" [app "EQUAL" [app "REALPART" [quote (cx 5 7)], quote (num 5)],
      app "EQUAL" [app "IMAGPART" [quote (cx 5 7)], quote (num 7)], quote .nil]) :=
  partsReplayed env

example (env : Env) : EvTrue functionWorld env
    (app "ACL2-NUMBERP" [app "CPLUS" [quote (num 3)]]) := typeReplayed env

-- A simple build-failing check on the three proof objects, complementing
-- the explicit unconditional statement pins. Do not harden this into a
-- second replay validator.
run_cmd Command.liftCoreM do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``addReplayed, ``partsReplayed, ``typeReplayed] do
    let axs ← collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do throwError "complex replay {n}: forbidden axioms {bad}"
    logInfo m!"{n}: {axs}"

end ACL2.Tests.ComplexReplay
