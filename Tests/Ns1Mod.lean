import Tests.Ns1Arithmetic

/-! The independent source pin consumes INTEGERP-MOD from the unmodified
arithmetic-3 floor/mod book. Its dependencies are separately replayed at the
same consumer World; each declaration uses the default command limit. -/
open ACL2 ACL2.Replay ACL2.Replay.Driver
namespace ACL2.Tests.Ns1Mod
private def miniLog : String := include_str "../acl2_samples/ns1/pass1/mini-theories.proof-log"
def miniDev : Development := load_development% miniLog
private def numLog : String := include_str "../acl2_samples/ns1/bind-free/numerator-and-denominator.proof-log"
def numDev : Development := load_development% numLog
private def modLog : String := include_str "../acl2_samples/ns1/floor-mod.proof-log"
def modDev : Development := load_development% modLog
derive_world modWorld from modDev
replayed_theorem congruence := driver_replayed% modDev modWorld "EQUIV-1-IMPLIES-EQUIV-*"
  from ACL2.Tests.Ns1Arithmetic.helperDev inline_deps
replayed_theorem cancel := driver_replayed% modDev modWorld "RIGHT-CANCELLATION-FOR-*"
  from ACL2.Tests.Ns1Arithmetic.helperDev inline_deps
replayed_theorem inverseUnique := driver_replayed% modDev modWorld "UNIQUENESS-OF-*-INVERSES-LEMMA"
  from ACL2.Tests.Ns1Arithmetic.helperDev inline_deps
replayed_theorem reciprocalEquality := driver_replayed% modDev modWorld "EQUAL-/"
  from ACL2.Tests.Ns1Arithmetic.helperDev inline_deps
replayed_theorem negateUnique := driver_replayed% modDev modWorld "UNIQUENESS-OF-+-INVERSES-LEMMA"
  from ACL2.Tests.Ns1Arithmetic.helperDev inline_deps
replayed_theorem negateTimes := driver_replayed% modDev modWorld "FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT"
  from ACL2.Tests.Ns1Arithmetic.helperDev inline_deps
replayed_theorem equalityIff := driver_replayed% modDev modWorld "REWRITE-LINEAR-EQUALITIES-TO-IFF"
  from miniDev inline_deps
replayed_theorem numeratorNegative := driver_replayed% modDev modWorld "NUMERATOR-NEGATIVE"
  from numDev inline_deps deps [miniDev]
replayed_theorem negateTwice := driver_replayed% modDev modWorld "FUNCTIONAL-SELF-INVERSION-OF-MINUS"
  from ACL2.Tests.Ns1Arithmetic.pass1Dev inline_deps
replayed_theorem reciprocalZero := driver_replayed% modDev modWorld "EQUAL-/-0"
  from ACL2.Tests.Ns1Arithmetic.pass1Dev inline_deps deps [ACL2.Tests.Ns1Arithmetic.helperDev]
replayed_theorem denominatorOne := driver_replayed% modDev modWorld "EQUAL-DENOMINATOR-1"
  from ACL2.Tests.Ns1Arithmetic.numdenDev inline_deps
replayed_theorem reciprocalPositive := driver_replayed% modDev modWorld "/-PRESERVES-POSITIVE"
  from ACL2.Tests.Ns1Arithmetic.inequalitiesDev inline_deps
replayed_theorem reciprocalNegative := driver_replayed% modDev modWorld "/-PRESERVES-NEGATIVE"
  from ACL2.Tests.Ns1Arithmetic.inequalitiesDev inline_deps
replayed_theorem productSign := driver_replayed% modDev modWorld "<-*-0"
  from ACL2.Tests.Ns1Arithmetic.inequalitiesDev inline_deps deps [ACL2.Tests.Ns1Arithmetic.pass1Dev]
replayed_theorem bindProductSign := driver_replayed% modDev modWorld "(< (* x y) 0)"
  from ACL2.Tests.Ns1Arithmetic.bindBasicDev inline_deps deps [ACL2.Tests.Ns1Arithmetic.pass1Dev, ACL2.Tests.Ns1Arithmetic.inequalitiesDev]
replayed_theorem integerModReplayed := driver_replayed% modDev modWorld "INTEGERP-MOD"
  inline_deps deps [ACL2.Tests.Ns1Arithmetic.helperDev, ACL2.Tests.Ns1Arithmetic.pass1Dev,
    ACL2.Tests.Ns1Arithmetic.bindBasicDev, ACL2.Tests.Ns1Arithmetic.numdenDev,
    ACL2.Tests.Ns1Arithmetic.inequalitiesDev, miniDev, numDev]
private def sym (s : String) : SExpr := .atom (.symbol {name := s})
private def app (s : String) (xs : List SExpr) : SExpr := SExpr.ofList (sym s :: xs)
theorem integerModSourcePinned (env : Env) : EvTrue modWorld env
    (app "IMPLIES" [app "IF" [app "INTEGERP" [sym "M"], app "INTEGERP" [sym "N"], quoteNil],
      app "INTEGERP" [app "MOD" [sym "M", sym "N"]]]) := integerModReplayed env
/-- info: 'ACL2.Tests.Ns1Mod.congruence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms congruence
/-- info: 'ACL2.Tests.Ns1Mod.cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cancel
/-- info: 'ACL2.Tests.Ns1Mod.inverseUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inverseUnique
/-- info: 'ACL2.Tests.Ns1Mod.reciprocalEquality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalEquality
/-- info: 'ACL2.Tests.Ns1Mod.negateUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negateUnique
/-- info: 'ACL2.Tests.Ns1Mod.negateTimes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negateTimes
/-- info: 'ACL2.Tests.Ns1Mod.equalityIff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms equalityIff
/-- info: 'ACL2.Tests.Ns1Mod.numeratorNegative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numeratorNegative
/-- info: 'ACL2.Tests.Ns1Mod.negateTwice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negateTwice
/-- info: 'ACL2.Tests.Ns1Mod.reciprocalZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalZero
/-- info: 'ACL2.Tests.Ns1Mod.denominatorOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms denominatorOne
/-- info: 'ACL2.Tests.Ns1Mod.reciprocalPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalPositive
/-- info: 'ACL2.Tests.Ns1Mod.reciprocalNegative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalNegative
/-- info: 'ACL2.Tests.Ns1Mod.productSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms productSign
/-- info: 'ACL2.Tests.Ns1Mod.bindProductSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bindProductSign
/-- info: 'ACL2.Tests.Ns1Mod.integerModReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integerModReplayed
-- A distinct consumer-world name has no cached mini-theories dependency.
-- The real NUMERATOR-NEGATIVE tree must retain that premise and the explicit
-- source-stage interface must refuse to publish it as a complete dependency.
derive_world missingDepsWorld from modDev
open Lean Lean.Meta Lean.Elab in
elab "ns1_source_stage_condition_control%" : command => Command.liftTermElabM do
  let stx ← `(term| driver_replayed% modDev missingDepsWorld "NUMERATOR-NEGATIVE"
    from numDev inline_deps)
  let msg ← try
    let _ ← Term.withoutErrToSorry <| Term.elabTerm stx none
    pure none
  catch e => pure (some (← e.toMessageData.toString))
  let some msg := msg | throwError "source stage accepted a missing dependency"
  unless msg.startsWith "driver_replayed% from: source replay keeps conditions" do
    throwError "source stage failed for another reason: {msg}"
  logInfo "source stage refuses the actual unclosed dependency"

/-- info: source stage refuses the actual unclosed dependency -/
#guard_msgs in
ns1_source_stage_condition_control%

end ACL2.Tests.Ns1Mod
