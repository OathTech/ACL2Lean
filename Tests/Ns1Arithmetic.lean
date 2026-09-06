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

private def pass1Log : String := include_str "../acl2_samples/ns1/basic-arithmetic.proof-log"
def pass1Dev : Development := load_development% pass1Log
derive_world pass1World from pass1Dev

private def inequalitiesLog : String := include_str "../acl2_samples/ns1/inequalities.proof-log"
def inequalitiesDev : Development := load_development% inequalitiesLog
derive_world inequalitiesWorld from inequalitiesDev

private def helperLog : String := include_str "../acl2_samples/ns1/basic-arithmetic-helper.proof-log"
def helperDev : Development := load_development% helperLog
derive_world helperWorld from helperDev

private def bindBasicLog : String := include_str "../acl2_samples/ns1/basic.proof-log"
def bindBasicDev : Development := load_development% bindBasicLog
derive_world bindBasicWorld from bindBasicDev

private def numdenLog : String := include_str "../acl2_samples/ns1/numerator-and-denominator.proof-log"
def numdenDev : Development := load_development% numdenLog
derive_world numdenWorld from numdenDev

replayed_theorem denominatorOneReplayed :=
  driver_replayed% numdenDev numdenWorld "EQUAL-DENOMINATOR-1"

replayed_theorem productMinusOneReplayed :=
  driver_replayed% bindBasicDev bindBasicWorld "(* -1 x)"

replayed_theorem additiveInverseReplayed :=
  driver_replayed% helperDev helperWorld "UNIQUENESS-OF-+-INVERSES-LEMMA"
replayed_theorem multiplicationCongruenceReplayed :=
  driver_replayed% helperDev helperWorld "EQUIV-1-IMPLIES-EQUIV-*"
replayed_theorem productNegationReplayed :=
  driver_replayed% helperDev helperWorld "FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT"

replayed_theorem reciprocalPositiveReplayed :=
  driver_replayed% inequalitiesDev inequalitiesWorld "/-PRESERVES-POSITIVE"
replayed_theorem reciprocalNegativeReplayed :=
  driver_replayed% inequalitiesDev inequalitiesWorld "/-PRESERVES-NEGATIVE"

replayed_theorem timesZeroReplayed :=
  driver_replayed% timesDev timesWorld "*-OF-0"
replayed_theorem floorZeroReplayed :=
  driver_replayed% floorDev floorWorld "FLOOR-OF-0-ARG1" deps [timesDev]
replayed_theorem modZeroReplayed :=
  driver_replayed% modDev modWorld "MOD-OF-0-ARG1" deps [timesDev, floorDev]
replayed_theorem negateTwiceReplayed :=
  driver_replayed% pass1Dev pass1World "FUNCTIONAL-SELF-INVERSION-OF-MINUS"

replayed_theorem pass1TimesZeroReplayed :=
  driver_replayed% pass1Dev pass1World "TIMES-ZERO"
replayed_theorem productSignReplayed :=
  driver_replayed% inequalitiesDev inequalitiesWorld "<-*-0" inline_deps deps [pass1Dev]
replayed_theorem bindProductSignReplayed :=
  driver_replayed% bindBasicDev bindBasicWorld "(< (* x y) 0)"
    inline_deps deps [pass1Dev, inequalitiesDev]

-- Independent source-formula pin: ACL2 multiplication completes nonnumbers
-- as well as rational/complex inputs. The actual proof is one recorded DP leaf.
private def sym (s : String) : SExpr := .atom (.symbol { name := s })
private def app (s : String) (xs : List SExpr) : SExpr := .cons (sym s) (SExpr.ofList xs)
private def zero : SExpr := app "QUOTE" [.atom (.number (.int 0))]
private def nilTerm : SExpr := app "QUOTE" [.nil]
private def trueTerm : SExpr := app "QUOTE" [.t]

example (env : Env) : EvTrue helperWorld env
    (app "IMPLIES" [app "EQUAL" [sym "X1", sym "X2"],
      app "EQUAL" [app "BINARY-*" [sym "X1", sym "Y"],
        app "BINARY-*" [sym "X2", sym "Y"]]]) := multiplicationCongruenceReplayed env

example (env : Env) : EvTrue pass1World env
    (app "EQUAL" [app "BINARY-*" [zero, sym "X"], zero]) := pass1TimesZeroReplayed env

-- Both sign statements preserve the source's rational hypotheses. The core
-- proof has five recorded verdict leaves; the wrapper uses that proof and
-- two further leaves. Its syntactic premise stays in the statement as well.
example (env : Env) : EvTrue inequalitiesWorld env
    (app "IMPLIES" [app "IF" [app "RATIONALP" [sym "X"], app "RATIONALP" [sym "Y"], nilTerm],
      app "EQUAL" [app "<" [app "BINARY-*" [sym "X", sym "Y"], zero],
        app "IF" [app "NOT" [app "EQUAL" [sym "X", zero]],
          app "IF" [app "NOT" [app "EQUAL" [sym "Y", zero]],
            app "IFF" [app "<" [sym "X", zero], app "<" [zero, sym "Y"]], nilTerm],
          nilTerm]]]) := productSignReplayed env

example (env : Env) : EvTrue bindBasicWorld env
    (app "IMPLIES" [app "IF" [app "SYNP" [nilTerm,
      app "QUOTE" [app "SYNTAXP" [app "REWRITING-GOAL-LITERAL" [sym "X", sym "MFC", sym "STATE"]]],
      app "QUOTE" [app "IF" [app "REWRITING-GOAL-LITERAL" [sym "X", sym "MFC", sym "STATE"],
        trueTerm, nilTerm]]],
      app "IF" [app "RATIONALP" [sym "X"], app "RATIONALP" [sym "Y"], nilTerm], nilTerm],
      app "EQUAL" [app "<" [app "BINARY-*" [sym "X", sym "Y"], zero],
        app "IF" [app "EQUAL" [sym "X", zero], nilTerm,
          app "IF" [app "EQUAL" [sym "Y", zero], nilTerm,
            app "IF" [app "<" [sym "X", zero], app "<" [zero, sym "Y"],
              app "IF" [app "<" [zero, sym "X"], app "<" [sym "Y", zero], nilTerm]]]]]]) :=
  bindProductSignReplayed env

-- The unchanged source has no rationality or integrality premise.
example (env : Env) : EvTrue numdenWorld env
    (app "EQUAL" [app "EQUAL" [app "DENOMINATOR" [sym "X"],
      app "QUOTE" [.atom (.number (.int 1))]],
      app "IF" [app "INTEGERP" [sym "X"], app "INTEGERP" [sym "X"],
        app "NOT" [app "RATIONALP" [sym "X"]]]]) := denominatorOneReplayed env

example (env : Env) : EvTrue bindBasicWorld env
    (app "EQUAL" [app "BINARY-*" [app "QUOTE" [.atom (.number (.int (-1)))], sym "X"],
      app "UNARY--" [sym "X"]]) := productMinusOneReplayed env

example (env : Env) : EvTrue helperWorld env
    (app "IMPLIES" [app "IF" [app "ACL2-NUMBERP" [sym "X"],
      app "IF" [app "ACL2-NUMBERP" [sym "Y"],
        app "EQUAL" [app "BINARY-+" [sym "X", sym "Y"], zero], nilTerm], nilTerm],
      app "EQUAL" [app "UNARY--" [sym "X"], sym "Y"]]) := additiveInverseReplayed env

-- Keep the source's syntactic premise and its translated quoted arguments.
-- The replay consumes both recorded USE instances before its tau leaf.
example (env : Env) : EvTrue helperWorld env
    (app "IMPLIES" [app "SYNP" [nilTerm,
      app "QUOTE" [app "SYNTAXP" [app "NOT" [app "QUOTEP" [sym "Y"]]]],
      app "QUOTE" [app "IF" [app "NOT" [app "QUOTEP" [sym "Y"]], trueTerm, nilTerm]]],
      app "EQUAL" [app "BINARY-*" [sym "X", app "UNARY--" [sym "Y"]],
        app "UNARY--" [app "BINARY-*" [sym "X", sym "Y"]]]]) := productNegationReplayed env

example (env : Env) : EvTrue timesWorld env
    (app "EQUAL" [app "BINARY-*" [zero, sym "X"], zero]) := timesZeroReplayed env

example (env : Env) : EvTrue floorWorld env
    (app "EQUAL" [app "FLOOR" [zero, sym "J"], zero]) := floorZeroReplayed env

example (env : Env) : EvTrue modWorld env
    (app "EQUAL" [app "MOD" [zero, sym "Y"], zero]) := modZeroReplayed env

example (env : Env) : EvTrue pass1World env
    (app "EQUAL" [app "UNARY--" [app "UNARY--" [sym "X"]],
      app "FIX" [sym "X"]]) := negateTwiceReplayed env

-- Independent translated source statements: preserve both directions of
-- the sign equivalence and the rational hypothesis, with zero in its source
-- position. The two source proofs each split into two recorded tau leaves.
example (env : Env) : EvTrue inequalitiesWorld env
    (app "IMPLIES" [app "RATIONALP" [sym "X"],
      app "EQUAL" [app "<" [zero, app "UNARY-/" [sym "X"]],
        app "<" [zero, sym "X"]]]) := reciprocalPositiveReplayed env

example (env : Env) : EvTrue inequalitiesWorld env
    (app "IMPLIES" [app "RATIONALP" [sym "X"],
      app "EQUAL" [app "<" [app "UNARY-/" [sym "X"], zero],
        app "<" [sym "X", zero]]]) := reciprocalNegativeReplayed env

/-- info: 'ACL2.Tests.Ns1Arithmetic.reciprocalPositiveReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalPositiveReplayed

/-- info: 'ACL2.Tests.Ns1Arithmetic.additiveInverseReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms additiveInverseReplayed

/-- info: 'ACL2.Tests.Ns1Arithmetic.productMinusOneReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms productMinusOneReplayed

/-- info: 'ACL2.Tests.Ns1Arithmetic.productNegationReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms productNegationReplayed

/-- info: 'ACL2.Tests.Ns1Arithmetic.reciprocalNegativeReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalNegativeReplayed

/-- info: 'ACL2.Tests.Ns1Arithmetic.negateTwiceReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negateTwiceReplayed

/-- info: 'ACL2.Tests.Ns1Arithmetic.modZeroReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms modZeroReplayed

/-- info: 'ACL2.Tests.Ns1Arithmetic.floorZeroReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms floorZeroReplayed

/-- info: 'ACL2.Tests.Ns1Arithmetic.timesZeroReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms timesZeroReplayed

/-- info: 'ACL2.Tests.Ns1Arithmetic.denominatorOneReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms denominatorOneReplayed

/-- info: 'ACL2.Tests.Ns1Arithmetic.pass1TimesZeroReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pass1TimesZeroReplayed

/-- info: 'ACL2.Tests.Ns1Arithmetic.productSignReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms productSignReplayed

/-- info: 'ACL2.Tests.Ns1Arithmetic.bindProductSignReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bindProductSignReplayed

/-- info: 'ACL2.Tests.Ns1Arithmetic.multiplicationCongruenceReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms multiplicationCongruenceReplayed

end ACL2.Tests.Ns1Arithmetic
