import ACL2Lean.Imported.Waypoints.Macro
import ACL2Lean.Imported.RuleApp
import ACL2Lean.DevLoad

namespace ACL2.Imported.Waypoints

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! ## The 17-rule-application book — TLP-APP-NIL and TLP-APP-NIL-TWICE

The book's feature is RULE APPLICATION: TLP-APP-NIL is proved by
induction and stored as a conditional `:REWRITE` rule; TLP-APP-NIL-TWICE
then has NO induction of its own — its whole proof is two applications of
that stored rule (the inner redex, then the outer), each hypothesis
relieved from the clause's own `(NOT (TLP X))` literal via the
type-alist. Both golden rows are `REPLAYED ✓` UNCONDITIONAL (no `cond[…]`
on either).

What was missing was decode-side only, and only for `TLP`: the `APP` kit
is REUSED verbatim from `Imported/Rev.lean` (same symbol, same emitted
body — world-parametric, so it instantiates at THIS world by `decide`),
and the `(TLP X)` antecedent of both rows is discharged at the encoded
instance by `Worlds.RuleApp.tlpL_true` (this book's own recognizer
accepts every `enc` image), never assumed. -/

private def ruleAppLog : String :=
  include_str "../../../acl2_samples/recon-tests/17-rule-application.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def ruleAppDev : Development :=
  load_development% ruleAppLog

derive_world ruleAppWorldD from ruleAppDev

/-- The driver's replayed statement for TLP-APP-NIL (the proof OBJECT). -/
replayed_theorem tlpAppNilReplayedCond := driver_replayed% ruleAppDev ruleAppWorldD
  "tlp-app-nil"

/-- The driver replayed statement — UNCONDITIONAL, STATEMENT-PINNED to
    the hand `tlp_app_nilFormula` (read off the log's root Goal clause,
    line 37: `(IMPLIES (TLP X) (EQUAL (APP X 'NIL) X))`). -/
theorem tlpAppNilReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f ruleAppWorldD env
      Worlds.RuleApp.tlp_app_nilFormula = some v ∧ v ≠ SExpr.nil :=
  tlpAppNilReplayedCond env

/-- ENTRY, PROVED — `xs ++ [] = xs` (over `SExpr`) through the DRIVER's
    replayed statement, with this book's own `(TLP X)` antecedent
    discharged at the encoded instance. -/
theorem tlp_app_nil_native_driver (xs : List SExpr) : xs ++ [] = xs :=
  Worlds.RuleApp.tlp_app_nil_native_of_replayed ruleAppWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) tlpAppNilReplayed_uncond xs

#print axioms tlp_app_nil_native_driver

/-- The driver's replayed statement for TLP-APP-NIL-TWICE (the proof
    OBJECT) — the RULE-APPLICATION row: its tree has no induction, only
    the two `(:REWRITE TLP-APP-NIL)` applications. -/
replayed_theorem tlpAppNilTwiceReplayedCond := driver_replayed% ruleAppDev ruleAppWorldD
  "tlp-app-nil-twice"

/-- The driver replayed statement — UNCONDITIONAL, STATEMENT-PINNED to
    the hand `tlp_app_nil_twiceFormula` (the log's root Goal clause,
    line 59: `(IMPLIES (TLP X) (EQUAL (APP (APP X 'NIL) 'NIL) X))`). -/
theorem tlpAppNilTwiceReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f ruleAppWorldD env
      Worlds.RuleApp.tlp_app_nil_twiceFormula = some v ∧ v ≠ SExpr.nil :=
  tlpAppNilTwiceReplayedCond env

/-- ENTRY, PROVED — `(xs ++ []) ++ [] = xs` (over `SExpr`) through the
    DRIVER's replayed statement of the book's capstone. -/
theorem tlp_app_nil_twice_native_driver (xs : List SExpr) :
    (xs ++ []) ++ [] = xs :=
  Worlds.RuleApp.tlp_app_nil_twice_native_of_replayed ruleAppWorldD
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) tlpAppNilTwiceReplayed_uncond xs

#print axioms tlp_app_nil_twice_native_driver

end ACL2.Imported.Waypoints
