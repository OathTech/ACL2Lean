import ACL2Lean.ProofLog
import ACL2Lean.ClauseTree
import Lean

/-! # `load_development%` — fail-closed development loading

Capstone-demo arc Phase 0 (overall-project audit P2-10): the previous
idiom at every embedded-log site,

    (((ProofLog.parse xLog).toOption.bind
      fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

silently converted a parse or reconstruction failure into the EMPTY
development — diagnostics lost, and a definition-only consumer could
observe `.done` without any error. This elaborator VALIDATES the log at
compile time (parse + buildDevelopment run during elaboration; failure
is a compile error carrying the real diagnostic) and then emits the same
runtime term — whose `.getD .done` fallback is thereby
unreachable-by-construction for the validated constant.

`scripts/check-no-getd-done.sh` (in `just ci`) bans the raw idiom
everywhere outside this file. -/

namespace ACL2
open Lean Elab Term

elab "load_development% " logId:ident : term => do
  let logName ← Lean.resolveGlobalConstNoOverload logId
  let logStr ← unsafe Meta.evalExpr String (mkConst ``String)
    (mkConst logName)
  match ProofLog.parse logStr with
  | .error e =>
    throwError "load_development% {logName}: proof-log parse FAILED: {e}"
  | .ok l =>
    match ClauseTree.buildDevelopment l with
    | .error e =>
      throwError "load_development% {logName}: buildDevelopment FAILED: {e}"
    | .ok _ => pure ()
  elabTerm
    (← `((((ProofLog.parse $logId).toOption.bind
        fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done))
    (some (mkConst ``ACL2.Development))

end ACL2
