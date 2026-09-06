import ACL2Lean.Replay.Runner
open ACL2 ACL2.Replay Lean Lean.Elab

/-! The two private induction helpers from the unchanged NIQ prefix retain
model definitions and admission data without entering witness scope. Negative
controls modify parsed events in memory only, never a positive capture. -/
namespace ACL2.Tests.Ns1LocalDefinitions
private def niqLog : String :=
  include_str "../acl2_samples/ns1/nonnegative-integer-quotient.proof-log"
private def encapsulateLog : String :=
  include_str "../acl2_samples/pattern-tests/cov-encapsulate.proof-log"

elab "ns1_local_definition_pins%" : command => Command.liftTermElabM do
  let parseDev := fun (contents : String) => do
    let .ok log := ProofLog.parse contents
      | throwError "local definition pin: failed to parse capture"
    let dev ← match ClauseTree.buildDevelopment log with
      | .ok d => pure d
      | .error e => throwError "local definition pin: {e}"
    pure (log, dev)
  let (log, dev) ← parseDev niqLog
  let locals := log.events.filterMap fun
    | .localDefun n fs body j => some (n, fs, body, j)
    | _ => none
  unless locals.length == 2 do throwError "local definition pin: expected two actual NIQ helpers"
  let .ok scopes := dev.scopes | throwError "local definition pin: scope reconstruction failed"
  for (n, fs, body, j) in locals do
    unless dev.toWorld.defs.get? { name := n } == some (fs, body) do
      throwError "local definition pin: helper absent or changed in canonical model"
    unless j.isSome && dev.justifications.any (fun (nm, _) => nm == n) do
      throwError "local definition pin: helper admission justification lost"
    if scopes.any (fun s => s.witnesses.any (fun (nm, _, _) => nm == n)) then
      throwError "local definition pin: helper entered the constrained witness vocabulary"
    logInfo m!"local helper {n}: model body and admission retained; no witness registration"
  let badWitness := log.events.map fun
    | .localDefun n fs body j => .witnessDefun n fs body j
    | ev => ev
  match ClauseTree.buildDevelopment { events := badWitness } with
  | .error e => unless (e.splitOn "outside any").length > 1 do throwError "wrong witness control failure: {e}"
  | .ok _ => throwError "local definition pin: out-of-scope witness accepted"
  let (scopeLog, _) ← parseDev encapsulateLog
  let badHelper := scopeLog.events.map fun
    | .witnessDefun n fs body j => .localDefun n fs body j
    | ev => ev
  match ClauseTree.buildDevelopment { events := badHelper } with
  | .error e => unless (e.splitOn "inside an encapsulate").length > 1 do throwError "wrong helper control failure: {e}"
  | .ok _ => throwError "local definition pin: encapsulate witness accepted as ordinary helper"
  let (n, fs, _, j) := locals.head!
  let changed := .localDefun n fs (.atom (.number (.int 1))) j
  match ClauseTree.buildDevelopment { events := log.events ++ [changed] } with
  | .error e => unless (e.splitOn "conflicting definitions").length > 1 do throwError "wrong collision control failure: {e}"
  | .ok _ => throwError "local definition pin: local helper name collision accepted"
  logInfo "local/witness provenance controls and conflicting-body rejection pass"

ns1_local_definition_pins%

end ACL2.Tests.Ns1LocalDefinitions
