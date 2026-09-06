import ACL2Lean.Replay.Runner

/-! Guard trees stay in the reconstructed development, outside its logical
theorem registry. This uses the existing real ACL2 capture, including the
logical theorem after VERIFY-GUARDS. Negative mutation is in memory only. -/

open ACL2 ACL2.Replay Lean
namespace ACL2.Tests.Ns1GuardTrees

private def guardLog : String :=
  include_str "../acl2_samples/pattern-tests/cov-verify-guards.proof-log"

private def removeGuardQed : List ProofEvent → Bool → List ProofEvent
  | [], _ => []
  | .verifyGuards g :: es, _ => .verifyGuards g :: removeGuardQed es true
  | .qed :: es, true => es
  | e :: es, openGuard => e :: removeGuardQed es openGuard

elab "ns1_guard_tree_pins%" : command => Elab.Command.liftTermElabM do
  let .ok log := ProofLog.parse guardLog | throwError "guard pin: capture parse failed"
  let dev ← match ClauseTree.buildDevelopment log with
    | .ok dev => pure dev
    | .error e => throwError "guard pin: reconstruction failed: {e}"
  let [(guard, proof)] := dev.guardProofs | throwError "guard pin: expected one guard tree"
  unless guard.names.map (·.name) == ["GSUM"] && proof.root.isSome do
    throwError "guard pin: GSUM guard waterfall was not retained"
  unless (Runner.bookTrees dev).map (·.1) == ["GSUM-OF-NIL"] do
    throwError "guard pin: guard proof leaked into logical theorem offers"
  let mutated := removeGuardQed log.events false
  unless mutated.length + 1 == log.events.length do
    throwError "guard pin: negative control did not remove exactly one QED"
  match ClauseTree.buildDevelopment { events := mutated } with
  | .ok _ => throwError "guard pin: missing guard QED was accepted"
  | .error e =>
    unless (e.splitOn "VERIFY-GUARDS").length > 1 &&
        (e.splitOn "closing (:QED)").length > 1 do
      throwError "guard pin: negative control failed at a different boundary: {e}"
  let (res, _) ← Runner.runBook "cov-verify-guards" guardLog
  unless res.integrityFails.isEmpty && res.total == 1 && res.replayed == 1 &&
      res.replayedCond == 0 && res.lines.any (·.endsWith
        "→ UNSUPPORTED (guard-proof tree retained; no replay)") do
    throwError "guard pin: expected one unconditional logical row and a reported guard frontier: {res.lines}"
  logInfo "NS1 guard tree retained; guard QED omission rejected; GSUM-OF-NIL replays unconditionally"

ns1_guard_tree_pins%

end ACL2.Tests.Ns1GuardTrees
