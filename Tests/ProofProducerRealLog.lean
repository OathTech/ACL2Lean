/-
  REAL-DATA test for the proof producer.

  Synthetic, hand-authored `ProofNode` tests were deleted (they gave false
  confidence — see docs/audits/2026-06-05_producer-triage.md). This is the sole
  producer test, and it drives the producer off the **reconstructed proof tree**
  of an actual ACL2 log:

      acl2_samples/simple.proof-log
        →  ProofLog.parse
        →  buildAllTheoremProofs   (TheoremProof → CaseProof → LiteralProof → ProofNode)
        →  proveNode  on every real node

  It is EXPECTED to fail on most nodes right now. The point is to measure, against
  real data, exactly which nodes the producer can discharge and where each one hits
  the frontier — that report is the worklist. As capability is added, more nodes flip
  to OK and the failure is pushed deeper.

  The world is `ACL2.Worlds.Simple.world` (the hand-written my-len/my-app world,
  a named/unfoldable const). If the reconstructed tree's symbols don't line up with
  it, that mismatch is itself a finding (the parse→world seam).
-/
import ACL2Lean.Replay.ProofProducer
import ACL2Lean.Imported.SimpleWorld
import ACL2Lean.ProofLog
import ACL2Lean.ProofTree

namespace ACL2.Replay.ProofProducer

open ACL2 ACL2.Replay Lean Elab Meta

/-- Walk the reconstructed proof tree of a real log and run `proveNode` on every
    top-level node of every literal, reporting OK / frontier per node. -/
elab "#produce_real_log" path:str : command => do
  Elab.Command.liftTermElabM do
    let p := path.getString
    let contents ← IO.FS.readFile p
    match ACL2.ProofLog.parse contents with
    | .error e => throwError "parse error: {e}"
    | .ok log =>
      let proofs := ACL2.buildAllTheoremProofs log
      let worldExpr := Lean.mkConst ``ACL2.Worlds.Simple.world
      let emptyEnv ← mkEmptyEnv
      let ctx : ProofCtx := {
        worldExpr := worldExpr
        world := ACL2.Worlds.Simple.world
        envExpr := emptyEnv
        worldUnfoldNames := #[``ACL2.Worlds.Simple.world,
          ``ACL2.Worlds.Simple.my_lenBody, ``ACL2.Worlds.Simple.my_appBody]
      }
      let mut ok := 0
      let mut fail := 0
      for proof in proofs do
        logInfo m!"══ theorem {proof.name} ══ (induction: {proof.induction.isSome}, {proof.cases.length} cases)"
        for c in proof.cases do
          for lp in c.literalProofs do
            for node in lp.nodes do
              match node with
              | .node (rt, rn) lhs _rhs _children _prov =>
                try
                  let pf ← proveNode ctx node
                  let _ ← check pf
                  ok := ok + 1
                  logInfo m!"  OK       {rt}:{rn}   {repr lhs}"
                catch ex =>
                  fail := fail + 1
                  let msg ← ex.toMessageData.toString
                  -- keep the report compact: first line of the failure
                  let firstLine := (msg.splitOn "\n").headD msg
                  logInfo m!"  FRONTIER {rt}:{rn}   {firstLine}"
      logInfo m!"━━ producer vs real tree: {ok} nodes discharged, {fail} at frontier ━━"

#produce_real_log "acl2_samples/simple.proof-log"

end ACL2.Replay.ProofProducer
