/-
  Proof-producing driver (stage 7 — the eventual `acl2_replay`).

  This is the schematic replay driver: it walks the reconstructed proof tree and
  emits a Lean `Expr` proving the replayed statement, by instantiating — per node —
  the per-rune combinator the hand proofs (`Imported/SimpleWorld.lean`,
  `Imported/AppAssoc.lean`) were written to be instances of. See
  `docs/plans/2026-06-08_driver-build-plan.md` and
  `docs/notes/2026-06-07_{driver-design,schematic-replay-rule}.md`.

  Replaces the retired `Replay/ProofProducer.lean` (the old value-computation
  skeleton, which computed both sides and matched — the banned shortcut).

  ## Architecture (per `docs/notes/2026-06-07_driver-design.md`).

  The driver is a RECURSIVE function over the reconstructed tree —
  `replayClause : World → Env → ReplayCtx → ClauseNode → MetaM Expr` and
  `replayNode : … → ProofNode → MetaM Expr` — reading every term/rune/subst/scheme
  FROM the tree. Nothing is transcribed or pre-staged: the only inputs are the
  parsed `Development`/`ClauseProof` (from `ProofLog.parse → buildDevelopment`) and
  the `World` + replayed statement — which, as WIRED, come from the SAME
  proof-log path, NOT from `gen-world`: the certified `World` is
  `Development.toWorld` (built from the log's `:DEFUN` events,
  provenance-gated per BUG-019) and the statement is
  `EvTrue w env (disjoinTerm root.inputClause)` over the log's root Goal
  clause (`Driver/Harness.lean`). `gen-world` is the INTENDED independent
  frontend and is not in the certified pipeline. (Header corrected
  2026-08-16 — the old "from `gen-world`" wording is exactly the mis-aim
  audit 2026-07-26 F5b flagged and CLAUDE.md warns auditors about.)

  FAIL-CLOSED, NEVER `sorry`. Each `replay*` either returns a real, kernel-checkable
  `Expr` of the node's exact goal, or **throws** — so an unimplemented frontier makes
  the theorem fail to compile, never produces a fake proof. This is a soundness
  invariant: a driver built only from `throwError` + kernel-checked per-rune lemmas
  can only ever emit valid proofs. (NO `mkSorry` anywhere — that would be a cheat.)

  Build sequence (see the plan file):
  - S1 — dummy driver, correct type, fail-closed (`throwError` on every node). Proven
    by `#check` of the types + a NEGATIVE test that it fails cleanly on a tree.
  - S2 — one `equal-self` node (hand-built minimal `ClauseProof` value) → a real
    sorry-free replayed statement, `#print axioms` clean. Solves the proof-object plumbing
    (reflection, fuel wrapper, statement matching, tactic) on the minimal case.
  - S3+ — grow by tree complexity (exec-counterpart, congruence, induction/IH), each
    driven by a progressively larger hand-built then real parsed tree.

  Below are the GENERAL, tree-agnostic helpers (reflection, congruence-path emitter,
  chaining, goal-type builders) the recursion is built from.
-/
import ACL2Lean.Replay.Driver.Harness

/-
  WP2 note (2026-07-18): this root module is a pure RE-EXPORT — all driver
  code lives in Driver/*.lean (see the module map in
  docs/plans/2026-07-18_driver-modular-refactor.md). Kept so every existing
  `import ACL2Lean.Replay.Driver` keeps working unchanged; keeping it
  code-free makes its re-elaboration on upstream changes near-free.
-/
