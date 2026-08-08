/-
  Replay/EvalLemmas — FACADE (perf arc, 2026-08-07): the monolith now
  lives in five section-aligned slices under Lemmas/ (Core → Derived →
  Totality → Discharge → Judgments, import-chained in the file's own
  def-before-use order — a MOVE-ONLY split, token-diff proven).
  Importers of this module are unchanged.
-/
import ACL2Lean.Replay.Lemmas.Judgments
import ACL2Lean.Replay.Lemmas.FnAlias
import ACL2Lean.Replay.Lemmas.FnAliasLift
