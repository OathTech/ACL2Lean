/-
  Driver/NodeCore — FACADE (perf arc 3a, 2026-08-07): the monolith now
  lives in six positional slices under NodeCore/ (Ctx → TypeSetWalk →
  Recognizer → Node → Rewrites → Literal, import-chained in the file's
  original def-before-use order — a MOVE-ONLY split). Importers of this
  module are unchanged.
-/
import ACL2Lean.Replay.Driver.NodeCore.Literal
