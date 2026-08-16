/-
  Driver/NodeCore — FACADE (perf arc 3a, 2026-08-07): the monolith now
  lives in eight positional slices under NodeCore/ (Ctx → Compose →
  TypeSetWalk → Recognizer → Node → Congruence → Rewrites → Literal,
  import-chained in the file's original def-before-use order — a
  MOVE-ONLY split; Compose split out of Ctx's tail 2026-08-08 when the
  parametric-replay routes regrew it past its baseline; Congruence added
  2026-08-14 by the G1 R-lane, carrying `replayNodeR` as a WRAPPER so
  Node.lean stays at its grandfathered weight cap). Importers of this
  module are unchanged.
-/
import ACL2Lean.Replay.Driver.NodeCore.Literal
