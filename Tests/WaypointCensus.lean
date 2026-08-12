/-
  Tests/WaypointCensus — the WAYPOINT-LAYER SHAPE CENSUS.

  A WATCHED NUMBER, reviewed at book-family audits — never a build
  failure. This is the demoted shape gate (gate-cruft review
  2026-08-11): the gate classified every authored theorem in the waypoint
  content namespaces and threw on an unregistered one, which meant two
  hand registries and two count floors to maintain. The census-as-a-
  number was the whole value, so the number is all that survives: the
  same environment scan, printed. A growing `support/other` bucket is
  the signal an audit reads; nothing here can fail.
-/
import ACL2Lean.Imported.WaypointCatalog

namespace ACL2.Tests.WaypointCensus

open Lean

run_cmd do
  let env ← getEnv
  let nss : List Name := [`ACL2.Worlds, `ACL2.Lifting]
  let mut nCorr := 0; let mut nEnc := 0; let mut nDecode := 0
  let mut nDis := 0; let mut nWorld := 0; let mut other : List Name := []
  for (c, ci) in env.constants.toList do
    -- public authored theorems only: no internal details, no compiler
    -- satellites, and nothing nested under an existing constant
    if nss.any (·.isPrefixOf c) && !c.isInternalDetail
        && !env.contains c.getPrefix then
      if let .thmInfo _ := ci then
        let s := (c.componentsRev.headD Name.anonymous).toString
        if s.startsWith "eq_" || s == "eq_def" || s == "sizeOf_spec"
            || s == "induct" || c.components.any (· == `_unary) then
          pure ()
        else if s.endsWith "_of_replayed" then nDecode := nDecode + 1
        else if s.startsWith "dis_" || s.startsWith "drv_" then
          nDis := nDis + 1
        else if s.endsWith "_exec_corr" then nCorr := nCorr + 1
        else if s.endsWith "_enc" then nEnc := nEnc + 1
        else if s.startsWith "world_has_" || s.startsWith "world_no_" then
          nWorld := nWorld + 1
        else other := other ++ [c]
  let counts :=
    s!"corr {nCorr}, enc {nEnc}, decode {nDecode}, dis/drv {nDis}, "
      ++ s!"world-fact {nWorld}, support/other {other.length}"
  logInfo m!"waypoint census (watched number — never fails the build): \
    {counts}\nsupport/other: {other}"

end ACL2.Tests.WaypointCensus
