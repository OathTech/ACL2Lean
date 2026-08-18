import Tests.Coverage.Harness
-- (PHASE 2 ITEM 2 — MEASURED AND NOT TAKEN, 2026-08-18: adding
-- `import ACL2Lean.Imported.Waypoints.EquisortParametric` here makes
-- the usefi prepare CONSUME the library parametric constants instead of
-- re-deriving the parametric trees per cite — the mechanism is live and
-- statement-matched fail-closed in mkUseFiDischarger, and it VERIFIED
-- (golden byte-identical, the three atAlias proofs consumed the library
-- constants). But the measured saving was ≈0 (the alias-world
-- instantiation engine, not the tree rebuild, dominates the prepare),
-- while the import couples this module + its dependents
-- (SortingPins*/DriverCoverage) to the Macro/PermBook/ConvertPerm/
-- OrderedPerms/EquisortParametric edit cone (~+28 min on that cascade
-- path). Flip = add the import line; everything else is already wired.)
-- Dep-module imports (perf arc phase 2 item 1b, 2026-08-17): the
-- covDeps module DAG — the dep books' own replayed constants become
-- visible, so the cross-book pre-pass TRANSPORTS them (Runner's
-- tryTransportDepConst) instead of re-replaying each tree here.
import Tests.Coverage.BSperm
import Tests.Coverage.BSconvertPermToHowMany
import Tests.Coverage.BSisort
import Tests.Coverage.BSbsort
import Tests.Coverage.BSorderedPerms
import Tests.Coverage.BSequisort
import Tests.Coverage.BSmsort
import Tests.Coverage.BSqsort

namespace ACL2.Tests.Coverage

set_option maxHeartbeats 0 in
coverage_book% "sorting/sorts-equivalent"

end ACL2.Tests.Coverage
