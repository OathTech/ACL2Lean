import Tests.Coverage.Harness
-- Dep-module imports (perf arc phase 2 item 1b, 2026-08-17): the
-- covDeps module DAG — the dep books' own replayed constants become
-- visible, so the cross-book pre-pass TRANSPORTS them (Runner's
-- tryTransportDepConst) instead of re-replaying each tree here.
import Tests.Coverage.BSperm
import Tests.Coverage.BSconvertPermToHowMany
import Tests.Coverage.BSorderedPerms

namespace ACL2.Tests.Coverage

-- hb guard: measured 5.28M user units vs bound UNLIMITED (0) (2026-08-19 sweep).
-- Needed — over Lean's 200k default. TRIAGE SITE for the next perf/design
-- round: see the TODO heartbeat/recursion sweep item.
set_option maxHeartbeats 0 in
coverage_book% "sorting/qsort"

end ACL2.Tests.Coverage
