import Tests.Coverage.Harness
-- Dep-module imports (perf arc phase 2 item 1b, 2026-08-17): the
-- covDeps module DAG — the dep books' own replayed constants become
-- visible, so the cross-book pre-pass TRANSPORTS them (Runner's
-- tryTransportDepConst) instead of re-replaying each tree here.
import Tests.Coverage.BSperm
import Tests.Coverage.BSconvertPermToHowMany
import Tests.Coverage.BSorderedPerms

namespace ACL2.Tests.Coverage

-- hb guard (2026-08-19 sweep): NO outer envelope by policy — the real
-- per-theorem/per-leaf guards are internal (see coverage_book%). This book
-- measured 1.42M units.
set_option maxHeartbeats 0 in
coverage_book% "sorting/msort"

end ACL2.Tests.Coverage
