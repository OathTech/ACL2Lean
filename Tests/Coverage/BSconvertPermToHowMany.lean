import Tests.Coverage.Harness
-- Dep-module imports (perf arc phase 2 item 1b, 2026-08-17): the
-- covDeps module DAG — the dep books' own replayed constants become
-- visible, so the cross-book pre-pass TRANSPORTS them (Runner's
-- tryTransportDepConst) instead of re-replaying each tree here.
import Tests.Coverage.BSperm

namespace ACL2.Tests.Coverage

set_option maxHeartbeats 0 in
coverage_book% "sorting/convert-perm-to-how-many"

end ACL2.Tests.Coverage
