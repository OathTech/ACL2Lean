import Tests.Coverage.Harness

namespace ACL2.Tests.Coverage

-- hb guard (2026-08-19 sweep): NO outer envelope by policy — the real
-- per-theorem/per-leaf guards are internal (see coverage_book%). This book
-- measured 42k units.
set_option maxHeartbeats 0 in
coverage_book% "01-multi-theorem"

end ACL2.Tests.Coverage
