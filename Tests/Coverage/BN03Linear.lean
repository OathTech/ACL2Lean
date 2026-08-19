import Tests.Coverage.Harness

namespace ACL2.Tests.Coverage

-- hb guard: measured 201k user units vs bound UNLIMITED (0) (2026-08-19 sweep).
-- Needed — over Lean's 200k default. TRIAGE SITE for the next perf/design
-- round: see the TODO heartbeat/recursion sweep item.
set_option maxHeartbeats 0 in
coverage_book% "03-linear"

end ACL2.Tests.Coverage
