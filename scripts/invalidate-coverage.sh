#!/usr/bin/env bash
# ONE source of truth for coverage-artifact invalidation (audit A6):
# the coverage modules read logs/golden via IO, invisible to Lake — any
# artifact change must delete their build products. Recursive (covers
# future subdirs). Used by capture-proof-log.sh (BEFORE capture — audit
# A1) and `just coverage-repin`.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
if [ -d "$ROOT/.lake/build/lib/lean/Tests/Coverage" ]; then
  find "$ROOT/.lake/build/lib/lean/Tests/Coverage" \
       \( -name '*.olean' -o -name '*.ilean' -o -name '*.trace' \) \
       -exec rm -f {} +
fi
rm -f "$ROOT"/.lake/build/lib/lean/Tests/DriverCoverage.{olean,ilean,trace}
# The waypoint catalog ALSO reads the golden via IO (its lift-coverage
# gate) — a stale Catalog.olean masks missing catalog decisions (found
# independently by both T1+2 P5 lanes, 2026-08-16). Speedbump against
# the honest mistake; do not harden further.
rm -f "$ROOT"/.lake/build/lib/lean/ACL2Lean/Imported/Waypoints/Catalog.{olean,ilean,trace}
echo "coverage artifacts invalidated (Tests/Coverage/** + aggregate + the catalog gate)"
