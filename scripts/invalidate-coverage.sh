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
echo "coverage artifacts invalidated (Tests/Coverage/** + aggregate)"
