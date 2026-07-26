#!/usr/bin/env bash
# Dark-file gate (audit 2026-07-26 F2/F9): every git-tracked .lean source in
# the library/test trees must be REACHABLE from a build root via the import
# graph, or carry an explicit allowlist entry here with a reason. TamperTests
# (the soundness regression net) was dark for 179 commits because nothing
# enforced this; presence-of-.olean is NOT used as the signal because stale
# .oleans from manual standalone builds mask darkness. Static, no build.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

# Build roots: the library root, the test root, both executables, and the
# modules `just ci` builds as DIRECT lake targets (driver-coverage).
ROOTS=(ACL2Lean.lean Tests.lean Main.lean ReplayMain.lean Tests/DriverCoverage.lean)

# Deliberately-unreachable files, each with its recorded justification:
#   Imported/*Spike — J1 validation artifacts, self-disclosed as not
#   regression guards (audit F9: accurately self-describing, kept dark).
ALLOW=(
  "ACL2Lean/Imported/FlattenSpike.lean"
  "ACL2Lean/Imported/InterleaveSpike.lean"
)

# BFS the import graph.
declare -A reached
queue=()
for r in "${ROOTS[@]}"; do
  [ -f "$r" ] || { echo "check-dark-files: missing build root $r" >&2; exit 1; }
  reached["$r"]=1; queue+=("$r")
done
while [ "${#queue[@]}" -gt 0 ]; do
  f="${queue[0]}"; queue=("${queue[@]:1}")
  while IFS= read -r mod; do
    p="${mod//.//}.lean"
    [ -f "$p" ] || continue          # external package import
    if [ -z "${reached[$p]:-}" ]; then reached["$p"]=1; queue+=("$p"); fi
  done < <(grep -E '^import ' "$f" | awk '{print $2}')
done

fail=0
count=0
while IFS= read -r f; do
  count=$((count + 1))
  [ -n "${reached[$f]:-}" ] && continue
  skip=0
  for a in "${ALLOW[@]}"; do [ "$f" = "$a" ] && skip=1 && break; done
  [ "$skip" = "1" ] && continue
  echo "DARK FILE: $f — not reachable from any build root (${ROOTS[*]}) and not allowlisted" >&2
  fail=1
done < <(git ls-files 'ACL2Lean/*.lean' 'ACL2Lean/**/*.lean' 'Tests/*.lean')

if [ "$count" -eq 0 ]; then
  echo "check-dark-files: found NO .lean sources — wrong directory?" >&2
  exit 1
fi
if [ "$fail" -ne 0 ]; then
  echo "check-dark-files: FAILED — dark sources (wire them into a root or allowlist WITH a reason)." >&2
  exit 1
fi
echo "check-dark-files: $count sources all reachable (or explicitly allowlisted)."
