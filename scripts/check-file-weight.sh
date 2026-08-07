#!/usr/bin/env bash
# Module-size RATCHET (perf arc 3d, user-requested 2026-08-07): heads
# off the giant-file default. Any tracked .lean over the norm must have
# a BASELINE entry (the grandfathered giants, pinned at their current
# size); a file may only SHRINK its baseline, never grow past it, and
# new files are capped at the norm outright. Cheap (wc -l); runs in ci.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
NORM=1500
BASELINE="$ROOT/scripts/file-weight-baseline.txt"
fail=0
while IFS= read -r f; do
  n=$(wc -l < "$ROOT/$f")
  cap=$NORM
  if b=$(grep -E "^${f//\//\\/} " "$BASELINE" 2>/dev/null | awk '{print $2}'); then
    [ -n "$b" ] && cap=$b
  fi
  if [ "$n" -gt "$cap" ]; then
    echo "OVERWEIGHT: $f is $n lines (cap $cap) — split it, or (for a \
grandfathered file) it must not GROW: shrink it back or split" >&2
    fail=1
  elif [ "$cap" -gt "$NORM" ] && [ "$n" -lt "$cap" ]; then
    echo "  ratchet: $f shrank to $n (baseline $cap) — tighten the baseline" >&2
  fi
done < <(cd "$ROOT" && git ls-files '*.lean')
[ "$fail" -eq 0 ] || { echo "check-file-weight: FAILED (see above)." >&2; exit 1; }
echo "check-file-weight: all modules within the norm/baseline."
