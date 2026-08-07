#!/usr/bin/env bash
# Module-size RATCHET (perf arc 3d; hardened per audit D1-D4,
# 2026-08-07): new .lean files are capped at the norm; grandfathered
# giants are pinned in the baseline and may only shrink. Exact-field
# awk lookup (no regex, no multi-match fail-open); duplicate baseline
# entries FAIL; stale baseline entries FAIL; the universe is tracked ∪
# untracked-not-ignored (a new giant is caught before `git add`).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
NORM=1500
BASELINE="$ROOT/scripts/file-weight-baseline.txt"
fail=0
# D1: duplicate entries fail closed
dups="$(awk '{print $1}' "$BASELINE" | sort | uniq -d)"
if [ -n "$dups" ]; then
  echo "check-file-weight: DUPLICATE baseline entries: $dups" >&2
  exit 1
fi
# D4: stale entries fail
while IFS=' ' read -r bf _; do
  [ -n "$bf" ] || continue
  if [ ! -f "$ROOT/$bf" ]; then
    echo "check-file-weight: STALE baseline entry (no such file): $bf" >&2
    fail=1
  fi
done < "$BASELINE"
while IFS= read -r f; do
  [ -f "$ROOT/$f" ] || continue
  n=$(wc -l < "$ROOT/$f")
  cap="$(awk -v f="$f" '$1==f {print $2; exit}' "$BASELINE")"
  [ -n "$cap" ] || cap=$NORM
  if [ "$n" -gt "$cap" ]; then
    echo "OVERWEIGHT: $f is $n lines (cap $cap) — split it, or (for a \
grandfathered file) it must not GROW: shrink it back or split" >&2
    fail=1
  elif [ "$cap" -gt "$NORM" ] && [ "$n" -lt "$cap" ]; then
    echo "  ratchet: $f shrank to $n (baseline $cap) — tighten the baseline" >&2
  fi
done < <(cd "$ROOT" && git ls-files -co --exclude-standard '*.lean')
[ "$fail" -eq 0 ] || { echo "check-file-weight: FAILED (see above)." >&2; exit 1; }
echo "check-file-weight: all modules within the norm/baseline."
