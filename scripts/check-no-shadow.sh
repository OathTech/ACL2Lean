#!/usr/bin/env bash
# NO-SHADOW gate (external-knowledge design D3/D2, WP1).
#
# `Development.toWorld` must exclude from the world every ground-zero
# snapshot defun whose name `callBuiltin` dispatches — world-first dispatch
# (`evalOptStep`) would otherwise SHADOW the builtin, changing fuel profiles
# and falsifying the `hnew` side condition of `evalOpt_world_mono`. The
# exclusion set is `builtinNames` (EvalOpt.lean), which must stay in sync
# with `callBuiltin`'s match arms. This script scrapes BOTH from the source
# and diffs them, so adding a `callBuiltin` arm without updating
# `builtinNames` (the dangerous, silently-shadowing direction) fails CI.
#
# Scrape contract (loud-fail if the shapes drift):
#   - callBuiltin arms:  lines `| "NAME", ...` between `def callBuiltin`
#     and its terminating `| _, _ => none`
#   - builtinNames:      string literals in the list literal between
#     `def builtinNames` and the closing `]`
set -uo pipefail
cd "$(dirname "$0")/.." || { echo "FATAL: cannot cd to repo root" >&2; exit 2; }

SRC=ACL2Lean/EvalOpt.lean
fail=0

arms=$(awk '/^def callBuiltin/,/^  \| _, _ => none/' "$SRC" \
  | grep -oE '\|[[:space:]]*"[^"]+"' | sed -E 's/\|[[:space:]]*"//; s/"//' | sort -u)
listed=$(awk '/^def builtinNames/,/\]/' "$SRC" \
  | grep -oE '"[^"]+"' | sed 's/"//g' | sort -u)

if [ -z "$arms" ]; then
  echo "FAIL: scraped ZERO callBuiltin match arms from $SRC — scrape contract broken?"
  fail=1
fi
if [ -z "$listed" ]; then
  echo "FAIL: scraped ZERO builtinNames entries from $SRC — scrape contract broken?"
  fail=1
fi

missing=$(comm -23 <(echo "$arms") <(echo "$listed"))
stale=$(comm -13 <(echo "$arms") <(echo "$listed"))

if [ -n "$missing" ]; then
  echo "FAIL: callBuiltin dispatches names ABSENT from builtinNames (a ground-zero"
  echo "      snapshot with such a name would SHADOW the builtin in the world):"
  echo "$missing" | awk '{print "        " $0}'
  fail=1
fi
if [ -n "$stale" ]; then
  echo "FAIL: builtinNames lists names callBuiltin does NOT dispatch (stale entry —"
  echo "      would wrongly exclude a genuine ground-zero def from the world):"
  echo "$stale" | awk '{print "        " $0}'
  fail=1
fi

count=$(echo "$arms" | grep -c .)
if [ "$fail" -eq 0 ]; then
  echo "OK: no-shadow exclusion list in sync with callBuiltin ($count names)."
fi
exit $fail
