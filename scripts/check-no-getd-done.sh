#!/usr/bin/env bash
# Ban the silent-empty-development idiom (capstone-demo arc Phase 0,
# overall-project audit P2-10): `.getD .done` swallows parse and
# reconstruction failures into an empty Development with no diagnostic.
# Every embedded-log site must use `load_development%`
# (ACL2Lean/DevLoad.lean), which validates at compile time and whose
# emitted fallback is unreachable-by-construction — DevLoad.lean is the
# ONLY file allowed to contain the raw pattern (it emits it).

set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"

hits="$(grep -rn "getD .done" "$ROOT/ACL2Lean" "$ROOT/Tests" \
  | grep -v "ACL2Lean/DevLoad.lean" || true)"
if [ -n "$hits" ]; then
  echo "check-no-getd-done: FAILED — raw '.getD .done' outside DevLoad.lean" >&2
  echo "(use load_development% — it reports parse/build errors at compile time):" >&2
  echo "$hits" >&2
  exit 1
fi
echo "check-no-getd-done: clean (load_development% everywhere)."
