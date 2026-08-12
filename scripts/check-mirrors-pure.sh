#!/usr/bin/env bash
# check-mirrors-pure: the NORTH STAR layer (ACL2Lean/Mirrors/) is
# the PRODUCT — pure idiomatic Lean, and any ACL2 notion in it is
# DEFINITIONALLY A BUG (two-category ruling, Mike 2026-08-12). This
# check pins each Mirrors file's imports to Std/Batteries (Mathlib REMOVED from the allowlist 2026-08-12 — re-admitting it is a ruling, not a default: mirror content must come via replay, not library lemmas)
# ONLY: since none of those can import this package, a clean direct
# import list makes the whole closure ACL2-free.
# THREAT MODEL: claims-tier — the product layer's vocabulary IS the
# product, so this one is a build gate, not a speedbump.
set -euo pipefail
cd "$(dirname "$0")/.."

fail=0
for f in ACL2Lean/Mirrors/*.lean; do
  [ -e "$f" ] || continue
  bad=$(grep -E '^import ' "$f" | grep -Ev '^import (Std|Batteries)(\.|$)' || true)
  if [ -n "$bad" ]; then
    echo "MIRROR TAINT: $f imports outside Std/Batteries:" >&2
    echo "$bad" >&2
    fail=1
  fi
done
if [ "$fail" -ne 0 ]; then
  echo "check-mirrors-pure: FAILED — ACL2 notions are forbidden in the product layer" >&2
  exit 1
fi
echo "check-mirrors-pure: the product layer is ACL2-free (imports pinned to Std/Batteries; Mathlib excluded)."
