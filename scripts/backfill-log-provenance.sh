#!/usr/bin/env bash
# ONE-TIME migration (capstone-demo arc Phase 0, review-1 P0-1,
# 2026-08-06): stamp source-identity fields into pre-existing sidecars
# whose logs predate the source-provenance capture fields.
#
# HONESTY NOTE: a backfilled stamp asserts "the CURRENT source text is
# the text this log was captured from." That assertion is not proven by
# capture (which is the point of the new fields) — it rests on the
# 2026-08-06 state of evidence: `just ci` green against these exact logs
# and sources, and the fork-commit + banner stamps already binding the
# image. Backfilled entries carry `source-provenance:
# backfilled-2026-08-06` so they remain distinguishable until Phase 1's
# full recapture replaces them with `captured` stamps. Refuses to touch
# a sidecar that already has source fields.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
# shellcheck source=lib-log-provenance.sh
. "$SCRIPT_DIR/lib-log-provenance.sh"

count=0
while IFS= read -r log; do
  meta="$log.meta"
  if [ ! -f "$meta" ]; then
    echo "Error: $log has no sidecar — recapture instead of backfilling" >&2
    exit 1
  fi
  if ! grep -q '^log-sha256: ' "$meta"; then
    # A2 one-time stamp: bind the CURRENT (gate-verified) log bytes.
    echo "log-sha256: $(sha256_of "$log")" >> "$meta"
    echo "log-hash stamped: $meta"
  fi
  if grep -q '^source-provenance: ' "$meta"; then
    echo "skip (already stamped): $meta"
    continue
  fi
  src="$(resolve_source_for_log "$log")"
  closure="$(include_closure "$src" "|$src|")"
  {
    echo "source-path: $(repo_rel "$src")"
    echo "source-sha256: $(sha256_of "$src")"
    while IFS= read -r inc; do
      [ -n "$inc" ] || continue
      case "$inc" in
        *" SYSTEM") incf="${inc% SYSTEM}"
          echo "include: $(repo_rel "$incf") $(sha256_of "$incf") system";;
        *) echo "include: $(repo_rel "$inc") $(sha256_of "$inc")";;
      esac
    done <<< "$closure"
    echo "source-provenance: backfilled-2026-08-06"
  } >> "$meta"
  count=$((count + 1))
  echo "stamped: $meta"
done < <(find "$ROOT/acl2_samples" -name '*.proof-log' | sort)

echo "backfill-log-provenance: stamped $count sidecar(s)."
