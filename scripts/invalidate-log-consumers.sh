#!/usr/bin/env bash
# Shared by ordinary-book and bootstrap-source capture.
set -euo pipefail

# include_str does NOT register a Lake file dependency, and Lake hashes module
# CONTENT (touch does not invalidate), so a recaptured log silently leaves the
# STALE embedded copy inside the consumer's .olean (verified empirically
# 2026-06-10: modifying an embedded log triggers ZERO rebuilds). Force the
# consumers to recompile by deleting their build artifacts.
#
# The consumer list is DERIVED from the source (every .lean that include_str's a
# .proof-log), not hardcoded — a hardcoded list is one more thing to desync (the
# same bug class as the CI capture list). We resolve the repo root and the module
# path (repo-relative, no extension) for each match.
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
echo "forcing rebuild of include_str consumers (Lake does not track embedded logs):"
consumers="$(cd "$ROOT" && git grep -l 'include_str "[^"]*proof-log"' -- '*.lean' | sort -u)"
if [ -z "$consumers" ]; then
  echo "  WARNING: found NO include_str proof-log consumers — has the embed pattern changed?" >&2
fi
while IFS= read -r src; do
  [ -n "$src" ] || continue
  m="${src%.lean}"
  rm -f "$ROOT/.lake/build/lib/lean/$m.olean" \
        "$ROOT/.lake/build/lib/lean/$m.ilean" \
        "$ROOT/.lake/build/lib/lean/$m.trace"
  echo "  will rebuild: $m"
done <<EOF
$consumers
EOF
