#!/usr/bin/env bash
# Preflight: every proof-log `include_str`'d by a Lean source must exist on disk.
#
# WHY THIS EXISTS. The .proof-log corpus is gitignored (regenerated from ACL2,
# not checked in) but embedded at compile time via `include_str`. Two lists
# must agree — the source files that `include_str` a log, and whatever step
# regenerates the logs (`just capture-all-logs` from acl2_samples/books.txt,
# or the CI capture step). If they desync, the build fails with an opaque
# `no such file or directory` deep in a Lean elaboration trace — and, worse,
# passes LOCALLY when a stale checked-out copy of the log happens to be present
# (so it only surfaces on a clean CI checkout). This preflight makes that
# failure loud, local, and actionable BEFORE the Lean build runs.
#
# It scans every `include_str "…proof-log"` across tracked Lean source,
# resolves each path the way Lean does (relative to the CONTAINING file's
# directory), and reports any that are missing with the fix hint.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

missing=0
checked=0

while IFS= read -r hit; do
  # hit = "path/to/File.lean:  include_str "../rel/log.proof-log""
  src="${hit%%:*}"
  rest="${hit#*:}"
  rel="$(printf '%s' "$rest" | sed -E 's/.*include_str "([^"]*)".*/\1/')"
  srcdir="$(dirname "$src")"
  resolved="$srcdir/$rel"
  checked=$((checked + 1))
  if [ ! -f "$resolved" ]; then
    echo "MISSING proof-log: $rel"
    echo "    include_str'd by: $src"
    missing=$((missing + 1))
  fi
done < <(git grep -n 'include_str "[^"]*proof-log"' -- '*.lean')

echo "checked $checked include_str proof-log reference(s)"

if [ "$missing" -gt 0 ]; then
  echo ""
  echo "ERROR: $missing proof-log(s) missing. The corpus is gitignored and must be"
  echo "regenerated from ACL2. Fix (run 'just build-acl2' first if acl2/saved_acl2"
  echo "is absent):"
  echo "    just capture-all-logs                              # sorting corpus (books.txt)"
  echo "    ./scripts/recon-test-dump.sh acl2_samples/recon-tests/*.lisp   # recon tests"
  echo "    ./scripts/capture-proof-log.sh acl2_samples/simple.lisp        # simple"
  echo ""
  echo "If you just added a book to the DriverCoverage corpus, also add its .lisp"
  echo "to acl2_samples/books.txt so capture-all-logs (and CI) produce its log."
  exit 1
fi
