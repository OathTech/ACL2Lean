#!/usr/bin/env bash
# Capture proof logs AND reconstructed-tree dumps for the reconstruction
# feature-coverage tests in acl2_samples/recon-tests/.
#
# For each <file>.lisp it writes:
#   <file>.proof-log   raw structured ACL2 log
#   <file>.dump        reconstructed tree (dump-proof-tree), stderr included
#
# Both outputs are gitignored; this script regenerates them from source.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TESTS="$ROOT/acl2_samples/recon-tests"

# Build the Lean exe once up front, then invoke the built binary DIRECTLY.
# (Going through `lake exe` replays cached build diagnostics into the output;
# calling the binary keeps the dump clean — only the program's own stdout/stderr.)
( cd "$ROOT" && lake build acl2lean >/dev/null )
BIN="$ROOT/.lake/build/bin/acl2lean"

shopt -s nullglob
for SRC in "$TESTS"/*.lisp; do
  base="${SRC%.lisp}"
  echo "=== $(basename "$SRC") ==="
  "$SCRIPT_DIR/capture-proof-log.sh" "$SRC"
  # Reconstruct; keep stderr (parse errors / "no theorems") in the dump so the
  # review sees hard-fails rather than silent gaps.
  "$BIN" dump-proof-tree "$base.proof-log" > "$base.dump" 2>&1 || true
  echo "  → $(wc -l < "$base.dump") dump lines"
done
echo "Done. Dumps + logs in $TESTS/"
