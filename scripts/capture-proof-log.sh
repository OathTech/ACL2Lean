#!/usr/bin/env bash
# Capture structured proof output from ACL2.
#
# Usage:
#   capture-proof-log.sh file.lisp              # single file
#   capture-proof-log.sh f1.lisp f2.lisp ...    # multiple files
#
# Output: file.proof-log alongside each input file.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ACL2="${ACL2:-$SCRIPT_DIR/../acl2/saved_acl2}"

if [ $# -eq 0 ]; then
  echo "Usage: capture-proof-log.sh file.lisp [file2.lisp ...]" >&2
  exit 1
fi

if [ ! -x "$ACL2" ]; then
  echo "Error: ACL2 executable not found at $ACL2" >&2
  echo "Run 'just build-acl2' first." >&2
  exit 1
fi

for INPUT in "$@"; do
  INPUT_ABS="$(cd "$(dirname "$INPUT")" && pwd)/$(basename "$INPUT")"
  OUTPUT="${INPUT_ABS%.lisp}.proof-log"

  if [ ! -f "$INPUT_ABS" ]; then
    echo "Error: $INPUT not found" >&2
    exit 1
  fi

  printf '(set-raw-proof-format :structured)
(ld "%s")
(good-bye)
' "$INPUT_ABS" | "$ACL2" > "$OUTPUT" 2>&1

  # Failure detection. `ld` halts on the first failed event (e.g. a defthm whose
  # PROOF succeeds but whose rule STORAGE is rejected — `:rule-classes nil` avoids
  # that). Under `:structured`, ACL2 suppresses the `:STOP-LD` / `******** FAILED`
  # text, so that grep alone can MISS a halt — a truncated log then looks clean.
  # The robust signal: ACL2 emits one `(:DEFTHM …)` per theorem it actually starts,
  # so fewer `(:DEFTHM` in the log than `(defthm` forms in the source means it
  # halted/failed partway. (Comments/`defthmd` make the source count approximate —
  # a mismatch is a loud warning, not a hard error.)
  want_defthm=$(grep -ciE '\(defthmd?\b' "$INPUT_ABS" || true)
  got_defthm=$(grep -c '(:DEFTHM' "$OUTPUT" || true)
  if grep -q ":STOP-LD\|\*\*\*\*\*\*\*\* FAILED" "$OUTPUT"; then
    echo "WARNING: $(basename "$INPUT") — ACL2 aborted an event (:STOP-LD); log is INCOMPLETE." >&2
  elif [ "$got_defthm" -lt "$want_defthm" ]; then
    echo "WARNING: $(basename "$INPUT") — logged $got_defthm of $want_defthm defthm proof(s); ACL2 likely FAILED/halted an event (error text suppressed by :structured). Log is INCOMPLETE." >&2
  fi

  echo "$(basename "$INPUT"): $(wc -l < "$OUTPUT") lines, $got_defthm/$want_defthm defthm(s) → $OUTPUT"
done
