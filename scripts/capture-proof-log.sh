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
' "$INPUT_ABS" | "$ACL2" 2>&1 > "$OUTPUT"

  echo "$(basename "$INPUT"): $(wc -l < "$OUTPUT") lines → $OUTPUT"
done
