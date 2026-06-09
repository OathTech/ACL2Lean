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
  #
  # The PRIMARY signal is QED-per-DEFTHM: a successful proof emits one `(:QED)` per
  # `(:DEFTHM …)` it started, but a FAILED proof emits the `(:DEFTHM …)` (at proof
  # START) with NO matching `(:QED)` — so `got_qed < got_defthm` means a proof
  # failed even though every theorem was *attempted*. (The old `got_defthm` vs
  # source-count check only catches a halt BEFORE a later defthm starts, not a
  # defthm that starts and then fails — which is the common case.) We also grep
  # ACL2's "proof attempt has failed" prose, which DOES survive :structured mode.
  # NOTE: this is a heuristic backstop — the load-bearing guard is downstream, in
  # buildDevelopment, which hard-fails on any :DEFTHM block lacking its :QED. The
  # proper positive signal (an explicit emit/proof-failed event) is a tracked
  # infra-revision item; see TODO.md.
  want_defthm=$(grep -ciE '\(defthmd?\b' "$INPUT_ABS" || true)
  got_defthm=$(grep -c '(:DEFTHM' "$OUTPUT" || true)
  got_qed=$(grep -c '(:QED' "$OUTPUT" || true)
  if grep -q ":STOP-LD\|\*\*\*\*\*\*\*\* FAILED\|proof attempt has failed" "$OUTPUT"; then
    echo "WARNING: $(basename "$INPUT") — ACL2 reported a FAILED/aborted event; log is INCOMPLETE." >&2
  elif [ "$got_qed" -lt "$got_defthm" ]; then
    echo "WARNING: $(basename "$INPUT") — $got_qed (:QED) for $got_defthm (:DEFTHM): a proof started but did NOT complete (no closing :QED). ACL2 FAILED a proof. Log is INCOMPLETE." >&2
  elif [ "$got_defthm" -lt "$want_defthm" ]; then
    echo "WARNING: $(basename "$INPUT") — logged $got_defthm of $want_defthm defthm proof(s); ACL2 likely FAILED/halted before a later event. Log is INCOMPLETE." >&2
  fi

  echo "$(basename "$INPUT"): $(wc -l < "$OUTPUT") lines, $got_qed/$got_defthm qed/defthm (source: $want_defthm) → $OUTPUT"
done
