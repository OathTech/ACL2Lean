#!/usr/bin/env bash
# Capture structured proof output from ACL2.
#
# Usage:
#   capture-proof-log.sh file.lisp              # single file
#   capture-proof-log.sh f1.lisp f2.lisp ...    # multiple files
#   OUTDIR=dir capture-proof-log.sh f1.lisp ... # logs into dir/ instead
#
# Output: file.proof-log alongside each input file, or in $OUTDIR if set.
# OUTDIR exists so that books sourced from the acl2/ SUBMODULE (the canonical
# upstream copies — we no longer duplicate them into acl2_samples/) get their
# logs captured into acl2_samples/ WITHOUT dirtying the submodule tree.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ACL2="${ACL2:-$SCRIPT_DIR/../acl2/saved_acl2}"
OUTDIR="${OUTDIR:-}"

if [ -n "$OUTDIR" ] && [ ! -d "$OUTDIR" ]; then
  echo "Error: OUTDIR=$OUTDIR is not a directory" >&2
  exit 1
fi

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
  if [ -n "$OUTDIR" ]; then
    OUTPUT="$OUTDIR/$(basename "${INPUT%.lisp}").proof-log"
  else
    OUTPUT="${INPUT_ABS%.lisp}.proof-log"
  fi

  if [ ! -f "$INPUT_ABS" ]; then
    echo "Error: $INPUT not found" >&2
    exit 1
  fi

  # emit-ground-zero-snapshots (fork, ld.lisp): after the book completes,
  # append the cited-closure ground-zero defun snapshots + rule statements
  # (external-knowledge design D3/D5) to the log's tail.
  printf '(set-raw-proof-format :structured)
(ld "%s")
(emit-ground-zero-snapshots state)
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
  # Count only UNCOMMENTED defthms in the source (a leading `;` comments the
  # form out — isort's perm-isort taught us this), and only :SOURCE :LOCAL
  # theorem events in the log: theorems arriving via include-book are
  # announced as `(:DEFTHM … :SOURCE :INCLUDE-BOOK)` with NO proof and NO
  # :QED (include skips proofs), so counting them against :QED is a false
  # alarm. Events line-wrap arbitrarily (`:SOURCE` and `:LOCAL` can land on
  # different lines), so normalize whitespace before counting. Note the log
  # count can legitimately EXCEED the source count (defequiv/defcong generate
  # theorems, e.g. PERM-IS-AN-EQUIVALENCE); only a SHORTFALL warns.
  want_defthm=$(grep -cE '^[^;]*\(defthmd?\b' "$INPUT_ABS" || true)
  # `|| true`: grep exits 1 on zero matches, and under pipefail that would
  # silently kill the whole run at the first book with no local defthms
  # (how-many.lisp is all defuns).
  got_defthm=$(tr -s ' \n' '  ' < "$OUTPUT" | { grep -o ':SOURCE :LOCAL' || true; } | wc -l | tr -d ' ')
  got_qed=$(grep -c '(:QED' "$OUTPUT" || true)
  if grep -q ":STOP-LD\|\*\*\*\*\*\*\*\* FAILED\|proof attempt has failed" "$OUTPUT"; then
    echo "WARNING: $(basename "$INPUT") — ACL2 reported a FAILED/aborted event; log is INCOMPLETE." >&2
  elif [ "$got_qed" -lt "$got_defthm" ]; then
    echo "WARNING: $(basename "$INPUT") — $got_qed (:QED) for $got_defthm (:DEFTHM): a proof started but did NOT complete (no closing :QED). ACL2 FAILED a proof. Log is INCOMPLETE." >&2
  elif [ "$got_defthm" -lt "$want_defthm" ]; then
    echo "WARNING: $(basename "$INPUT") — logged $got_defthm of $want_defthm defthm proof(s); ACL2 likely FAILED/halted before a later event. Log is INCOMPLETE." >&2
  fi

  # Hardening G2: provenance sidecar — bind this log to the fork commit and
  # image that produced it. check-log-provenance.sh (in `just ci`, static)
  # hard-fails when a corpus log's stamped commit is not the current
  # submodule HEAD — catching stale images and PARTIAL recaptures the moment
  # the fork moves. An ACL2 override outside a git checkout stamps
  # "unknown", which the checker rejects (fail-closed).
  {
    echo "acl2-commit: $(git -C "$(dirname "$ACL2")" rev-parse HEAD 2>/dev/null || echo unknown)"
    echo "image-mtime: $(stat -f %m "$ACL2" 2>/dev/null || stat -c %Y "$ACL2" 2>/dev/null || echo unknown)"
    echo "captured-at: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  } > "$OUTPUT.meta"

  echo "$(basename "$INPUT"): $(wc -l < "$OUTPUT") lines, $got_qed/$got_defthm qed/defthm (source: $want_defthm) → $OUTPUT"
done

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
