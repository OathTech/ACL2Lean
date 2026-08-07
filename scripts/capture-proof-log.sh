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
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
# shellcheck source=lib-log-provenance.sh
. "$SCRIPT_DIR/lib-log-provenance.sh"
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

# PARALLEL capture (perf arc item 2, 2026-08-07): the per-book runs are
# independent single-threaded ACL2 processes writing DISJOINT outputs
# (log + sidecar per book), so with >1 input we fan out via xargs -P.
# Each worker re-invokes this script on ONE input with CAPTURE_WORKER=1
# (inheriting ACL2/OUTDIR); xargs exits nonzero if ANY worker fails
# (fail-closed, no partial-success masking). The include_str consumer
# invalidation below runs ONCE, in the parent, after all workers.
# Audit A1 (2026-08-07): invalidate the coverage artifacts BEFORE any
# capture runs — a PARTIAL parallel capture (one book fails after others
# promoted) must never leave cached-green coverage modules. Workers skip
# (the parent has already done it).
if [ -z "${CAPTURE_WORKER:-}" ]; then
  "$SCRIPT_DIR/invalidate-coverage.sh" || true
fi

if [ -z "${CAPTURE_WORKER:-}" ] && [ $# -gt 1 ]; then
  printf '%s\n' "$@" \
    | ACL2="$ACL2" OUTDIR="$OUTDIR" CAPTURE_WORKER=1 \
      xargs -P "$(nproc)" -n 1 "$0" \
    || { echo "Error: one or more parallel captures FAILED (see above)." >&2
         exit 1; }
  set -- ""  # skip the sequential loop; fall through to invalidation
fi

for INPUT in "$@"; do
  [ -n "$INPUT" ] || continue
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

  # --no-sysinit keeps ACL2 hermetic: /etc/sbclrc must not inject lisp into the
  # capture run (and it is unreadable inside the nono sandbox).
  # emit-ground-zero-snapshots (fork, ld.lisp): after the book completes,
  # append the cited-closure ground-zero defun snapshots + rule statements
  # (external-knowledge design D3/D5) to the log's tail.
  # ATOMIC output (capstone-demo arc Phase 0, review-1 P0-2): write to a
  # temp path; the real $OUTPUT and its sidecar appear ONLY on a verified
  # complete capture. A failed run leaves any previous artifacts
  # untouched (their sidecar hashes still bind them to the source that
  # produced them).
  # emit-capture-manifest (fork-batch item 8): the post-ld manifest +
  # explicit :STATUS :COMPLETE end record — the LAST event of a healthy
  # capture; the completeness check below requires it.
  printf '(set-raw-proof-format :structured)
(ld "%s")
(emit-ground-zero-snapshots state)
(emit-capture-manifest state)
(good-bye)
' "$INPUT_ABS" | "$ACL2" --no-sysinit > "$OUTPUT.tmp" 2>&1

  # Failure detection — FATAL (capstone-demo arc Phase 0, review-1 P0-2;
  # the pre-2026-08-06 version WARNED and exited 0, so a failed/truncated
  # ACL2 run could be accepted as producer output). The completeness
  # logic (QED-per-DEFTHM primary signal, source-count halt detection,
  # FAILED/HARD-ERROR prose) lives in lib-log-provenance.sh, shared with
  # check-log-provenance.sh so ci re-verifies the same invariant
  # statically. The proper positive signal (an explicit emit/proof-failed
  # event + post-ld manifest) is fork-batch item 8.
  if ! check_capture_complete "$INPUT_ABS" "$OUTPUT.tmp" >&2; then
    echo "Error: $(basename "$INPUT") capture INCOMPLETE — no log/sidecar written; ACL2 output kept at $OUTPUT.tmp for diagnosis." >&2
    exit 1
  fi
  # UNCONDITIONAL at capture (fork-batch item 8): the image emits
  # (:CAPTURE-END ... :STATUS :COMPLETE) as the last event — its absence
  # means truncation ANYWHERE, including before any countable signal.
  if ! tr -s ' \n' '  ' < "$OUTPUT.tmp" | grep -q '(:CAPTURE-END .*:STATUS :COMPLETE'; then
    echo "Error: $(basename "$INPUT") capture has NO (:CAPTURE-END :STATUS :COMPLETE) end record — truncated or pre-item-8 image; no log/sidecar written (output kept at $OUTPUT.tmp)." >&2
    exit 1
  fi

  # Include closure computed OUTSIDE the sidecar subshell: a plain
  # assignment propagates include_closure's fail-closed error under
  # set -e, where a process substitution would swallow it.
  closure="$(include_closure "$INPUT_ABS" "|$INPUT_ABS|")"

  # Hardening G2: provenance sidecar — bind this log to the fork commit and
  # image that produced it. check-log-provenance.sh (in `just ci`, static)
  # hard-fails when a corpus log's stamped commit is not the current
  # submodule HEAD — catching stale images and PARTIAL recaptures the moment
  # the fork moves. An ACL2 override outside a git checkout stamps
  # "unknown", which the checker rejects (fail-closed).
  # DIRTY-TREE stamping (S2 audit F5, 2026-07-25): rev-parse HEAD names a
  # commit, not the TREE the image was built from — a capture over
  # uncommitted fork edits used to stamp a clean hash the log's content
  # doesn't match (incident: the LAMBDA-BODY logs stamped a90dd106). A dirty
  # submodule now stamps "<hash>-dirty", which the checker rejects.
  {
    acl2dir="$(dirname "$ACL2")"
    commit="$(git -C "$acl2dir" rev-parse HEAD 2>/dev/null || echo unknown)"
    if [ "$commit" != "unknown" ] && [ -n "$(git -C "$acl2dir" status --porcelain 2>/dev/null)" ]; then
      commit="$commit-dirty"
    fi
    echo "acl2-commit: $commit"
    # GNU stat first (fresh-verify N4: BSD-form `stat -f %m` on GNU prints a
    # filesystem dump to stdout AND fails, so the fallback appended to the
    # garbage — every sidecar carried a 6-line value). GNU `-c` on BSD fails
    # cleanly with no stdout, so this order is safe both ways.
    echo "image-mtime: $(stat -c %Y "$ACL2" 2>/dev/null || stat -f %m "$ACL2" 2>/dev/null || echo unknown)"
    echo "captured-at: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
    # SOURCE provenance (capstone-demo arc Phase 0, review-1 P0-1): bind
    # the log to the exact source text and its transitive include-book
    # closure. check-log-provenance.sh recomputes these against the
    # CURRENT tree — an edited book paired with an old log now fails the
    # local gate instead of certifying a proof about the old text.
    echo "source-path: $(repo_rel "$INPUT_ABS")"
    echo "source-sha256: $(sha256_of "$INPUT_ABS")"
    while IFS= read -r inc; do
      [ -n "$inc" ] || continue
      case "$inc" in
        *" SYSTEM") incf="${inc% SYSTEM}"
          echo "include: $(repo_rel "$incf") $(sha256_of "$incf") system";;
        *) echo "include: $(repo_rel "$inc") $(sha256_of "$inc")";;
      esac
    done <<< "$closure"
    # Audit A2 (2026-08-07): bind the LOG'S OWN BYTES — any
    # out-of-band change to a promoted log (editor, cp, restore)
    # fails check-log-provenance in ci.
    echo "log-sha256: $(sha256_of "$OUTPUT.tmp")"
    echo "source-provenance: captured"
  } > "$OUTPUT.meta.tmp"

  # Atomic promote: log first, then sidecar (a crash between the two
  # leaves a log whose OLD sidecar hashes fail the checker — fail-closed).
  mv "$OUTPUT.tmp" "$OUTPUT"
  mv "$OUTPUT.meta.tmp" "$OUTPUT.meta"

  echo "$(basename "$INPUT"): $(wc -l < "$OUTPUT") lines, $(count_log_qeds "$OUTPUT")/$(count_log_local_defthms "$OUTPUT") qed/defthm (source: $(count_source_defthms "$INPUT_ABS")) → $OUTPUT"
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
# Workers skip the invalidation — the parent runs it ONCE after the fan-out.
if [ -n "${CAPTURE_WORKER:-}" ]; then exit 0; fi
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
# (Coverage invalidation now runs BEFORE capture — audit A1; see
# scripts/invalidate-coverage.sh, the single source of the rm set.)
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
