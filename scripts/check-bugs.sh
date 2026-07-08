#!/usr/bin/env bash
# Cross-check the canonical fidelity-bug index (docs/BUGS.md) against the
# self-enforcing differential corpus, so a logged bug can neither rot in prose
# nor be silently dropped. Enforced in `just ci`.
#
# Two directions:
#  (1) every `bug:BUG-NNN` tag in Tests/differential/corpus/*.lisp must name a
#      BUG that EXISTS in BUGS.md and is Status: open.
#  (2) every BUG in BUGS.md that is `Status: open` AND `Pinned-by: differential`
#      must have >= 1 live `bug:BUG-NNN` tag in the corpus.
# Bugs with `Pinned-by: none (...)` are exempt from (2) — they are logged but
# not yet mechanically pinnable (e.g. a builtin not wired into the interpreter).
#
# See docs/BUGS.md for the entry format and the robustness contract.
#
# No `-e`: we aggregate all violations and report them; guard `cd` explicitly.
set -uo pipefail
cd "$(dirname "$0")/.." || { echo "FATAL: cannot cd to repo root" >&2; exit 2; }

# Paths are overridable (BUGS_MD / CORPUS_DIR) so the checker can be exercised
# against throwaway copies in tests without touching the real files.
BUGS="${BUGS_MD:-docs/BUGS.md}"
CORPUS_GLOB="${CORPUS_DIR:-Tests/differential/corpus}"

[[ -f "$BUGS" ]] || { echo "FATAL: $BUGS not found" >&2; exit 2; }

fail=0

# ── Parse BUGS.md: for each BUG-NNN, capture Status and Pinned-by. ──
# A bug's block runs from its `## BUG-NNN` header to the next `##`/EOF; the
# Status:/Pinned-by: lines are the first such lines in that block.
declare -A bug_status bug_pin
cur=""
while IFS= read -r line; do
  case "$line" in
    "## BUG-"*)
      # Real bug headers are `## BUG-NNN …` with NNN numeric. The format-doc
      # example header `## BUG-NNN` (literal) has no digits — skip it (and any
      # other non-numeric `## BUG-` prose) by only setting `cur` on a match.
      cur="$(printf '%s' "$line" | grep -oE 'BUG-[0-9]+' || true)"
      if [[ -n "$cur" ]]; then bug_status["$cur"]=""; bug_pin["$cur"]=""; fi ;;
    "Status:"*)
      [[ -n "$cur" && -z "${bug_status[$cur]}" ]] && \
        bug_status["$cur"]="$(printf '%s' "$line" | sed -E 's/^Status:[[:space:]]*//' | tr -d ' ')" ;;
    "Pinned-by:"*)
      [[ -n "$cur" && -z "${bug_pin[$cur]}" ]] && \
        bug_pin["$cur"]="$(printf '%s' "$line" | sed -E 's/^Pinned-by:[[:space:]]*//')" ;;
  esac
done < "$BUGS"

# ── Collect the bug ids TAGGED in the corpus (bug:BUG-NNN in ;@ lines). ──
declare -A corpus_tag
while IFS= read -r id; do
  [[ -n "$id" ]] && corpus_tag["$id"]=1
done < <(grep -rhoE 'bug:BUG-[0-9]+' "$CORPUS_GLOB" 2>/dev/null | sed 's/^bug://' | sort -u)

# ── Direction 1: every corpus tag names an existing OPEN bug. ──
for id in "${!corpus_tag[@]}"; do
  if [[ -z "${bug_status[$id]+x}" ]]; then
    echo "FAIL: corpus tags $id but $BUGS has no such entry"; fail=1
  elif [[ "${bug_status[$id]}" != "open" ]]; then
    echo "FAIL: corpus tags $id but $BUGS marks it '${bug_status[$id]}' (expected open)"; fail=1
  fi
done

# ── Direction 2: every open, differential-pinned bug has >= 1 corpus tag. ──
for id in "${!bug_status[@]}"; do
  [[ "${bug_status[$id]}" == "open" ]] || continue
  case "${bug_pin[$id]}" in
    differential)
      if [[ -z "${corpus_tag[$id]+x}" ]]; then
        echo "FAIL: $id is open + Pinned-by:differential but has NO 'bug:$id' tag in $CORPUS_GLOB/"
        echo "      (add the tag to its known-bug entry, or change Pinned-by if it can't be pinned)"
        fail=1
      fi ;;
    none*|"") : ;;  # logged-but-unpinned (exempt) or blank (flagged below)
    *) echo "FAIL: $id has unrecognized Pinned-by '${bug_pin[$id]}' (use 'differential' or 'none (<reason>)')"; fail=1 ;;
  esac
  [[ -z "${bug_pin[$id]}" ]] && { echo "FAIL: $id ($([[ ${bug_status[$id]} = open ]] && echo open)) has no Pinned-by field"; fail=1; }
done

n_bugs=${#bug_status[@]}; n_tags=${#corpus_tag[@]}
echo "checked $n_bugs bug entries in $BUGS against $n_tags tagged id(s) in the corpus"
if [[ "$fail" -eq 0 ]]; then
  echo "bug index and differential corpus are consistent."
else
  echo ""
  echo "The canonical bug index ($BUGS) and the differential corpus are OUT OF SYNC."
  echo "Fix the entries above so no logged bug can be lost. See docs/BUGS.md."
  exit 1
fi
