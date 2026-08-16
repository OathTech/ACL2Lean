#!/usr/bin/env bash
# waypoint-metrics: the ruled success metrics (2026-08-11) — MEASURED,
# never asserted.
#   1. Kept-condition census by class, from the driver-coverage golden
#      (the headline metric — computed by the driver from the proof
#      term, so Lean-side effort cannot move it).
#   2. Hand lines per catalog native (the industrialization tell —
#      must FALL as books land).
# Written invariant (ruled): no constant defined in the waypoint layer
# may be injected into the coverage sweep (enforced structurally:
# prepareUseFi has no injection parameter since 2026-08-11).
set -euo pipefail
cd "$(dirname "$0")/.."

golden=Tests/driver-coverage.golden

echo "== kept-condition census (from ${golden}) =="
head -1 "$golden"
# bucket every kept condition in every cond[...] block by class prefix
grep -o 'cond\[[^]]*\]' "$golden" \
  | sed -e 's/^cond\[//' -e 's/\]$//' -e 's/, /\n/g' \
  | sed -e 's/:.*$//' \
  | sort | uniq -c | sort -rn \
  | awk '{printf "  %-12s %s\n", $2":", $1}'

# THE TWO SURFACES (reconciliation, 2026-08-16 audit A3-T2-5). The census
# above buckets EVERY cond[...] in the file, which mixes two different
# things:
#   ROW conditions            — the kept hypotheses of the replayed row.
#                               This is what the golden's header counts
#                               (Tests/Coverage/Harness.lean strips the
#                               "  [DISCHARGE:" tail before it looks for
#                               " cond["), and it is the metric.
#   DISCHARGE-bracket conds   — the telescopes of the standalone,
#                               INFORMATIONAL DP probe appended to a row.
#                               Ruled probe-structural; they are not row
#                               qualifications and never gate anything.
# (both counts may legitimately be ZERO — grep's exit 1 must not abort
#  the script under `set -e`/pipefail)
all_blocks=$(grep -o 'cond\[' "$golden" | wc -l | tr -d ' ' || true)
row_blocks=$(sed 's/  \[DISCHARGE:.*$//' "$golden" \
  | { grep -o 'cond\[' || true; } | wc -l | tr -d ' ')
echo "  --"
echo "  cond[...] blocks on ROWS (the metric):        ${row_blocks}"
echo "  cond[...] blocks inside [DISCHARGE: …]:       $((all_blocks - row_blocks))  (informational DP-probe telescopes)"

echo
echo "== hand lines per catalog native =="
hand_files=(
  ACL2Lean/Imported/Sorting.lean
  ACL2Lean/Imported/SortingBsort.lean
  ACL2Lean/Imported/SortingConvertPerm.lean
  ACL2Lean/Imported/Perm.lean
  ACL2Lean/Imported/EquisortWitness.lean
  ACL2Lean/Imported/SimpleWorld.lean
  ACL2Lean/Imported/AppAssoc.lean
  ACL2Lean/Imported/RevAcc.lean
  # (GzPrelude.lean was deleted at T1+2 sprint P4b — its five statements
  #  moved down to Replay/GzRules.lean; listing it here aborted the whole
  #  script under `set -e` from 2026-08-15 until the 2026-08-16 audit.)
)
hand_lines=$(cat "${hand_files[@]}" | wc -l)
catalog=ACL2Lean/Imported/Waypoints/Catalog.lean
# entry statuses are followed by a double-backtick decl ref — prose
# mentions of the status names never are
n_native=$(grep -c '\.native ``' "$catalog" || true)
n_sorried=$(grep -c '\.nativeSorried ``' "$catalog" || true)
total=$((n_native + n_sorried))
if [ "$total" -eq 0 ]; then
  echo "  ERROR: zero catalog natives counted — the entry regex rotted" >&2
  exit 1
fi
echo "  hand lines (per-book Imported files): ${hand_lines}"
echo "  catalog natives: ${n_native} .native + ${n_sorried} .nativeSorried = ${total}"
echo "  HAND LINES PER NATIVE: $((hand_lines / total))"

echo
echo "== decode coverage (hreplayed-usage gate's scan surface) =="
# REPORTED, not a floor (gate-cruft review 2026-08-11, R2): the gate
# itself checks each decode's content; the count of decodes it sees is a
# watched number here instead of a build-failing floor in Catalog.lean.
n_decode=$(cat "${hand_files[@]}" | grep -c '_of_replayed (' || true)
echo "  decode theorems (_of_replayed) in the per-book Imported files: ${n_decode}"
