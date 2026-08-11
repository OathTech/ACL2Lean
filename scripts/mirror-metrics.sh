#!/usr/bin/env bash
# mirror-metrics: the ruled success metrics (2026-08-11) — MEASURED,
# never asserted.
#   1. Kept-condition census by class, from the driver-coverage golden
#      (the headline metric — computed by the driver from the proof
#      term, so Lean-side effort cannot move it).
#   2. Hand lines per catalog native (the industrialization tell —
#      must FALL as books land).
# Written invariant (ruled): no constant defined in the mirror layer
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

echo
echo "== hand lines per catalog native =="
# The sorting book's hand content is the six layer modules of
# ACL2Lean/Imported/Sorting/ (split 2026-08-11, the demo build); the
# facade ACL2Lean/Imported/Sorting.lean is imports + prose, not hand
# content, so it is deliberately NOT counted.
hand_files=(
  ACL2Lean/Imported/Sorting/Sims.lean
  ACL2Lean/Imported/Sorting/Iso.lean
  ACL2Lean/Imported/Sorting/IsoAdmission.lean
  ACL2Lean/Imported/Sorting/Decode.lean
  ACL2Lean/Imported/Sorting/DecodeSorts.lean
  ACL2Lean/Imported/Sorting/Debt.lean
  ACL2Lean/Imported/SortingBsort.lean
  ACL2Lean/Imported/SortingConvertPerm.lean
  ACL2Lean/Imported/Perm.lean
  ACL2Lean/Imported/EquisortWitness.lean
  ACL2Lean/Imported/SimpleWorld.lean
  ACL2Lean/Imported/AppAssoc.lean
  ACL2Lean/Imported/GzPrelude.lean
)
hand_lines=$(cat "${hand_files[@]}" | wc -l)
catalog=ACL2Lean/Imported/Mirrors/Catalog.lean
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
