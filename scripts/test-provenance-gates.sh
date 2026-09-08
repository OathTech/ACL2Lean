#!/usr/bin/env bash
# NEGATIVE tests for the provenance/completeness gates (capstone-demo arc
# Phase 0 exit criterion, review-1 P0-1/P0-2): a source-edited book and a
# truncated log must FAIL the local gate. Runs in `just ci`. Fixtures are
# built under the project .tmp (the sandbox TMPDIR) from a real corpus
# log, and the checker is pointed at them via SCAN_ROOT.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CHECK="$SCRIPT_DIR/check-log-provenance.sh"
FIX="$ROOT/.tmp/provenance-gate-tests"

# A small real log with a waterfall proof and a sibling source.
REAL_LOG="$ROOT/acl2_samples/pattern-tests/cov-defun-sk.proof-log"
REAL_SRC="$ROOT/acl2_samples/pattern-tests/cov-defun-sk.lisp"

rm -rf "$FIX"
mkdir -p "$FIX"

fails=0

# expect_fail <name> <expected-substring> — the checker must exit nonzero
# AND name the expected failure class.
expect_fail() {
  local name="$1" want="$2" out
  if out="$(SCAN_ROOT="$FIX/$name" bash "$CHECK" 2>&1)"; then
    echo "NEGATIVE-TEST FAIL: $name — checker PASSED but must fail" >&2
    fails=1
  elif ! echo "$out" | grep -q "$want"; then
    echo "NEGATIVE-TEST FAIL: $name — checker failed but without '$want':" >&2
    echo "$out" | tail -3 >&2
    fails=1
  else
    echo "  ok (fails closed): $name → $want"
  fi
}

mk_case() { mkdir -p "$FIX/$1"; cp "$REAL_LOG" "$REAL_LOG.meta" "$FIX/$1/"; }

# 1. SOURCE-DRIFT: the sidecar's source hash no longer matches the tree —
#    i.e. the book was edited after capture. Point the fixture sidecar at
#    a fixture source whose content differs from the stamped hash.
mk_case source-drift
cp "$REAL_SRC" "$FIX/source-drift/edited.lisp"
echo ";; post-capture edit" >> "$FIX/source-drift/edited.lisp"
sed -i "s|^source-path: .*|source-path: .tmp/provenance-gate-tests/source-drift/edited.lisp|" \
  "$FIX/source-drift/cov-defun-sk.proof-log.meta"
expect_fail source-drift "SOURCE-DRIFT"

# 2. TRUNCATED: cut the log after the last proof's first (:STEP but
#    before its (:QED — the pairing walk must catch the open waterfall.
#    (The banner survives at the top, so only completeness fires.)
mk_case truncated
lastqed="$(grep -n '(:QED' "$FIX/truncated/cov-defun-sk.proof-log" | tail -1 | cut -d: -f1)"
head -n "$((lastqed - 1))" "$REAL_LOG" > "$FIX/truncated/cov-defun-sk.proof-log"
sed -i "s|^source-sha256: .*|source-sha256: $(sha256sum "$REAL_SRC" | cut -d' ' -f1)|" \
  "$FIX/truncated/cov-defun-sk.proof-log.meta"
expect_fail truncated "TRUNCATED"

# 3. NO-SOURCE-PROVENANCE: a pre-2026-08-06 sidecar (no source fields)
#    must be rejected, not skipped.
mk_case no-provenance
sed -i '/^source-provenance: /d; /^source-path: /d; /^source-sha256: /d; /^include: /d' \
  "$FIX/no-provenance/cov-defun-sk.proof-log.meta"
expect_fail no-provenance "NO-SOURCE-PROVENANCE"

# 4. NO-END-RECORD (audit 2026-08-07 M1 — the class the conditional
#    rung missed): strip (:CAPTURE-END ...); the ci-side check must now
#    fail UNCONDITIONALLY.
mk_case no-end-record
grep -v '(:CAPTURE-END' "$REAL_LOG" > "$FIX/no-end-record/cov-defun-sk.proof-log"
expect_fail no-end-record "CAPTURE-END"

# 5. Control: an untouched copy must PASS (guards against the checker
#    failing for fixture-environment reasons, which would make tests 1-3
#    vacuous).
mk_case control
if ! SCAN_ROOT="$FIX/control" bash "$CHECK" > /dev/null 2>&1; then
  echo "NEGATIVE-TEST FAIL: control — untouched fixture must PASS" >&2
  SCAN_ROOT="$FIX/control" bash "$CHECK" 2>&1 | tail -3 >&2
  fails=1
else
  echo "  ok (control passes): untouched fixture"
fi

# Explicit source-prefix scope must survive provenance round trips. The
# positive record comes from real ACL2's LD filter, never a truncated log.
scope_log="$ROOT/acl2_samples/ns1/floor.proof-log"
for name in scope-control scope-missing scope-wrong; do
  mkdir -p "$FIX/$name"
  cp "$scope_log" "$scope_log.meta" "$FIX/$name/"
done
if ! SCAN_ROOT="$FIX/scope-control" bash "$CHECK"; then
  echo "NEGATIVE-TEST FAIL: genuine scoped capture must pass" >&2
  fails=1
fi
sed -i '/^capture-through: /d' "$FIX/scope-missing/floor.proof-log.meta"
expect_fail scope-missing "TRUNCATED"
sed -i 's/^capture-through: .*/capture-through: FLOOR-BOUND-HACK-ERIC/' \
  "$FIX/scope-wrong/floor.proof-log.meta"
expect_fail scope-wrong "capture-through"

# Bootstrap captures must retain their source-initialization receipt. Both
# fixtures derive from a genuine original proof; only the negative sidecar
# is changed. This catches an ordinary copy/partial-capture mistake.
bootstrap_log="$ROOT/acl2_samples/ns1/bootstrap/reciprocal-default.proof-log"
for name in bootstrap-control bootstrap-no-receipt; do
  mkdir -p "$FIX/$name"
  cp "$bootstrap_log" "$bootstrap_log.meta" "$FIX/$name/"
done
if ! SCAN_ROOT="$FIX/bootstrap-control" bash "$CHECK"; then
  echo "NEGATIVE-TEST FAIL: genuine bootstrap capture must pass" >&2
  fails=1
fi
sed -i '/^bootstrap-receipt: /d' "$FIX/bootstrap-no-receipt/reciprocal-default.proof-log.meta"
expect_fail bootstrap-no-receipt "BOOTSTRAP-PROVENANCE"

# NS1 capture-data regression: a real emitted quoted diagnostic/NUL must
# pass completeness, while an injected actual diagnostic line must fail.
# Only the negative artifact is mutated; positive input is a real capture.
# shellcheck source=lib-log-provenance.sh
. "$SCRIPT_DIR/lib-log-provenance.sh"
data_log="$ROOT/acl2_samples/pattern-tests/cov-quoted-snapshot.proof-log"
data_src="$ROOT/acl2_samples/pattern-tests/cov-quoted-snapshot.lisp"
if ! check_capture_complete "$data_src" "$data_log"; then
  echo "NEGATIVE-TEST FAIL: actual quoted diagnostic/NUL capture must pass" >&2
  fails=1
fi
cp "$data_log" "$FIX/actual-error.proof-log"
printf '\nHARD ACL2 ERROR in TEST: actual diagnostic\n' >> "$FIX/actual-error.proof-log"
if check_capture_complete "$data_src" "$FIX/actual-error.proof-log" > "$FIX/actual-error.out"; then
  echo "NEGATIVE-TEST FAIL: an actual diagnostic line must fail" >&2
  fails=1
elif ! grep -q 'FAILED/aborted/HARD-ERROR' "$FIX/actual-error.out"; then
  echo "NEGATIVE-TEST FAIL: actual diagnostic rejected for the wrong reason" >&2
  fails=1
else
  echo "  ok (fails closed): actual diagnostic; real quoted data passes"
fi

if [ "$fails" -ne 0 ]; then
  echo "test-provenance-gates: FAILED — fixtures kept at $FIX for diagnosis" >&2
  exit 1
fi
rm -rf "$FIX"
echo "test-provenance-gates: all gates fail closed."
