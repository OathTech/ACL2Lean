#!/usr/bin/env bash
# Mapping-arc gate: the pattern map (docs/notes/2026-07-22_pattern-map.md)
# is a GATED ARTIFACT, not prose that can rot (the check-bugs.sh pattern,
# MDD-ratified 2026-07-23). Three fail-closed checks:
#
#   1. BIDIRECTIONAL book<->map: every book source in
#      acl2_samples/pattern-tests/*.lisp is mentioned in the map, and every
#      pattern-tests book the map mentions exists as a source. A book can
#      neither be added silently nor claimed falsely.
#   2. LOGS PRESENT: every book has a captured .proof-log alongside it
#      (logs are gitignored + regenerated; a missing one means the capture
#      is stale/incomplete — run scripts/capture-proof-log.sh, never skip).
#   3. PIN SIGNATURES: each pinned claim in the map has its grep-able
#      signature in the actual captured log — characterization drift and
#      log-regeneration drift both fail loudly here.
#
# Exit: 0 = all green; 1 = any failure (each printed).
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
MAP="$ROOT/docs/notes/2026-07-22_pattern-map.md"
DIR="$ROOT/acl2_samples/pattern-tests"
fail=0
err() { echo "check-pattern-map: FAIL — $*" >&2; fail=1; }

[ -f "$MAP" ] || { err "map file missing: $MAP"; exit 1; }
[ -d "$DIR" ] || { err "pattern-tests dir missing: $DIR"; exit 1; }

# --- 1. bidirectional book<->map ---------------------------------------
for src in "$DIR"/*.lisp; do
  b="$(basename "$src" .lisp)"
  grep -q "$b" "$MAP" || err "book $b.lisp is not mentioned in the map"
done
# books the map names (pattern-tests namespace: p1-* and cov-* tokens)
while read -r name; do
  [ -f "$DIR/$name.lisp" ] || err "map mentions $name but $name.lisp does not exist"
done < <(grep -oE '\b(p1|cov)-[a-z0-9-]*[a-z0-9]' "$MAP" \
           | sed 's/\.lisp$//' | sed 's/\.proof-log$//' | sort -u)

# --- 2. logs present ----------------------------------------------------
for src in "$DIR"/*.lisp; do
  b="$(basename "$src" .lisp)"
  [ -f "$DIR/$b.proof-log" ] \
    || err "book $b has no captured proof-log (stale capture — run scripts/capture-proof-log.sh $src)"
done

# --- 3. pin signatures --------------------------------------------------
# sig <book> <min-count> <fixed-string>   — grep -F count >= min
sig() {
  local b="$1" min="$2" pat="$3" log="$DIR/$1.proof-log" n
  [ -f "$log" ] || return 0   # already reported by check 2
  n=$(grep -cF -- "$pat" "$log" || true)
  [ "$n" -ge "$min" ] \
    || err "pin drift: $b.proof-log has $n < $min occurrence(s) of '$pat'"
}
# nosig <book> <fixed-string> — signature must be ABSENT (halt-family books)
nosig() {
  local b="$1" pat="$2" log="$DIR/$1.proof-log"
  [ -f "$log" ] || return 0
  if grep -qF -- "$pat" "$log"; then
    err "pin drift: $b.proof-log unexpectedly contains '$pat' (halt pin resolved? update the map)"
  fi
}

# P1 circle
sig p1-swap-descend    1 "(IF (CONSP X) (ATOM Y) (ATOM X))"
sig p1-swap-double-neg 1 "(NOT (NOT"
sig p1-or-opt-probe    1 ":UNREWRITTEN-TEST"
# S1-corrected books (2026-07-23): all six former "halt" surfaces capture
sig cov-complex             2 "(:QED)"
sig cov-number-literals     4 "(:QED)"
sig cov-type-set-inverter   1 "(:QED)"
sig cov-quoted-constant-rule 2 "(:QED)"
sig cov-defconst-local      1 ":SOURCE :LOCAL"
sig cov-defconst-local      2 "(:QED)"
sig cov-defattach           4 "(:QED)"
# crown artifacts
sig cov-force-round   1 "(:QED :FORCED 1)"
sig cov-force-round   1 "[1]Goal"
sig cov-force-round   1 "(:FORCING-ROUND :ROUND 1"
nosig cov-force-round "Modulo the following forced"
sig cov-cong-consume  1 ":EQUIV SAME-LEN2"
sig cov-trivial-drop2 1 ":SCHEME-DROPPED ((("
sig cov-linear-pot    1 ":FAKE-RUNE-FOR-LINEAR"
sig cov-wf-relation   1 ":WFREL MY-LT"
sig cov-by-hint       1 "APPLY-TOP-HINTS-CLAUSE"
sig cov-typeset-decode 3 ":TYPESET"
sig cov-backchain-limit 1 "(BFN X) '0 (0))"
sig cov-let-lambda    1 "(LAMBDA (Y)"
sig cov-mv-let        1 "(LAMBDA (MV)"
sig cov-verify-guards 1 "(:VERIFY-GUARDS :NAMES (GSUM)"
sig cov-verify-guards 2 "(:QED)"
# rewrite-cache: ONE recorded unfold for two occurrences
n=$(grep -cF "RUNE (:DEFINITION RC2)" "$DIR/cov-rewrite-cache.proof-log" 2>/dev/null || echo 0)
if [ "$n" != "1" ]; then
  err "pin drift: cov-rewrite-cache expects exactly 1 RC2 unfold, found $n"
fi

if [ "$fail" -eq 0 ]; then
  nbooks=$(find "$DIR" -name '*.lisp' | wc -l | tr -d ' ')
  echo "check-pattern-map: OK ($nbooks books, bidirectional + logs + signatures)"
fi
exit "$fail"
