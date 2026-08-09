#!/usr/bin/env bash
# GZ AGREEMENT-LEMMA gate (Phase 3 close-out item 2; audit 2026-08-08
# outside F13). A BUILTIN-NAMED ground-zero snapshot defun is excluded
# from the World (no-shadow), so `evalOpt` dispatches it to the
# `callBuiltin` primitive — the emitted ACL2 definition and our
# primitive can silently diverge unless a kernel-checked AGREEMENT
# LEMMA (`gz_def_<fn>`, Replay/Lemmas/Derived.lean) relates them.
#
# This gate enforces: every builtin-named `(:DEFUN <fn> …
# :SOURCE :GROUND-ZERO)` across the captured corpus has either
#  (a) a `gz_def_<fn>` theorem in Derived.lean, or
#  (b) an explicit FLAG below, with a justification.
# Flags are themselves checked for rot: a flagged name that gains a
# lemma or stops being emitted fails the gate.
#
# No `-e`: aggregate all violations. Static (no build needed); in `just ci`.
set -uo pipefail
cd "$(dirname "$0")/.." || { echo "FATAL: cannot cd to repo root" >&2; exit 2; }

DERIVED="${DERIVED_OVERRIDE:-ACL2Lean/Replay/Lemmas/Derived.lean}"
EVALOPT="ACL2Lean/EvalOpt.lean"
[[ -f "$DERIVED" ]] || { echo "FATAL: $DERIVED not found" >&2; exit 2; }
[[ -f "$EVALOPT" ]] || { echo "FATAL: $EVALOPT not found" >&2; exit 2; }

# ── FLAGGED entries: no pure-`Logic` value composition exists (the body
#    cites a non-builtin fn), so the family's lemma shape cannot state
#    them; each carries its alternative fidelity anchor. ──
#   LEXORDER — body cites ALPHORDER (a World fn); fidelity rests on the
#              LexorderOrder theorems + the differential corpus.
#   EXPT     — body cites ZIP (a World fn); fidelity rests on the
#              differential corpus (BUG-021 pin).
FLAGGED=("LEXORDER" "EXPT")

fail=0

# ── The builtin name list, parsed from EvalOpt.lean's `builtinNames`. ──
builtins=$(sed -n '/^def builtinNames : List String :=/,/^$/p' "$EVALOPT" \
  | grep -o '"[^"]*"' | tr -d '"')
[[ -n "$builtins" ]] || { echo "FATAL: could not parse builtinNames" >&2; exit 2; }

# ── Builtin-named gz snapshot defuns across the captured corpus. ──
gz_names=$(grep -rhoE '\(:DEFUN [A-Z0-9<>=/+*-]+ [^\n]*:SOURCE :GROUND-ZERO' \
    acl2_samples --include='*.proof-log' 2>/dev/null \
  | sed -E 's/^\(:DEFUN ([A-Z0-9<>=/+*-]+) .*/\1/' | sort -u)
[[ -n "$gz_names" ]] || { echo "FATAL: no ground-zero snapshots found" >&2; exit 2; }

# name → lemma suffix: lower-case, '-' → '_'
lemma_suffix() { echo "$1" | tr 'A-Z-' 'a-z_'; }

flagged_seen=()
while IFS= read -r nm; do
  # only builtin-named snapshots are in scope
  grep -qxF "$nm" <<<"$builtins" || continue
  suffix=$(lemma_suffix "$nm")
  has_lemma=0
  grep -qE "^theorem gz_def_${suffix} " "$DERIVED" && has_lemma=1
  is_flagged=0
  for f in "${FLAGGED[@]}"; do [[ "$f" == "$nm" ]] && is_flagged=1; done
  if [[ $is_flagged -eq 1 ]]; then
    flagged_seen+=("$nm")
    if [[ $has_lemma -eq 1 ]]; then
      echo "FAIL: $nm is FLAGGED but now HAS gz_def_${suffix} — remove the flag" >&2
      fail=1
    fi
  elif [[ $has_lemma -eq 0 ]]; then
    echo "FAIL: builtin-named ground-zero defun $nm has no agreement \
lemma gz_def_${suffix} in $DERIVED and is not flagged" >&2
    fail=1
  fi
done <<<"$gz_names"

# ── Flag rot: every FLAGGED entry must still be an emitted builtin-named
#    gz snapshot. ──
for f in "${FLAGGED[@]}"; do
  seen=0
  for s in "${flagged_seen[@]:-}"; do [[ "$s" == "$f" ]] && seen=1; done
  if [[ $seen -eq 0 ]]; then
    echo "FAIL: FLAGGED entry $f is no longer an emitted builtin-named \
ground-zero snapshot — remove the stale flag" >&2
    fail=1
  fi
done

if [[ $fail -eq 0 ]]; then
  echo "check-gz-agreement: OK (every builtin-named ground-zero snapshot \
has an agreement lemma or an explicit flag)"
fi
exit $fail
