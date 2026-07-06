#!/usr/bin/env bash
# Guard for the ACL2 instrumentation tagging convention
# (docs/notes/2026-06-09_acl2-tagging-survey.md / CLAUDE.md):
#   - every fork insertion carries a tag `; TRACE-LOG[<ns>/<label>]:`, ns in {emit,suppress,infra}
#   - no bare `; TRACE-LOG:` (old form)
#   - round-trip: every emitted rewrite-step `:origin '<sym>` has a matching TRACE-LOG[emit/<sym>]
# Run from repo root:  bash scripts/check-acl2-tags.sh   (exit !=0 on any violation)
set -uo pipefail
cd "$(dirname "$0")/.."
ACL2=acl2
fail=0

# 1. No bare `; TRACE-LOG:` (TRACE-LOG followed by ':' rather than '[').
bare=$(grep -rnE "; *TRACE-LOG:" "$ACL2"/*.lisp 2>/dev/null || true)
if [ -n "$bare" ]; then echo "FAIL: bare '; TRACE-LOG:' tags (use TRACE-LOG[<ns>/<label>]:):"; echo "$bare"; fail=1; fi

# 2. Every TRACE-LOG[...] is namespaced emit/ | suppress/ | infra/.
badns=$(grep -rhoE "TRACE-LOG\[[^]]*\]" "$ACL2"/*.lisp 2>/dev/null | grep -vE "TRACE-LOG\[(emit|suppress|infra)/" || true)
if [ -n "$badns" ]; then echo "FAIL: non-namespaced TRACE-LOG tags:"; echo "$badns"; fail=1; fi

# Direct top-level fms emits (emitted by keyword, not via :origin) — exempt from the
# rewrite-step round-trip below.
direct="step defthm defun type-prescription induction qed begin-proof-log rule rules pool-consider pool-subsumed"

# 3a. emit -> tag: each emitted rewrite-step origin (:origin 'X) has a TRACE-LOG[emit/X].
emitted=$(grep -rhoE ":origin '[A-Za-z0-9/-]+" "$ACL2"/*.lisp 2>/dev/null | sed "s/:origin '//" | sort -u)
for sym in $emitted; do
  if ! grep -rqF "TRACE-LOG[emit/$sym]" "$ACL2"/*.lisp 2>/dev/null; then
    echo "FAIL: emitted origin ':origin '$sym' has no TRACE-LOG[emit/$sym] tag"; fail=1
  fi
done

# 3b. tag -> emit: each TRACE-LOG[emit/X] (X not a direct top-level keyword) has an emitted
# :origin 'X. (This direction catches a tag whose code emits nothing/the wrong origin —
# e.g. a rewrite-step push missing its :origin.)
taglabels=$(grep -rhoE "TRACE-LOG\[emit/[A-Za-z0-9/-]+\]" "$ACL2"/*.lisp 2>/dev/null | sed -E 's/TRACE-LOG\[emit\///; s/\]//' | sort -u)
for lbl in $taglabels; do
  case " $direct " in *" $lbl "*) continue ;; esac
  if ! grep -rqF ":origin '$lbl" "$ACL2"/*.lisp 2>/dev/null; then
    echo "FAIL: TRACE-LOG[emit/$lbl] has no emitted \":origin '$lbl\" (label/emit mismatch)"; fail=1
  fi
done

# Report.
echo "--- TRACE-LOG tags by namespace ---"
grep -rhoE "TRACE-LOG\[[a-z]+/" "$ACL2"/*.lisp 2>/dev/null | sort | uniq -c
echo "--- rewrite-step origins (round-trip-checked) : $(echo "$emitted" | grep -c . ) ---"
if [ "$fail" -eq 0 ]; then echo "OK: tagging convention satisfied."; else echo "TAGGING CHECK FAILED."; fi
exit $fail
