#!/usr/bin/env bash
# Differential test: evalOpt (Lean trusted core) vs real ACL2 on ground terms.
#
# For each ground s-expression in the battery below, evaluate it in BOTH
#   - the Lean model:  `lake exe acl2lean eval-in acl2_samples/simple.lisp <expr>`
#       (the `world` has my-len/my-app; builtins are intrinsic to evalOpt)
#   - real ACL2:       acl2/saved_acl2 with `(set-guard-checking nil)` so ACL2
#       computes the LOGICAL (fix-coerced, total) value that evalOpt models,
#       plus the same two defuns.
# Outputs are normalized (case-fold, whitespace-collapse) and compared.
#
# Any MISMATCH is a real discrepancy in the trusted core (evalOpt/Logic) vs ACL2.
# A "Lean: <stuck>" with an ACL2 value is an evalOpt INCOMPLETENESS (unmodeled
# builtin / fuel), reported separately from a value MISMATCH.
#
# Usage:  bash scripts/diff_eval.sh        (run from repo root)
set -uo pipefail
cd "$(dirname "$0")/.."
ROOT="$(pwd)"
WORLD="acl2_samples/simple.lisp"
ACL2_BIN="acl2/saved_acl2"
export ACL2_CUSTOMIZATION=NONE

# ── The battery ────────────────────────────────────────────────────────────
# Each entry is a ground s-expression. ACL2 `'` quoting is fine inside the
# bash double-quoted array elements.
tests=(
  # integer arithmetic
  "(binary-+ '2 '3)"
  "(binary-+ '-5 '5)"
  "(binary-+ '-2 '-3)"
  "(binary-* '3 '4)"
  "(binary-* '-2 '6)"
  "(unary-- '7)"
  "(binary-+ (binary-+ '1 '2) '3)"
  # rational arithmetic (exercises mkNumber gcd-normalization)
  "(binary-+ '1/2 '1/2)"
  "(binary-+ '1/3 '1/6)"
  "(binary-+ '1/3 '2/3)"
  "(binary-* '1/2 '4)"
  "(binary-* '2/3 '3/4)"
  "(unary-/ '4)"
  "(binary-+ '1/6 '1/6)"
  # fix-coercion of non-numbers (set-guard-checking nil semantics)
  "(binary-+ 'nil '3)"
  "(binary-+ 't '3)"
  "(binary-+ '(1 2) '5)"
  "(fix '5)"
  "(fix 'nil)"
  "(fix 't)"
  # recognizers / type
  "(acl2-numberp '5)"
  "(acl2-numberp 'nil)"
  "(acl2-numberp '1/2)"
  "(integerp '5)"
  "(integerp '1/2)"
  "(consp '(1))"
  "(consp 'nil)"
  "(consp '5)"
  # car/cdr/cons incl. non-cons (logical: nil)
  "(car '(1 2))"
  "(cdr '(1 2 3))"
  "(cons '1 '2)"
  "(car '5)"
  "(cdr '5)"
  "(car 'nil)"
  "(cdr 'nil)"
  # comparison / equal
  "(< '2 '3)"
  "(< '3 '2)"
  "(< '1/3 '1/2)"
  "(equal '(1 2) '(1 2))"
  "(equal '(1 2) '(1 3))"
  "(if 't '1 '2)"
  "(if 'nil '1 '2)"
  # my-len / my-app (recursion, symbols, edge cases)
  "(my-len '(1 2 3))"
  "(my-len 'nil)"
  "(my-len '7)"
  "(my-app '(1 2) '(3 4))"
  "(my-app 'nil '(1 2))"
  "(my-app '(a b) '(c d e))"
  "(my-len (my-app '(1 2 3) '(4 5)))"
  "(binary-+ (my-len '(1 2)) (my-len '(3 4 5)))"
  "(my-len (my-app '(1 2 3) 'nil))"
)

normalize() { tr 'a-z' 'A-Z' | tr -s ' \t' ' ' | sed 's/^ *//; s/ *$//'; }

echo "Building (lake build)…"
lake build >/dev/null 2>&1 || { echo "lake build FAILED"; exit 1; }

# ── ACL2 side: one session, indexed cw markers ─────────────────────────────
acl2_in="${TMPDIR:-/tmp}/acl2_diff_$$.lsp"; acl2_out="${TMPDIR:-/tmp}/acl2_diff_$$.out"
{
  echo '(set-guard-checking nil)'
  echo '(defun my-len (x) (if (consp x) (+ 1 (my-len (cdr x))) 0))'
  echo '(defun my-app (x y) (if (consp x) (cons (car x) (my-app (cdr x) y)) y))'
  for i in "${!tests[@]}"; do
    printf '(cw "@@%s@@~x0@@~%%" %s)\n' "$i" "${tests[$i]}"
  done
  echo '(good-bye)'
} > "$acl2_in"
timeout 180 "$ACL2_BIN" < "$acl2_in" > "$acl2_out" 2>&1

# ── Compare ────────────────────────────────────────────────────────────────
pass=0; mismatch=0; stuck=0
printf '\n%-3s %-34s %-16s %-16s %s\n' "#" "expr" "lean" "acl2" "verdict"
printf '%s\n' "------------------------------------------------------------------------------------------"
for i in "${!tests[@]}"; do
  expr="${tests[$i]}"
  lean_raw="$(lake exe acl2lean eval-in "$WORLD" "$expr" 2>/dev/null | tail -1)"
  # ACL2: pull the value between @@i@@ and @@ (handle possible prompt prefix)
  acl2_raw="$(grep -aoE "@@$i@@.*@@" "$acl2_out" | head -1 | sed -E "s/^@@$i@@//; s/@@$//")"
  ln="$(printf '%s' "$lean_raw" | normalize)"
  an="$(printf '%s' "$acl2_raw" | normalize)"
  if [[ -z "$lean_raw" ]]; then
    verdict="STUCK(lean)"; stuck=$((stuck+1))
  elif [[ -z "$acl2_raw" ]]; then
    verdict="NO-ACL2"; stuck=$((stuck+1))
  elif [[ "$ln" == "$an" ]]; then
    verdict="ok"; pass=$((pass+1))
  else
    verdict="*** MISMATCH ***"; mismatch=$((mismatch+1))
  fi
  printf '%-3s %-34s %-16s %-16s %s\n' "$i" "$expr" "${lean_raw:-<none>}" "${acl2_raw:-<none>}" "$verdict"
done
printf '%s\n' "------------------------------------------------------------------------------------------"
echo "PASS=$pass  MISMATCH=$mismatch  STUCK/NO-ACL2=$stuck  (total ${#tests[@]})"
rm -f "$acl2_in" "$acl2_out"
[[ $mismatch -eq 0 ]]
