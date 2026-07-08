#!/usr/bin/env bash
# Differential test manager: compare the Lean ACL2-logic interpreter against
# real ACL2, form-by-form, over a corpus of ACL2 forms.
#
# This script is a PURE COMPARATOR. It does not evaluate anything itself and
# neither interpreter knows it is being tested — each is just "an ACL2":
#   forms on stdin  →  one value per form on stdout.
#     reference: acl2/saved_acl2 < forms.lisp
#     Lean:      lake exe acl2lean eval[-in <book>] < forms.lisp
# The manager feeds a corpus file to both, joins the two value streams by form
# index, and consults the corpus metadata (`;@` comment lines — invisible to
# both interpreters) to decide whether each result is expected.
#
# Corpus format + expectation classes (match / stuck / diverge): see
# Tests/differential/README.md. Long-term aim: the Lean interpreter masquerades
# as ACL2 completely, so this becomes a plain string-diff over random programs.
#
# Usage:
#   scripts/diff-test.sh                       # all corpus/*.lisp
#   scripts/diff-test.sh corpus/int-arith.lisp # specific file(s)
# Needs acl2/saved_acl2 (just build-acl2) and a built acl2lean exe.
#
# No `-e`: we report per-form and aggregate failures, exiting non-zero at the
# end. `cd` is guarded explicitly (a silent failure would use the wrong tree).
set -uo pipefail
cd "$(dirname "$0")/.." || { echo "FATAL: cannot cd to repo root" >&2; exit 2; }

DIFF_DIR="Tests/differential"
ACL2_BIN="acl2/saved_acl2"
export ACL2_CUSTOMIZATION=NONE

if [[ ! -x "$ACL2_BIN" ]]; then
  echo "FATAL: $ACL2_BIN not found — run 'just build-acl2' first." >&2
  exit 2
fi

echo "Building the Lean interpreter (lake build acl2lean)…"
lake build acl2lean >/dev/null 2>&1 || { echo "FATAL: lake build acl2lean failed" >&2; exit 2; }
LEAN_EXE=(lake exe acl2lean)

# Map a `;@world <name>` directive to a book path. `simple` is the in-repo
# world with my-len/my-app; extend as corpora need other books.
world_book() {
  case "$1" in
    ""|empty) echo "" ;;
    simple)   echo "acl2_samples/simple.lisp" ;;
    *)        echo "__UNKNOWN__" ;;
  esac
}

# Normalize a value line for comparison: uppercase (ACL2 prints symbols upper,
# our interpreter lower — a known rendering gap, folded here until the printer
# masquerade is complete) and collapse internal whitespace.
normalize() { printf '%s' "$1" | tr '[:lower:]' '[:upper:]' | tr -s ' \t' ' ' | sed 's/^ *//; s/ *$//'; }

# Discover corpus files.
if [[ $# -gt 0 ]]; then
  files=("$@")
else
  mapfile -t files < <(find "$DIFF_DIR/corpus" -name '*.lisp' | sort)
fi
if [[ ${#files[@]} -eq 0 ]]; then
  echo "No corpus files found under $DIFF_DIR/corpus/." >&2
  exit 2
fi

tmp="${TMPDIR:-/tmp}/difftest_$$"; mkdir -p "$tmp"
trap 'rm -rf "$tmp"' EXIT

total_ok=0 total_stuck=0 total_diverge=0 total_fail=0
declare -a fail_lines=()
declare -a target_lines=()

for file in "${files[@]}"; do
  [[ -f "$file" ]] || { echo "skip (not a file): $file" >&2; continue; }
  echo ""
  echo "═══ $file ═══"

  # World directive (first `;@world` line, if any).
  world="$(grep -m1 -oE '^;@world[[:space:]]+[A-Za-z0-9_-]+' "$file" | awk '{print $2}')"
  book="$(world_book "${world:-}")"
  if [[ "$book" == "__UNKNOWN__" ]]; then
    echo "  FATAL: unknown ;@world '$world' in $file (extend world_book)" >&2
    total_fail=$((total_fail+1)); continue
  fi

  # Expectations, in form order: every `;@` line that is NOT a directive.
  mapfile -t expects < <(grep -oE '^;@[[:space:]].*$' "$file")

  # The bare forms (strip `;@…` metadata lines; keep everything else — the
  # interpreters' own readers skip ordinary comments/blank lines). This is the
  # exact byte stream both interpreters consume.
  grep -vE '^;@' "$file" > "$tmp/forms.lisp"

  # ── ACL2 value stream ──
  # A leading `(set-guard-checking nil)` puts ACL2 in the total/logical
  # semantics evalOpt models (else guard violations like (binary-+ 'nil 3)
  # yield no value); a `;@world` book is loaded the normal ACL2 way with `ld`,
  # mirroring how the Lean side's `eval-in` loads it. We print a sentinel after
  # the preamble and slice the value stream to what follows, so preamble output
  # is not counted.
  {
    echo '(set-guard-checking nil)'
    [[ -n "$book" ]] && printf '(ld "%s")\n' "$book"
    echo '(cw "@@SENTINEL@@~%")'
    cat "$tmp/forms.lisp"
  } > "$tmp/acl2.in"
  "$ACL2_BIN" < "$tmp/acl2.in" > "$tmp/acl2.raw" 2>&1
  # ACL2 echoes each value after its `ACL2 !?>` prompt. Keep only the value
  # lines strictly AFTER the sentinel line itself, and drop the final `Bye.`.
  # (`/re/,$p` includes the matching line, whose own `ACL2 >@@SENTINEL@@`
  # prompt would otherwise count as a spurious leading value — hence the
  # explicit drop of the sentinel line.)
  sed -n '/@@SENTINEL@@/,$p' "$tmp/acl2.raw" | grep -av '@@SENTINEL@@' \
    | grep -aE '^ACL2 !?>' | sed -E 's/^ACL2 !?>//' | grep -av '^Bye\.$' > "$tmp/acl2.vals"

  # ── Lean value stream (one process, whole file) ──
  if [[ -z "$book" ]]; then
    "${LEAN_EXE[@]}" eval < "$tmp/forms.lisp" > "$tmp/lean.vals" 2>/dev/null
  else
    "${LEAN_EXE[@]}" eval-in "$book" < "$tmp/forms.lisp" > "$tmp/lean.vals" 2>/dev/null
  fi

  n_exp=${#expects[@]}
  n_acl2=$(wc -l < "$tmp/acl2.vals" | tr -d ' ')
  n_lean=$(wc -l < "$tmp/lean.vals" | tr -d ' ')

  # Alignment self-check: #expectations must equal #values from each side.
  if [[ "$n_exp" -ne "$n_acl2" ]] || [[ "$n_exp" -ne "$n_lean" ]]; then
    echo "  FATAL: stream misalignment in $file — $n_exp expectations, $n_acl2 ACL2 values, $n_lean Lean values."
    echo "         (every form needs exactly one preceding ;@ line; a form that"
    echo "          errors in ACL2 emits an empty value line — check the form.)"
    total_fail=$((total_fail+1))
    continue
  fi

  mapfile -t acl2_vals < "$tmp/acl2.vals"
  mapfile -t lean_vals < "$tmp/lean.vals"

  printf '  %-4s %-9s %-30s %-16s %-16s %s\n' "#" "expect" "form-value(acl2)" "lean" "acl2" "verdict"
  for i in "${!expects[@]}"; do
    # expect line looks like ";@ <class> [lean <val>]"
    read -r _at class rest <<<"${expects[$i]}"
    lean_raw="${lean_vals[$i]:-}"
    acl2_raw="${acl2_vals[$i]:-}"
    ln="$(normalize "$lean_raw")"; an="$(normalize "$acl2_raw")"

    verdict="?"
    case "$class" in
      match)
        if [[ "$lean_raw" == "<stuck>" ]]; then
          verdict="FAIL(lean stuck)"; total_fail=$((total_fail+1))
          fail_lines+=("$file: expected MATCH but Lean STUCK (acl2=$acl2_raw)")
        elif [[ "$ln" == "$an" ]]; then
          verdict="ok"; total_ok=$((total_ok+1))
        else
          verdict="FAIL-MISMATCH"; total_fail=$((total_fail+1))
          fail_lines+=("$file: MISMATCH lean=$lean_raw acl2=$acl2_raw (fidelity bug)")
        fi ;;
      stuck)
        if [[ "$lean_raw" == "<stuck>" ]]; then
          verdict="ok-stuck"; total_stuck=$((total_stuck+1))
          target_lines+=("$acl2_raw  ⇐  (unmodeled; acl2 value shown)")
        else
          verdict="FAIL-GREW(->match)"; total_fail=$((total_fail+1))
          fail_lines+=("$file: 'stuck' entry now yields lean=$lean_raw (acl2=$acl2_raw) — reclassify to match")
        fi ;;
      diverge)
        # rest = "lean <val>"
        read -r _kw dval <<<"$rest"
        dn="$(normalize "$dval")"
        if [[ "$ln" == "$dn" ]]; then
          verdict="ok-diverge"; total_diverge=$((total_diverge+1))
          target_lines+=("DIVERGENCE lean=$lean_raw vs acl2=$acl2_raw (known; $file)")
        else
          verdict="FAIL-DIVERGE-CHANGED"; total_fail=$((total_fail+1))
          fail_lines+=("$file: 'diverge' entry: lean now=$lean_raw, recorded=$dval (divergence changed — reclassify)")
        fi ;;
      *)
        verdict="FAIL(bad-class:$class)"; total_fail=$((total_fail+1))
        fail_lines+=("$file: unknown expectation class '$class'") ;;
    esac
    printf '  %-4s %-9s %-30s %-16s %-16s %s\n' "$i" "$class" "" "${lean_raw:-<none>}" "${acl2_raw:-<none>}" "$verdict"
  done
done

echo ""
if [[ ${#target_lines[@]} -gt 0 ]]; then
  echo "── DOCUMENTED SURFACE (not-yet-faithful; gate stays green) ──"
  printf '  %s\n' "${target_lines[@]}"
  echo ""
fi
if [[ ${#fail_lines[@]} -gt 0 ]]; then
  echo "── FAILURES (${#fail_lines[@]}) ──"
  printf '  %s\n' "${fail_lines[@]}"
  echo ""
fi
echo "SUMMARY: $total_ok match-ok, $total_stuck stuck, $total_diverge diverge, $total_fail FAIL"
if [[ $total_fail -eq 0 ]]; then exit 0; else exit 1; fi
