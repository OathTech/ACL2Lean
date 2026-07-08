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
# Corpus format + expectation classes (match / unsupported / known-bug): see
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

total_ok=0 total_unsupported=0 total_known_bug=0 total_refuse=0 total_fail=0
declare -a fail_lines=()
declare -a target_lines=()

# Is an outcome "no value" (Lean stuck/refused, or ACL2 refused)? Both `<stuck>`
# (evalOpt did not converge) and `<refused>` (a parse/translate/read error)
# count as the interpreter declining to produce a value.
is_no_value() { [[ "$1" == "<stuck>" || "$1" == "<refused>" ]]; }

# The shared verdict for one form. Args: class, rest-of-;@-line, lean_raw,
# acl2_raw, file. Updates the global counters / fail_lines / target_lines and
# echoes the verdict string. Used by BOTH the batched and the per-form
# (isolated) paths, so the classification rules live in exactly one place.
classify_form() {
  local class="$1" rest="$2" lean_raw="$3" acl2_raw="$4" file="$5"
  local ln an dval dn _kw
  ln="$(normalize "$lean_raw")"; an="$(normalize "$acl2_raw")"
  case "$class" in
    match)
      # Both must produce a real value AND agree. A no-value on either side is a
      # FAIL: Lean stuck/refused is a regression; ACL2 refused/empty means the
      # form isn't a clean value there (mis-classified — a match entry must be a
      # genuine agreeing value on both sides, never a both-fail vacuous pass).
      if is_no_value "$lean_raw"; then
        total_fail=$((total_fail+1))
        fail_lines+=("$file: expected MATCH but Lean gave no value ($lean_raw; acl2=$acl2_raw)")
        VERDICT="FAIL(lean $lean_raw)"
      elif [[ "$acl2_raw" == "<refused>" || -z "$acl2_raw" ]]; then
        total_fail=$((total_fail+1))
        fail_lines+=("$file: 'match' entry but ACL2 produced no value ($acl2_raw; lean=$lean_raw) — not a clean value in ACL2; reclassify (refuse/unsupported)")
        VERDICT="FAIL(acl2 no-value)"
      elif [[ "$ln" == "$an" ]]; then
        total_ok=$((total_ok+1)); VERDICT="ok"
      else
        total_fail=$((total_fail+1))
        fail_lines+=("$file: MISMATCH lean=$lean_raw acl2=$acl2_raw (fidelity bug)")
        VERDICT="FAIL-MISMATCH"
      fi ;;
    unsupported)
      # evalOpt does not model this yet; Lean must produce no value AND ACL2 must
      # produce a real value (the class pins the target value a faithful model
      # must later compute — an `unsupported` form ACL2 ALSO can't evaluate is
      # ill-formed/mis-classified, not a real target).
      if [[ "$acl2_raw" == "<refused>" || -z "$acl2_raw" ]]; then
        total_fail=$((total_fail+1))
        fail_lines+=("$file: 'unsupported' entry but ACL2 produced no value ($acl2_raw; lean=$lean_raw) — form is ill-formed; reclassify to refuse or fix it")
        VERDICT="FAIL(acl2 no-value)"
      elif is_no_value "$lean_raw"; then
        total_unsupported=$((total_unsupported+1))
        target_lines+=("$acl2_raw  ⇐  (unsupported; acl2 value shown)")
        VERDICT="ok-unsupported"
      else
        total_fail=$((total_fail+1))
        fail_lines+=("$file: 'unsupported' entry now yields lean=$lean_raw (acl2=$acl2_raw) — now modeled, reclassify to match")
        VERDICT="FAIL-GREW(->match)"
      fi ;;
    refuse)
      # Ill-formed / rejected form: BOTH interpreters must decline (ACL2 errors
      # → <refused>; Lean → <stuck> or <refused>). PASS iff neither produced a
      # value — the fidelity check that our fail-closed matches ACL2's refusal.
      if is_no_value "$lean_raw" && [[ "$acl2_raw" == "<refused>" ]]; then
        total_refuse=$((total_refuse+1))
        VERDICT="ok-refuse"
      elif [[ "$acl2_raw" != "<refused>" ]]; then
        total_fail=$((total_fail+1))
        fail_lines+=("$file: 'refuse' entry but ACL2 produced a VALUE ($acl2_raw; lean=$lean_raw) — not actually refused; reclassify")
        VERDICT="FAIL(acl2 accepted)"
      else
        total_fail=$((total_fail+1))
        fail_lines+=("$file: 'refuse' entry but Lean produced a VALUE ($lean_raw; acl2 refused) — divergence; reclassify to known-bug")
        VERDICT="FAIL(lean accepted)"
      fi ;;
    known-bug)
      # Known divergence: the recorded `lean <val>` is what Lean produces (a
      # value, or <stuck>/<refused>), while ACL2 differs. FAILs when Lean's
      # outcome changes — e.g. a fix — forcing reclassification.
      read -r _kw dval <<<"$rest"
      dn="$(normalize "$dval")"
      if [[ "$ln" == "$dn" ]]; then
        total_known_bug=$((total_known_bug+1))
        target_lines+=("KNOWN-BUG lean=$lean_raw vs acl2=$acl2_raw ($file)")
        VERDICT="ok-known-bug"
      else
        total_fail=$((total_fail+1))
        fail_lines+=("$file: 'known-bug' entry: lean now=$lean_raw, recorded=$dval (behavior changed — likely fixed; reclassify)")
        VERDICT="FAIL-BUG-CHANGED"
      fi ;;
    *)
      total_fail=$((total_fail+1))
      fail_lines+=("$file: unknown expectation class '$class'")
      VERDICT="FAIL(bad-class:$class)" ;;
  esac
}

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

  # ── Per-form ISOLATION path (`;@isolate` directive) ──────────────────────
  # For boundary/ill-formed forms: a float literal HALTS the ACL2 session and a
  # radix literal ABORTS the Lean parse stream, so they cannot share a batched
  # session. Run each form in its own ACL2 session and its own Lean invocation,
  # mapping a read/translate/parse error to the `<refused>` outcome. Forms are
  # single-line here (the boundary corpus is written that way): pair each `;@`
  # with the next non-blank, non-comment line.
  if grep -qE '^;@isolate\b' "$file"; then
    mapfile -t iso_forms < <(grep -vE '^;' "$file" | grep -vE '^[[:space:]]*$')
    if [[ "${#iso_forms[@]}" -ne "${#expects[@]}" ]]; then
      echo "  FATAL: $file (isolate) — ${#expects[@]} expectations vs ${#iso_forms[@]} forms; each ;@ needs one single-line form."
      total_fail=$((total_fail+1)); continue
    fi
    printf '  %-4s %-12s %-16s %-16s %s\n' "#" "expect" "lean" "acl2" "verdict"
    for i in "${!expects[@]}"; do
      read -r _at class rest <<<"${expects[$i]}"
      form="${iso_forms[$i]}"
      # ACL2, isolated: value line after the @@GO@@ marker, or <refused> on any
      # read/translate/interface error (incl. the session-halting float error).
      { echo '(set-guard-checking nil)'; [[ -n "$book" ]] && printf '(ld "%s")\n' "$book";
        echo '(cw "@@GO@@~%")'; printf '%s\n' "$form"; echo '(good-bye)'; } > "$tmp/iso.in"
      "$ACL2_BIN" < "$tmp/iso.in" > "$tmp/iso.raw" 2>&1
      local_acl2=""
      if sed -n '/@@GO@@/,$p' "$tmp/iso.raw" | grep -qaE '^ACL2 Error|^Error:|floating-point input|Halted'; then
        local_acl2="<refused>"
      else
        local_acl2="$(sed -n '/@@GO@@/,$p' "$tmp/iso.raw" | grep -av '@@GO@@' \
          | grep -aE '^ACL2 !?>' | sed -E 's/^ACL2 !?>//' | grep -av '^Bye\.$' | head -1)"
      fi
      # Lean, isolated: <refused> on a parse error/uncaught exception, else the
      # value or <stuck>.
      if [[ -z "$book" ]]; then
        local_lean="$(printf '%s\n' "$form" | "${LEAN_EXE[@]}" eval 2>&1 | tail -1)"
      else
        local_lean="$(printf '%s\n' "$form" | "${LEAN_EXE[@]}" eval-in "$book" 2>&1 | tail -1)"
      fi
      case "$local_lean" in
        *"Parse error"*|*"uncaught exception"*) local_lean="<refused>" ;;
      esac
      classify_form "$class" "$rest" "$local_lean" "$local_acl2" "$file"
      printf '  %-4s %-12s %-16s %-16s %s\n' "$i" "$class" "${local_lean:-<none>}" "${local_acl2:-<none>}" "$VERDICT"
    done
    continue
  fi

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
  # Reconstruct ONE outcome per form from ACL2's output. Each form's output
  # begins at an `ACL2 !?>` prompt; the value may WRAP onto continuation lines
  # (ACL2 pretty-prints wide values across lines — only the first has a prompt),
  # and an ill-formed form emits an `ACL2 Error [...]`/Halt block instead of a
  # value. So we split on prompts and, per segment: emit `<refused>` if it holds
  # an error/halt, else JOIN its lines into the single value (whitespace is
  # collapsed later by normalize). This (a) fixes truncation of wrapped values —
  # a first-line-only slice could otherwise pass a wrong value as a match — and
  # (b) surfaces ACL2 errors as `<refused>` uniformly with the isolate path,
  # instead of the old ambiguous empty line. Everything before the sentinel
  # (preamble: guard-checking, ld) is skipped; the trailing good-bye prompt is
  # an empty segment and dropped.
  awk '
    /@@SENTINEL@@/ { seen=1; next }
    !seen { next }
    /^ACL2 !?>/ {
      flush()
      line=$0; sub(/^ACL2 !?>/,"",line)
      seg=line; started=1; err=0
      if (line ~ /ACL2 Error|Halted|floating-point input/) err=1
      next
    }
    started {
      if ($0 ~ /ACL2 Error|Halted|floating-point input/) err=1
      seg = seg " " $0
    }
    function flush() {
      if (!started) return
      gsub(/^ +| +$/,"",seg)
      if (err) print "<refused>"
      else if (seg != "" && seg != "Bye.") print seg
      started=0; seg=""; err=0
    }
    END { flush() }
  ' "$tmp/acl2.raw" > "$tmp/acl2.vals"

  # ── Lean value stream (one process, whole file) ──
  if [[ -z "$book" ]]; then
    "${LEAN_EXE[@]}" eval < "$tmp/forms.lisp" > "$tmp/lean.vals" 2>/dev/null
  else
    "${LEAN_EXE[@]}" eval-in "$book" < "$tmp/forms.lisp" > "$tmp/lean.vals" 2>/dev/null
  fi

  n_exp=${#expects[@]}
  n_acl2=$(wc -l < "$tmp/acl2.vals" | tr -d ' ')
  n_lean=$(wc -l < "$tmp/lean.vals" | tr -d ' ')

  # Alignment self-check: #expectations must equal #outcomes from each side.
  # The ACL2 reconstruction emits exactly one outcome per prompt (value, joined
  # across wrap lines, or <refused>); the Lean stream emits one line per form.
  if [[ "$n_exp" -ne "$n_acl2" ]] || [[ "$n_exp" -ne "$n_lean" ]]; then
    echo "  FATAL: stream misalignment in $file — $n_exp expectations, $n_acl2 ACL2 outcomes, $n_lean Lean outcomes."
    echo "         (every form needs exactly one preceding ;@ line; batched files"
    echo "          cannot contain session-fatal forms — floats/radix need ;@isolate.)"
    total_fail=$((total_fail+1))
    continue
  fi

  mapfile -t acl2_vals < "$tmp/acl2.vals"
  mapfile -t lean_vals < "$tmp/lean.vals"

  printf '  %-4s %-12s %-16s %-16s %s\n' "#" "expect" "lean" "acl2" "verdict"
  for i in "${!expects[@]}"; do
    # expect line looks like ";@ <class> [lean <val>]"
    read -r _at class rest <<<"${expects[$i]}"
    lean_raw="${lean_vals[$i]:-}"
    acl2_raw="${acl2_vals[$i]:-}"
    ln="$(normalize "$lean_raw")"; an="$(normalize "$acl2_raw")"

    classify_form "$class" "$rest" "$lean_raw" "$acl2_raw" "$file"
    printf '  %-4s %-12s %-16s %-16s %s\n' "$i" "$class" "${lean_raw:-<none>}" "${acl2_raw:-<none>}" "$VERDICT"
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
echo "SUMMARY: $total_ok match, $total_unsupported unsupported, $total_known_bug known-bug, $total_refuse refuse, $total_fail FAIL"
if [[ $total_fail -eq 0 ]]; then exit 0; else exit 1; fi
