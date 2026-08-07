# Shared provenance/completeness helpers (capstone-demo arc Phase 0,
# review-1 P0-1/P0-2). ONE copy of the source-resolution, include-closure,
# and completeness-count logic, sourced by capture-proof-log.sh,
# check-log-provenance.sh, and backfill-log-provenance.sh — a fix applied
# to a clone missing its twin is the exact drift class this prevents.
#
# Callers must run under `set -euo pipefail` and define ROOT (repo root).

# The canonical source .lisp for a captured log. Rule (mirrors the capture
# recipes): a sibling <base>.lisp wins; else the acl2/books/sorting/
# submodule copy (OUTDIR captures). Fails loudly otherwise.
resolve_source_for_log() {
  local log="$1" base dir
  dir="$(dirname "$log")"
  base="$(basename "${log%.proof-log}")"
  if [ -f "$dir/$base.lisp" ]; then
    echo "$dir/$base.lisp"
  elif [ -f "$ROOT/acl2/books/sorting/$base.lisp" ]; then
    echo "$ROOT/acl2/books/sorting/$base.lisp"
  else
    echo "resolve_source_for_log: no source .lisp for $log (looked at \
$dir/$base.lisp and acl2/books/sorting/$base.lisp)" >&2
    return 1
  fi
}

# Transitive include-book closure of a source .lisp: prints one line per
# reachable book, depth-first, each once:
#   <path>            — a sibling-relative include (hash + recurse)
#   <path> SYSTEM     — a `:dir :system` community book, resolved against
#                       acl2/books/. NOT recursed: everything inside the
#                       acl2/ submodule is already transitively pinned by
#                       the sidecar's acl2-commit stamp + the dirty-tree
#                       check, which the checker enforces. The file's own
#                       hash is still recorded as defense-in-depth.
# An unresolvable include is FATAL (fail-closed — a book we cannot pair
# is a book we cannot certify provenance for).
include_closure() {
  local src="$1" seen="$2" dir form name target
  dir="$(dirname "$src")"
  while IFS= read -r form; do
    name="$(echo "$form" | sed 's/(include-book "//; s/".*$//')"
    case "$form" in
      *:dir*:system*)
        target="$ROOT/acl2/books/$name.lisp"
        if [ ! -f "$target" ]; then
          echo "include_closure: $src includes \"$name\" :dir :system but \
$target does not exist (unresolved include — fail-closed)" >&2
          return 1
        fi
        case "$seen" in *"|$target|"*) continue;; esac
        seen="$seen|$target|"
        echo "$target SYSTEM";;
      *)
        target="$dir/$name.lisp"
        if [ ! -f "$target" ]; then
          echo "include_closure: $src includes \"$name\" but $target does \
not exist (unresolved include — fail-closed)" >&2
          return 1
        fi
        case "$seen" in *"|$target|"*) continue;; esac
        seen="$seen|$target|"
        echo "$target"
        include_closure "$target" "$seen";;
    esac
  done < <(sed 's/;.*$//' "$src" \
             | grep -oE '\(include-book "[^"]+"( +:dir +:system)?' || true)
}

# Uncommented defthm/defthmd count in a source file (a leading `;`
# comments the form out — isort's perm-isort taught us this).
count_source_defthms() {
  grep -cE '^[^;]*\(defthmd?\b' "$1" || true
}

# :SOURCE :LOCAL theorem events in a log (include-book'd theorems arrive
# with no proof and no :QED — counting them against :QED is a false
# alarm). Events line-wrap arbitrarily, so normalize whitespace first.
# The negated character class excludes :SOURCE :LOCAL-WITNESS (encapsulate
# witness events, which carry NO :QED): the pre-2026-08-06 bare-prefix
# grep counted them too, so equisort/cov-encapsulate/cov-meta-rule
# captures ALWAYS warned "N of M" — a warning nobody saw, which is
# review-1 P0-2's exact failure mode, discovered the day the check
# became fatal.
count_log_local_defthms() {
  tr -s ' \n' '  ' < "$1" | { grep -oE ':SOURCE :LOCAL[^-A-Z]' || true; } \
    | wc -l | tr -d ' '
}

count_log_qeds() {
  grep -c '(:QED' "$1" || true
}

# Completeness verdict for (source, log): exit 0 iff complete; prints the
# reason on failure. The QED-per-DEFTHM signal is primary (a failed proof
# emits :DEFTHM at proof start with no matching :QED); the source count
# catches halts before a later defthm starts; the FAILED/HARD-ERROR grep
# catches prose that survives :structured mode. The log count can
# legitimately EXCEED the source count (defequiv/defcong generate
# theorems) — only a SHORTFALL fails.
check_capture_complete() {
  local src="$1" log="$2" want got qed
  # N1 (audit 2026-08-07): fail CLOSED on a missing source/log — an
  # empty count string previously produced a shell comparison error
  # and EXIT=0.
  if [ ! -f "$src" ] || [ ! -f "$log" ]; then
    echo "INCOMPLETE: missing source ($src) or log ($log)"
    return 1
  fi
  want="$(count_source_defthms "$src")"
  got="$(count_log_local_defthms "$log")"
  qed="$(count_log_qeds "$log")"
  if [ -z "$want" ] || [ -z "$got" ] || [ -z "$qed" ]; then
    echo "INCOMPLETE: $(basename "$log") — counting failed (empty count)"
    return 1
  fi
  if grep -q ":STOP-LD\|\*\*\*\*\*\*\*\* FAILED\|proof attempt has failed\|HARD ACL2 ERROR" "$log"; then
    echo "INCOMPLETE: $(basename "$log") — ACL2 reported a FAILED/aborted/HARD-ERROR event"
    return 1
  fi
  # PAIRING, not count equality (2026-08-06, found the day the check went
  # fatal): a macro-admitted :LOCAL defthm (defun-sk's -SUFF constraint)
  # legitimately has NO waterfall and NO :QED — but a defthm whose window
  # (up to the next event) contains (:STEP activity MUST reach (:QED, or
  # the proof was cut off. Events line-wrap arbitrarily, so records split
  # on "(:...". Residual blind spot (recorded): a truncation that cuts
  # exactly between a :DEFTHM line and its first :STEP looks
  # macro-admitted — the source-count rung below catches it unless
  # macro-generated theorems pad the count; the real fix is fork-batch
  # item 8's explicit capture END record.
  local unpaired
  unpaired="$(awk 'BEGIN{RS="\n\\(:"; bad=""}
    /^DEFTHM/ {
      if (open != "" && steps && !qed) bad = bad " " open
      open = ""; steps = 0; qed = 0
      if ($0 ~ /:SOURCE :LOCAL([^-A-Z]|$)/) { open = $2 }
      next }
    /^STEP/ { if (open != "") steps = 1; next }
    /^QED/  { if (open != "") qed = 1; next }
    END { if (open != "" && steps && !qed) bad = bad " " open
          print bad }' "$log")"
  if [ -n "${unpaired// /}" ]; then
    echo "INCOMPLETE: $(basename "$log") — waterfall started but no (:QED) for:${unpaired} (proof cut off or FAILED)"
    return 1
  fi
  if [ "$got" -lt "$want" ]; then
    echo "INCOMPLETE: $(basename "$log") — logged $got of $want source defthm proof(s): ACL2 halted before a later event ($qed :QED)"
    return 1
  fi
  # The explicit END record (fork-batch item 8; UNCONDITIONAL since the
  # 2026-08-07 audit M1 — the conditional form was a no-op against the
  # truncation it was landed to catch, and the whole corpus is
  # post-item-8): a healthy capture ends with (:CAPTURE-END ... :STATUS
  # :COMPLETE); its absence means truncation ANYWHERE, including before
  # any countable signal.
  if ! tr -s ' \n' '  ' < "$log" | grep -q '(:CAPTURE-END .*:STATUS :COMPLETE'; then
    echo "INCOMPLETE: $(basename "$log") — no (:CAPTURE-END :STATUS :COMPLETE) end record (truncated, or a pre-item-8 capture)"
    return 1
  fi
  # S7 (audit 2026-08-07): an ACL2-level event failure emits
  # (:EVENT-FAILED ...) and ld returns to the loop — the driver then
  # stamps :STATUS :COMPLETE regardless. The event marker is the truth.
  if grep -q '(:EVENT-FAILED' "$log"; then
    echo "INCOMPLETE: $(basename "$log") — (:EVENT-FAILED) present: an event FAILED during capture"
    return 1
  fi
  return 0
}

sha256_of() {
  sha256sum "$1" | cut -d' ' -f1
}

# Repo-relative form of an absolute path.
repo_rel() {
  case "$1" in
    "$ROOT"/*) echo "${1#"$ROOT"/}";;
    *) echo "$1";;
  esac
}
