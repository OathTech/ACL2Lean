#!/usr/bin/env bash
# TRUST-IMPORT gate (demo build 2026-08-11, design
# docs/plans/2026-08-11_demo-design.md §a): the `Imported/Sorting/`
# split makes the module layering the trust story, so a reader answers
# "what must I trust?" from `import` lines instead of from proofs. This
# script pins that layering. Static; no build; runs in `ci` next to
# check-file-weight.
#
# WHAT IT CHECKS — exactly two things, both by reading `^import` lines:
#
#  (1) LAYER PINS. Each of the six `Imported/Sorting/*.lean` modules'
#      DIRECT imports must equal its pinned set below. That is the
#      layering: Sims (definitions) <- Iso/IsoAdmission
#      (correspondence) <- Decode/DecodeSorts (replayed-statement
#      transports); Debt (the assumed facts) sits on Sims ALONE, so the
#      12 sorried statements are stated over the definitions only.
#
#  (2) NO REPLAY MACHINERY under Sims and Debt. Their TRANSITIVE import
#      closure (BFS over `^import` lines, same walk as
#      check-dark-files.sh) must not reach the proof-log / clause-tree /
#      development / driver / mirror-catalog modules listed in FORBIDDEN
#      below.
#
# WHAT IT DOES *NOT* CHECK — say this out loud, because the demo must
# not overclaim: Sims' closure DOES reach `ACL2Lean.Replay.EvalLemmas`
# and `ACL2Lean.Replay.Lemmas.*`, unavoidably, because
# `Imported/Lifting.lean` holds the encoders (`enc`/`boolEnc`) and
# imports the evaluation lemmas from one module. Separating those is
# real surgery on Lifting, not a rename; until it happens the honest
# claim is the one enforced here — Sims knows nothing of proof logs,
# clause trees, developments or the driver — NOT "no Replay module at
# all". `Sims.lean`'s header and `docs/DEMO.md` are worded to match.
#
# THREAT MODEL (two-standard rule, 2026-08-11): a SPEEDBUMP against
# forgetting the boundary while editing — a contributor who wants the
# driver in Sims can add it to the pinned set in one line, and that is
# fine, because the point is that the edit is visible and deliberate.
# It is NOT a barrier against a motivated construction (re-export
# through an allowed module defeats it — known, accepted). DO NOT
# HARDEN IT.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

DIR=ACL2Lean/Imported/Sorting

# (1) the pinned DIRECT imports, one line per module: "<file>|<imports>"
# (imports space-separated, order-insensitive).
PINS=(
  "Sims|ACL2Lean.Imported.Lifting ACL2Lean.Imported.Perm ACL2Lean.Lexorder"
  "Iso|ACL2Lean.Imported.Sorting.Sims ACL2Lean.Imported.ExecGen ACL2Lean.Imported.SimGen"
  "IsoAdmission|ACL2Lean.Imported.Sorting.Iso"
  "Decode|ACL2Lean.Imported.Sorting.IsoAdmission"
  "DecodeSorts|ACL2Lean.Imported.Sorting.Decode"
  "Debt|ACL2Lean.Imported.Sorting.Sims"
)

# (2) modules the Sims/Debt closures must not reach.
FORBIDDEN=(
  ACL2Lean.ProofLog
  ACL2Lean.ProofTree
  ACL2Lean.ClauseTree
  ACL2Lean.ClauseId
  ACL2Lean.DevLoad
  ACL2Lean.Replay.Driver
  ACL2Lean.Replay.Runner
  ACL2Lean.Replay.ParametricInstantiate
)
# every module under these prefixes is forbidden too
FORBIDDEN_PREFIXES=(
  ACL2Lean.Replay.Driver.
  ACL2Lean.Imported.Mirrors.
)

fail=0

imports_of() {  # $1 = path
  grep -E '^import ' "$1" | awk '{print $2}'
}

for pin in "${PINS[@]}"; do
  m="${pin%%|*}"; want="${pin#*|}"
  f="$DIR/$m.lean"
  if [ ! -f "$f" ]; then
    echo "check-trust-imports: missing layer module $f" >&2
    fail=1; continue
  fi
  read -r -a want_arr <<< "$want"
  got="$(imports_of "$f" | sort | tr '\n' ' ')"
  exp="$(printf '%s\n' "${want_arr[@]}" | sort | tr '\n' ' ')"
  if [ "$got" != "$exp" ]; then
    echo "LAYER PIN BROKEN: $f" >&2
    echo "  expected imports: $exp" >&2
    echo "  actual imports:   $got" >&2
    echo "  (the layering IS the trust story — if the change is" >&2
    echo "   deliberate, update PINS in scripts/check-trust-imports.sh" >&2
    echo "   and the layer docstrings/docs/DEMO.md that describe it)" >&2
    fail=1
  fi
done

is_forbidden() {  # $1 = module name
  local m="$1" p
  for p in "${FORBIDDEN[@]}"; do [ "$m" = "$p" ] && return 0; done
  for p in "${FORBIDDEN_PREFIXES[@]}"; do
    case "$m" in "$p"*) return 0 ;; esac
  done
  return 1
}

closure_check() {  # $1 = start module, $2 = human label
  local start="$1" label="$2"
  declare -A seen=()
  local queue=("$start") m path via
  declare -A parent=()
  while [ "${#queue[@]}" -gt 0 ]; do
    m="${queue[0]}"; queue=("${queue[@]:1}")
    path="${m//.//}.lean"
    [ -f "$path" ] || continue          # external package (e.g. Mathlib)
    while IFS= read -r imp; do
      [ -n "${seen[$imp]:-}" ] && continue
      seen["$imp"]=1
      parent["$imp"]="$m"
      if is_forbidden "$imp"; then
        via="$imp"
        local chain="$imp"
        while [ -n "${parent[$via]:-}" ] && [ "${parent[$via]}" != "$start" ]; do
          via="${parent[$via]}"; chain="$via -> $chain"
        done
        echo "REPLAY MACHINERY REACHED: $label reaches $imp" >&2
        echo "  via: $start -> $chain" >&2
        echo "  (first offender only — the rest of that subtree follows)" >&2
        fail=1
        return 0
      fi
      queue+=("$imp")
    done < <(imports_of "$path")
  done
}

closure_check ACL2Lean.Imported.Sorting.Sims "Sims.lean (layer 1, the definitions)"
closure_check ACL2Lean.Imported.Sorting.Debt "Debt.lean (layer 4, the assumed facts)"

if [ "$fail" -ne 0 ]; then
  echo "check-trust-imports: FAILED (see above)." >&2
  exit 1
fi
echo "check-trust-imports: layer pins hold; Sims/Debt closures free of \
proof-log/clause-tree/driver machinery."
