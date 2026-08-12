#!/usr/bin/env bash
# TRUST-IMPORT gate — v2 (demo v2, 2026-08-12). THE DEMO FOLDER
# (`ACL2Lean/Demo/Sorting/`) IS THE TRUST BASE, and the trust story is
# told by `import` lines: a reader answers "what must I trust?" by
# reading four files, not by chasing proofs. This script pins that.
# Static; no build; runs in `ci` next to check-file-weight.
#
# WHAT IT CHECKS — three things, all by reading `^import` lines:
#
#  (1) DEMO CLOSURE WHITELIST. The TRANSITIVE import closure of
#      `TCB.lean`, `AclSource.lean` and `Assumptions.lean` may contain
#      NOTHING but the value/semantic core listed in DEMO_CLOSURE_OK
#      below (plus external packages, which have no ACL2Lean content).
#      That is the strong, honest claim: the definitions, the ACL2
#      transcripts and the assumptions know nothing of the replay —
#      not "no driver", but no `Replay` module at all. (v1 could not
#      make this claim: the old `Sims.lean` reached
#      `Replay.EvalLemmas` through `Imported/Lifting.lean`. Demo v2
#      moved the definitions and term builders OUT of Lifting instead,
#      so the caveat is gone; the arrow now runs machinery -> demo.)
#
#  (2) LAYER PINS. Each demo module and each `Imported/Sorting/*.lean`
#      machinery module must have EXACTLY its pinned direct imports.
#      `Statements.lean` is the one demo file that imports machinery,
#      and it imports the catalog alone — it is statements only.
#
#  (3) NO REVERSE ARROW. No file under `ACL2Lean/Demo/` may import the
#      replay machinery listed in FORBIDDEN, other than
#      `Statements.lean`'s pinned catalog import.
#
# THREAT MODEL (two-standard rule, 2026-08-11): a SPEEDBUMP against
# forgetting the boundary while editing — a contributor who wants the
# driver in the TCB can add it to the pinned set in one line, and that
# is fine, because the point is that the edit is visible and
# deliberate. It is NOT a barrier against a motivated construction
# (re-export through an allowed module defeats it — known, accepted).
# DO NOT HARDEN IT.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

DEMO=ACL2Lean/Demo/Sorting
MACH=ACL2Lean/Imported/Sorting

# (2) the pinned DIRECT imports, one line per module:
# "<path>|<imports>" (space-separated, order-insensitive).
PINS=(
  "$DEMO/TCB.lean|ACL2Lean.Lexorder Batteries.Data.List.Basic"
  "$DEMO/AclSource.lean|ACL2Lean.Syntax"
  "$DEMO/Assumptions.lean|ACL2Lean.EvalOpt ACL2Lean.Demo.Sorting.TCB ACL2Lean.Demo.Sorting.AclSource"
  "$DEMO/Statements.lean|ACL2Lean.Imported.Mirrors.Catalog"
  "$MACH/Iso.lean|ACL2Lean.Demo.Sorting.TCB ACL2Lean.Demo.Sorting.AclSource ACL2Lean.Imported.Perm ACL2Lean.Imported.ExecGen ACL2Lean.Imported.SimGen"
  "$MACH/IsoAdmission.lean|ACL2Lean.Imported.Sorting.Iso"
  "$MACH/Decode.lean|ACL2Lean.Imported.Sorting.IsoAdmission"
  "$MACH/DecodeSorts.lean|ACL2Lean.Imported.Sorting.Decode"
)

# (1) the ONLY ACL2Lean modules the demo trust base may transitively
# reach: the value core, the semantic model, and each other.
DEMO_CLOSURE_OK=(
  ACL2Lean.Syntax
  ACL2Lean.Logic
  ACL2Lean.Lexorder
  ACL2Lean.Parser
  ACL2Lean.EvalOpt
  ACL2Lean.Demo.Sorting.TCB
  ACL2Lean.Demo.Sorting.AclSource
)

# (3) machinery no demo file may import directly (Statements' pinned
# catalog import is checked by the layer pin instead).
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
FORBIDDEN_PREFIXES=(
  ACL2Lean.Replay.
  ACL2Lean.Imported.
)

fail=0

imports_of() {  # $1 = path
  grep -E '^import ' "$1" | awk '{print $2}'
}

for pin in "${PINS[@]}"; do
  f="${pin%%|*}"; want="${pin#*|}"
  if [ ! -f "$f" ]; then
    echo "check-trust-imports: missing pinned module $f" >&2
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
    echo "   and the headers/docs/demo/ pages that describe it)" >&2
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

is_closure_ok() {  # $1 = module name
  local m="$1" p
  for p in "${DEMO_CLOSURE_OK[@]}"; do [ "$m" = "$p" ] && return 0; done
  return 1
}

closure_check() {  # $1 = start module, $2 = human label
  local start="$1" label="$2"
  declare -A seen=()
  declare -A parent=()
  local queue=("$start") m path via chain
  while [ "${#queue[@]}" -gt 0 ]; do
    m="${queue[0]}"; queue=("${queue[@]:1}")
    path="${m//.//}.lean"
    [ -f "$path" ] || continue          # external package (e.g. Batteries)
    while IFS= read -r imp; do
      [ -n "${seen[$imp]:-}" ] && continue
      seen["$imp"]=1
      parent["$imp"]="$m"
      if [ -f "${imp//.//}.lean" ] && ! is_closure_ok "$imp"; then
        via="$imp"; chain="$imp"
        while [ -n "${parent[$via]:-}" ] && [ "${parent[$via]}" != "$start" ]; do
          via="${parent[$via]}"; chain="$via -> $chain"
        done
        echo "DEMO CLOSURE BROKEN: $label reaches $imp" >&2
        echo "  via: $start -> $chain" >&2
        echo "  (the demo trust base may reach the value/semantic core" >&2
        echo "   ONLY — see DEMO_CLOSURE_OK in this script)" >&2
        echo "  (first offender only — the rest of that subtree follows)" >&2
        fail=1
        return 0
      fi
      queue+=("$imp")
    done < <(imports_of "$path")
  done
}

closure_check ACL2Lean.Demo.Sorting.TCB \
  "TCB.lean (the definitions)"
closure_check ACL2Lean.Demo.Sorting.AclSource \
  "AclSource.lean (the ACL2 transcripts)"
closure_check ACL2Lean.Demo.Sorting.Assumptions \
  "Assumptions.lean (the assumed facts)"

# (3) the arrow: machinery imports the demo, never the reverse.
while IFS= read -r f; do
  [ "$f" = "$DEMO/Statements.lean" ] && continue
  while IFS= read -r imp; do
    if is_forbidden "$imp"; then
      echo "REVERSE ARROW: $f imports replay machinery ($imp)" >&2
      echo "  (machinery imports the demo folder, never the other way;" >&2
      echo "   Statements.lean is the sole exception and is pinned)" >&2
      fail=1
    fi
  done < <(imports_of "$f")
done < <(find "$DEMO" -name '*.lean' | sort)

if [ "$fail" -ne 0 ]; then
  echo "check-trust-imports: FAILED (see above)." >&2
  exit 1
fi
echo "check-trust-imports: layer pins hold; the demo trust base \
(TCB/AclSource/Assumptions) reaches the value core ONLY — no Replay \
module, no proof log, no driver."
