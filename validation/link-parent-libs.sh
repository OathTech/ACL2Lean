#!/usr/bin/env bash
# Regenerates .parent-lean-path if absent, then symlinks every
# top-level entry of the parent ACL2Lean workspace's Lean
# library dirs (LEAN_PATH as printed by `lake env printenv LEAN_PATH` in
# the parent) into this validation workspace's .lake/build/lib/lean, so
# that plain `lake build Solution` — including the comparator's
# sandboxed one — resolves the project imports WITHOUT a lake `require`
# (which would trigger rebuilds inside the parent tree). Read-only
# toward the parent: symlinks only. Idempotent.
set -euo pipefail
VAL_DIR="$(cd "$(dirname "$0")" && pwd)"
LIB="$VAL_DIR/.lake/build/lib/lean"
mkdir -p "$LIB"
if [ ! -f "$VAL_DIR/.parent-lean-path" ]; then
  (cd "$VAL_DIR/.." && lake env printenv LEAN_PATH) > "$VAL_DIR/.parent-lean-path"
fi
tr ':' '\n' < "$VAL_DIR/.parent-lean-path" | while read -r dir; do
  [ -d "$dir" ] || continue
  # skip the toolchain dir (lean finds it itself)
  case "$dir" in "$HOME"/.elan/*) continue;; esac
  for entry in "$dir"/*; do
    name="$(basename "$entry")"
    case "$name" in Challenge*|Solution*) continue;; esac
    if [ "$name" = "ACL2Lean" ] && [ -d "$entry" ]; then
      # The challenge builds its OWN byte-identical copies of the
      # ACL2Lean.Mirrors.* spec modules (module names must match the
      # project's — private auxiliary names embed the module name), so
      # the ACL2Lean tree must be REAL DIRECTORIES on the write path:
      # symlinking the whole dir would let lake write through the
      # symlink into the parent tree.
      mkdir -p "$LIB/ACL2Lean/Mirrors"
      for sub in "$entry"/*; do
        subname="$(basename "$sub")"
        case "$subname" in Mirrors) continue;; esac
        [ -e "$LIB/ACL2Lean/$subname" ] || ln -s "$sub" "$LIB/ACL2Lean/$subname"
      done
      # NOTE: nothing from the parent's Mirrors dir is linked — the
      # local copies shadow it for every module loaded in this
      # workspace, including the parent's compiled MirrorProofs oleans.
      continue
    fi
    [ -e "$LIB/$name" ] || ln -s "$entry" "$LIB/$name"
  done
done
