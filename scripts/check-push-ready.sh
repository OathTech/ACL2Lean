#!/usr/bin/env bash
# Hardening (quality pass, 2026-07-21 — incident: superproject main pushed
# while the acl2 fork was 3 commits unpushed; GitHub CI died at submodule
# checkout with "not our ref"). Run BEFORE any superproject push: verifies
# the acl2 submodule pointer is reachable from the fork REMOTE, so a push
# can never publish a dangling submodule reference.
#
# Usage: scripts/check-push-ready.sh   (network: fetches the fork remote)

set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SUB="$ROOT/acl2"

ptr=$(git -C "$ROOT" ls-tree HEAD acl2 | awk '{print $3}')
[ -n "$ptr" ] || { echo "check-push-ready: no acl2 submodule pointer in HEAD" >&2; exit 1; }

git -C "$SUB" fetch --quiet origin
if git -C "$SUB" merge-base --is-ancestor "$ptr" \
     "$(git -C "$SUB" rev-parse origin/acl2-lean-output)" 2>/dev/null; then
  echo "check-push-ready: submodule pointer $ptr is on origin/acl2-lean-output — safe to push."
else
  echo "check-push-ready: submodule pointer $ptr is NOT reachable from" >&2
  echo "  origin/acl2-lean-output — push the fork FIRST:" >&2
  echo "  ( cd acl2 && git push origin acl2-lean-output )" >&2
  exit 1
fi
