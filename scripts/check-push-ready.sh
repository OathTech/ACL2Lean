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

# REMOTE CI conclusion (audit 2026-07-26 F0: remote CI was RED for four
# merges while every close-out reported the LOCAL `just ci` as "gates
# green" — the local/remote split was invisible because the local run IS
# green after a developer recapture-all). A push is not ready unless the
# remote gate suite passed on the current main. HARD requirement: no gh /
# no network / no run found all fail closed.
#
# Escape hatch — ONLY for pushing the commit that fixes a red CI itself
# (chicken-and-egg): ALLOW_RED_CI=1 scripts/check-push-ready.sh
if [ "${ALLOW_RED_CI:-0}" = "1" ]; then
  echo "check-push-ready: ALLOW_RED_CI=1 — SKIPPING the remote CI check" >&2
  echo "  (only valid for pushing a CI fix itself)" >&2
  exit 0
fi
command -v gh >/dev/null 2>&1 \
  || { echo "check-push-ready: gh CLI not found — cannot verify the remote CI conclusion (fail-closed; install gh or use ALLOW_RED_CI=1 for a CI-fix push)" >&2; exit 1; }
conclusion=$(gh run list --repo septract/ACL2Lean --branch main --limit 1 \
               --json conclusion --jq '.[0].conclusion' 2>/dev/null) \
  || { echo "check-push-ready: gh query failed — cannot verify the remote CI conclusion (fail-closed)" >&2; exit 1; }
if [ "$conclusion" = "success" ]; then
  echo "check-push-ready: remote CI on main is GREEN — safe to push."
else
  echo "check-push-ready: remote CI on main concluded '${conclusion:-<none>}' — NOT green." >&2
  echo "  Fix CI before pushing anything else onto it (see the 2026-07-26 audit F0)." >&2
  echo "  Pushing the CI FIX itself: ALLOW_RED_CI=1 scripts/check-push-ready.sh" >&2
  exit 1
fi
