#!/usr/bin/env bash
# Hardening G2: every corpus .proof-log must carry a provenance sidecar
# (<log>.meta, written by capture-proof-log.sh) whose acl2-commit matches the
# CURRENT acl2/ submodule HEAD. This makes two silent-staleness classes loud:
#   - logs captured with an OLD image after the fork moved (incident I1/I3);
#   - PARTIAL recaptures (some logs refreshed, others stale — incident I2).
# Static (no build); runs in `just ci`.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
HEAD="$(git -C "$ROOT/acl2" rev-parse HEAD)"

fail=0
count=0
while IFS= read -r log; do
  count=$((count + 1))
  meta="$log.meta"
  if [ ! -f "$meta" ]; then
    echo "MISSING sidecar: $meta (recapture: just recapture-all)" >&2
    fail=1
    continue
  fi
  commit="$(sed -n 's/^acl2-commit: //p' "$meta")"
  case "$commit" in
    *-dirty)
      # S2 audit F5: a "-dirty" stamp means the image was built from
      # UNCOMMITTED fork edits — the log's true origin is unrecorded.
      echo "DIRTY-TREE log: $log — captured from an uncommitted acl2 tree ($commit); commit the fork, rebuild, and recapture" >&2
      fail=1
      continue;;
  esac
  if [ "$commit" != "$HEAD" ]; then
    echo "STALE log: $log — captured at acl2 commit ${commit:-<none>}, submodule HEAD is $HEAD (recapture: just recapture-all)" >&2
    fail=1
  fi
  # BANNER cross-check (audit 2026-08-03 F8): the log's own ACL2 banner
  # records the commit the IMAGE was built from; the meta stamp records the
  # tree at CAPTURE time. A skew means the image predates the stamped commit
  # ("build → commit → recapture" defeated the dirty-tree guard once, by
  # 33 seconds). The banner commit must equal the meta stamp.
  # FAIL-CLOSED (fresh-verify N5): a log with NO banner commit can't be
  # cross-checked — reject it rather than skip (every healthy capture
  # starts with the ACL2 banner; its absence means a truncated/foreign log).
  banner="$(sed -n 's/.*(Git commit hash: \([0-9a-f]\{40\}\)).*/\1/p' "$log" | head -1)"
  if [ -z "$banner" ]; then
    echo "NO-BANNER log: $log — no '(Git commit hash: …)' banner line; truncated or non-capture file (recapture: just recapture-all)" >&2
    fail=1
  elif [ "$banner" != "$commit" ]; then
    echo "IMAGE-SKEW log: $log — image built from $banner but meta stamped $commit (rebuild the image AFTER committing, then recapture)" >&2
    fail=1
  fi
done < <(find "$ROOT/acl2_samples" -name '*.proof-log' | sort)

if [ "$count" -eq 0 ]; then
  echo "check-log-provenance: found NO .proof-log files under acl2_samples — corpus missing?" >&2
  exit 1
fi

if [ "$fail" -ne 0 ]; then
  echo "check-log-provenance: FAILED — stale or unstamped logs (see above)." >&2
  exit 1
fi
echo "check-log-provenance: $count log(s) all stamped at submodule HEAD ${HEAD:0:12}."
