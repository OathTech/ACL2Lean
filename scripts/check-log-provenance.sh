#!/usr/bin/env bash
# Hardening G2: every corpus .proof-log must carry a provenance sidecar
# (<log>.meta, written by capture-proof-log.sh) whose acl2-commit matches the
# CURRENT acl2/ submodule HEAD. This makes two silent-staleness classes loud:
#   - logs captured with an OLD image after the fork moved (incident I1/I3);
#   - PARTIAL recaptures (some logs refreshed, others stale — incident I2).
# Static (no build); runs in `just ci`.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
# shellcheck source=lib-log-provenance.sh
. "$(dirname "$0")/lib-log-provenance.sh"
HEAD="$(git -C "$ROOT/acl2" rev-parse HEAD)"
# SCAN_ROOT: overridable for the negative-test harness
# (test-provenance-gates.sh points it at fixture corpora); defaults to
# the real corpus.
SCAN_ROOT="${SCAN_ROOT:-$ROOT/acl2_samples}"

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
  # SOURCE-IDENTITY cross-check (capstone-demo arc Phase 0, review-1
  # P0-1): the sidecar's source hash + include-closure hashes must match
  # the CURRENT tree — an edited book paired with an old log fails HERE,
  # locally, instead of certifying a proof about the old text. Missing
  # fields fail closed (recapture, or backfill-log-provenance.sh for the
  # one-time 2026-08-06 migration).
  sprov="$(sed -n 's/^source-provenance: //p' "$meta")"
  spath="$(sed -n 's/^source-path: //p' "$meta")"
  ssha="$(sed -n 's/^source-sha256: //p' "$meta")"
  case "$sprov" in
    captured|backfilled-2026-08-06) ;;
    *)
      echo "NO-SOURCE-PROVENANCE log: $log — sidecar lacks source-provenance (pre-2026-08-06 sidecar; recapture or run scripts/backfill-log-provenance.sh)" >&2
      fail=1; continue;;
  esac
  if [ -z "$spath" ] || [ -z "$ssha" ]; then
    echo "NO-SOURCE-IDENTITY log: $log — sidecar lacks source-path/source-sha256" >&2
    fail=1; continue
  fi
  if [ ! -f "$ROOT/$spath" ]; then
    echo "SOURCE-MISSING log: $log — sidecar names $spath which does not exist" >&2
    fail=1; continue
  fi
  if [ "$(sha256_of "$ROOT/$spath")" != "$ssha" ]; then
    echo "SOURCE-DRIFT log: $log — $spath has been EDITED since capture (hash mismatch); the log proves the OLD text (recapture: just recapture-all)" >&2
    fail=1
  fi
  while IFS=' ' read -r ipath isha _flag; do
    [ -n "$ipath" ] || continue
    if [ ! -f "$ROOT/$ipath" ]; then
      echo "INCLUDE-MISSING log: $log — included book $ipath does not exist" >&2
      fail=1
    elif [ "$(sha256_of "$ROOT/$ipath")" != "$isha" ]; then
      echo "INCLUDE-DRIFT log: $log — included book $ipath edited since capture (hash mismatch)" >&2
      fail=1
    fi
  done < <(sed -n 's/^include: //p' "$meta")
  # COMPLETENESS re-verification (review-1 P0-2, static half): the same
  # QED-per-DEFTHM/source-count invariant the capture script now enforces
  # fatally, recomputed in ci so a truncated log cannot survive however
  # it arrived.
  if ! msg="$(check_capture_complete "$ROOT/$spath" "$log")"; then
    echo "TRUNCATED log: $log — $msg" >&2
    fail=1
  fi
done < <(find "$SCAN_ROOT" -name '*.proof-log' | sort)

if [ "$count" -eq 0 ]; then
  echo "check-log-provenance: found NO .proof-log files under acl2_samples — corpus missing?" >&2
  exit 1
fi

if [ "$fail" -ne 0 ]; then
  echo "check-log-provenance: FAILED — stale or unstamped logs (see above)." >&2
  exit 1
fi
echo "check-log-provenance: $count log(s) all stamped at submodule HEAD ${HEAD:0:12}."
