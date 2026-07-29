# Book manifest: lists all ACL2 files to translate and test
books := "acl2_samples/books.txt"

# Build the Lean project
build:
    lake build

# Run tests
test:
    lake build Tests

# Preflight: verify every include_str'd proof-log exists (the corpus is
# gitignored — this fails loudly and locally with a fix hint BEFORE the opaque
# Lean "no such file" error, and catches a stale local copy masking a
# corpus/CI desync). Runs first in `ci`.
check-proof-logs:
    ./scripts/check-proof-logs.sh

# Cross-check the canonical fidelity-bug index (docs/BUGS.md) against the
# self-enforcing differential corpus, so a logged bug can't rot in prose or be
# silently dropped. Static (no ACL2/Lean build needed), so it runs in `ci`.
check-bugs:
    ./scripts/check-bugs.sh

# NO-SHADOW gate (D3/D2): builtinNames (the ground-zero world-entry
# exclusion set) must stay in sync with callBuiltin's match arms — a
# builtin-named snapshot entering the world would shadow the builtin.
# Static source scrape; runs in `ci`.
check-no-shadow:
    ./scripts/check-no-shadow.sh

# Full conformance: preflight + build + unit tests + driver-coverage (the last
# gates on reconstruction integrity AND the black-box-leaf emission frontier —
# see docs/plans/2026-06-09_direct-proof-emission.md). driver-coverage
# include_str's the gitignored .proof-log corpus; check-proof-logs runs first
# so a missing log is a clear error, not a deep elaboration-trace failure.
ci: lint-sh check-bugs check-no-shadow check-acl2-tags check-dark-files check-proof-logs check-log-provenance check-pattern-map build test driver-coverage

# Run the corpus report
report:
    lake exe acl2lean report

# Evaluate an expression in the context of a file
eval-in file expr:
    lake exe acl2lean eval-in {{file}} "{{expr}}"

# Generate a World definition from an ACL2 file
gen-world file:
    lake exe acl2lean gen-world {{file}}

# Build ACL2 from the submodule. Hard-fails unless make actually produced a
# fresh image: ACL2's make can exit 0 through wrapper layers while the build
# failed (hardening G1 — a stale saved_acl2 then silently poisons every
# recapture), so we require the success marker AND a refreshed image file.
build-acl2:
    #!/usr/bin/env bash
    set -euo pipefail
    stamp=$(mktemp)
    out=$(mktemp)
    trap 'rm -f "$stamp" "$out"' EXIT
    # --no-sysinit keeps the build hermetic in the sandbox (/etc/sbclrc is
    # unreadable there — the same flag capture-proof-log.sh already passes)
    ( cd acl2 && make LISP="sbcl --no-sysinit" ) 2>&1 | tee "$out"
    grep -q "Successfully built .*saved_acl2" "$out" \
      || { echo "build-acl2: success marker missing — ACL2 build FAILED (read acl2/make.log)" >&2; exit 1; }
    [ acl2/saved_acl2 -nt "$stamp" ] \
      || { echo "build-acl2: acl2/saved_acl2 was NOT refreshed — stale image" >&2; exit 1; }

# FOCUSED replay (the fast OODA loop): one book — optionally stopping after
# THM — at runtime, from a .proof-log on disk. Row text identical to the
# coverage sweep's; the full sweep (driver-coverage) remains the gate.
replay file thm="":
    lake build acl2lean-replay
    lake env .lake/build/bin/acl2lean-replay {{file}} {{thm}}

# Capture structured proof log for a single file
capture-proof-log file:
    ./scripts/capture-proof-log.sh {{file}}

# Capture proof logs for all books in the manifest. Sources live in the acl2/
# submodule; OUTDIR keeps the captured logs in acl2_samples/sorting/ so the
# submodule tree stays clean.
capture-all-logs:
    OUTDIR=acl2_samples/sorting ./scripts/capture-proof-log.sh $(grep -v '^\s*#' {{books}} | grep -v '^\s*$')

# Recapture the WHOLE log surface (hardening G4): sorting corpus +
# recon-tests + simple, in one shot — a PARTIAL recapture after a fork
# change leaves stale logs that check-log-provenance then rejects
# (incident I2: sorting recaptured, recon-tests stale, caught only by
# luck). This is the one target agents should reach for after any
# instrumentation change.
recapture-all: capture-all-logs
    ./scripts/capture-proof-log.sh acl2_samples/simple.lisp acl2_samples/recon-tests/*.lisp acl2_samples/pattern-tests/*.lisp

# STRUCTURAL golden review (hardening G3): classify golden→actual changes
# into STATUS FLIPS (review first) vs message-only churn, so a regression
# can't hide in an error-text wall. The ci gate stays byte-exact; this is
# the review lens for promotions.
golden-review:
    bash scripts/golden-diff.sh

# Pre-push guard: the acl2 submodule pointer must be reachable from the
# fork REMOTE before any superproject push (2026-07-21 incident: main
# pushed with the fork 3 commits unpushed — GitHub CI "not our ref").
# Network (fetches the fork remote); run manually before pushing.
check-push-ready:
    bash scripts/check-push-ready.sh

# Mapping-arc gate: the pattern map is a gated artifact (bidirectional
# book<->map + logs present + pin signatures) — the check-bugs.sh pattern.
check-pattern-map:
    bash scripts/check-pattern-map.sh

# Provenance gate (hardening G2): every corpus log's sidecar must be
# stamped at the CURRENT acl2 submodule HEAD (stale/partial recaptures
# fail loudly). Static; runs in `ci`.
check-log-provenance:
    bash scripts/check-log-provenance.sh

# Parse and display a proof log
parse-proof-log file:
    lake exe acl2lean parse-proof-log {{file}}

# Run the replay driver over the whole sample corpus; prints REPLAYED-vs-frontier per
# theorem. Hard-fails if any proof-log is absent (regenerate with capture-all-logs first).
driver-coverage:
    lake build Tests.DriverCoverage

# Dark-file gate (audit F2/F9): every tracked .lean reachable from a build root.
check-dark-files:
    bash scripts/check-dark-files.sh

# Verify the ACL2 instrumentation tagging convention (namespaced TRACE-LOG, round-trip).
check-acl2-tags:
    bash scripts/check-acl2-tags.sh

# Differential test: the Lean ACL2-logic interpreter vs real ACL2, over the
# Tests/differential/ corpus (see its README). Feeds the same ACL2 forms to
# both interpreters and diffs the value streams. Needs acl2/saved_acl2
# (just build-acl2). Pass corpus file paths to run a subset.
diff-test *files:
    bash scripts/diff-test.sh {{files}}

# Lint the shell scripts (portability + robustness). Config in .shellcheckrc.
# Skips gracefully if shellcheck is not installed, so `ci` never hard-fails on
# a missing dev tool — CI installs it explicitly.
lint-sh:
    #!/usr/bin/env bash
    set -euo pipefail
    if ! command -v shellcheck >/dev/null 2>&1; then
      echo "shellcheck not installed — skipping (install: brew install shellcheck)"
      exit 0
    fi
    shellcheck scripts/*.sh
    echo "shellcheck: all scripts clean"
