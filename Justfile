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
ci: lint-sh check-bugs check-no-shadow check-proof-logs build test driver-coverage

# Run the corpus report
report:
    lake exe acl2lean report

# Evaluate an expression in the context of a file
eval-in file expr:
    lake exe acl2lean eval-in {{file}} "{{expr}}"

# Generate a World definition from an ACL2 file
gen-world file:
    lake exe acl2lean gen-world {{file}}

# Build ACL2 from the submodule
build-acl2:
    cd acl2 && make LISP=sbcl

# Capture structured proof log for a single file
capture-proof-log file:
    ./scripts/capture-proof-log.sh {{file}}

# Capture proof logs for all books in the manifest. Sources live in the acl2/
# submodule; OUTDIR keeps the captured logs in acl2_samples/sorting/ so the
# submodule tree stays clean.
capture-all-logs:
    OUTDIR=acl2_samples/sorting ./scripts/capture-proof-log.sh $(grep -v '^\s*#' {{books}} | grep -v '^\s*$')

# Parse and display a proof log
parse-proof-log file:
    lake exe acl2lean parse-proof-log {{file}}

# Run the replay driver over the whole sample corpus; prints REPLAYED-vs-frontier per
# theorem. Hard-fails if any proof-log is absent (regenerate with capture-all-logs first).
driver-coverage:
    lake build Tests.DriverCoverage

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
