# Book manifest: lists all ACL2 files to translate and test
books := "acl2_samples/books.txt"

# Build the Lean project
build:
    lake build

# Run tests
test:
    lake build Tests

# Full conformance: build + unit tests + driver-coverage (the latter gates on
# reconstruction integrity AND the black-box-leaf emission frontier — see
# docs/plans/2026-06-09_direct-proof-emission.md). driver-coverage include_str's the
# gitignored .proof-log corpus, so regenerate it first (scripts/recon-test-dump.sh)
# if a fresh checkout reports a missing-log compile error rather than the frontier.
ci: build test driver-coverage

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
