# Book manifest: lists all ACL2 files to translate and test
books := "acl2_samples/books.txt"

# Build the Lean project
build:
    lake build

# Run tests
test:
    lake build Tests

# Full conformance: build + unit tests + translate all books + verify
ci: build test translate-all

# Run the corpus report
report:
    lake exe acl2lean report

# Verify evaluator against ACL2
verify:
    python3 Verify.py

# Translate a single ACL2 file to Lean
translate file:
    lake exe acl2lean translate {{file}}

# Evaluate an expression in the context of a file
eval-in file expr:
    lake exe acl2lean eval-in {{file}} "{{expr}}"

# Translate all books listed in the manifest and verify
translate-all:
    ./scripts/translate-book.sh $(grep -v '^\s*#' {{books}} | grep -v '^\s*$') --verify

# Translate a directory of ACL2 files
translate-dir dir:
    ./scripts/translate-book.sh {{dir}} --verify

# Build ACL2 from the submodule
build-acl2:
    cd acl2 && make LISP=sbcl

# Capture structured proof log for a single file
capture-proof-log file:
    ./scripts/capture-proof-log.sh {{file}}

# Capture proof logs for all books in the manifest
capture-all-logs:
    ./scripts/capture-proof-log.sh $(grep -v '^\s*#' {{books}} | grep -v '^\s*$')

# Parse and display a proof log
parse-proof-log file:
    lake exe acl2lean parse-proof-log {{file}}
