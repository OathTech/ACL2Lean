# Book manifest: lists all ACL2 files to translate and test
books := "acl2_samples/books.txt"

# Build the Lean project
build:
    lake build

# Run tests
test:
    lake build Tests

# Full conformance: build + unit tests
ci: build test

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

# Capture proof logs for all books in the manifest
capture-all-logs:
    ./scripts/capture-proof-log.sh $(grep -v '^\s*#' {{books}} | grep -v '^\s*$')

# Parse and display a proof log
parse-proof-log file:
    lake exe acl2lean parse-proof-log {{file}}
