# Reconstruction feature-coverage tests

Small, targeted ACL2 proofs that each isolate one or more features, used to
review what the proof-log → proof-tree **reconstruction** captures, drops, or
mangles. These are NOT the trust anchor and NOT performance benchmarks — they
exist so we can audit the reconstruction output against a known source and find
fixes (the same exercise that produced the §D.1 if-simplification fix).

`*.proof-log` and `*.dump` are gitignored (regenerated from the ACL2 image).

| File | Feature(s) probed |
|------|-------------------|
| `00-direct.lisp` | Direct (no-induction) proofs; ground evaluation; the `"Goal"` clause that reconstruction filters out |
| `01-multi-theorem.lisp` | Several theorems per file; theorem separation; inductive/non-inductive mix |
| `02-rev.lisp` | Chained proofs consuming **prior user lemmas** as `:REWRITE` runes; cross-fertilization (rev-rev) |
| `03-linear.lisp` | Linear arithmetic + type-set reasoning (non-rewriter waterfall steps) |
| `04-multi-case-induction.lisp` | Induction with **>2 cases** (recursion on `cddr`); nested case splits |
| `05-hints.lisp` | Explicit `:hints` — `:use`, `:induct`, `:in-theory` provenance |
| `06-measure.lisp` | Explicit **`:measure`** / termination proofs (simple, lexicographic `l<`, structural) |
| `07-mutual-recursion.lisp` | `mutual-recursion` bundles; the induced mutual induction scheme |

## Regenerate

```sh
just build-acl2                       # only if the ACL2 image is stale
./scripts/recon-test-dump.sh          # capture .proof-log + .dump for every file here
```

Each run writes `<file>.proof-log` (raw structured log) and `<file>.dump`
(reconstructed tree as rendered by `dump-proof-tree`) alongside the source.
