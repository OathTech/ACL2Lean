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
| `08-equality-reasoning.lisp` | Equality stepping stones toward transitivity; `:rule-classes nil` theorems (not stored as `:REWRITE`) |
| `09-defn-unfold.lisp` | Non-inductive definition unfold then close — the `def-unfold` rune with no induction |
| `10-tree-induction.lisp` | Binary-tree recursion → a step case with **two IHs** (one per recursive call); multi-`:ALISTS` per case |
| `11-custom-measure.lisp` | An explicit **non-`acl2-count` measure** (`nfix n`) inducted on; step substitutes `n := (- n 2)` |
| `12-multi-controller.lisp` | Simultaneous recursion on two args → **multiple `:CONTROLLERS`**; multi-variable IH alist |
| `13-multi-measured-var.lisp` | A **compound measure over two vars** (`(+ (acl2-count x) (acl2-count y))`); the IH *swaps* variables |
| `14-accumulator.lisp` | Tail-recursive accumulator: an IH substitution to a **constructed (growing)** term; controller + non-controller substituted together |
| `15-nested-induction.lisp` | **Two inductions in one theorem** — a nested/sequential induction with a synthesized `*1.k` pool root |
| `16-three-way.lisp` | Three-way simultaneous recursion → a **3-element IH alist** and a 3-disjunct governing test |
| `17-rule-application.lisp` | **Theorem dependency** (`rule:<thm>`): citing a prior theorem as a `:REWRITE` rule; `(:RULES …)` emission, `:SUBST`, and `:HYP-RELIEF` |

## Regenerate

```sh
just build-acl2                       # only if the ACL2 image is stale
./scripts/recon-test-dump.sh          # capture .proof-log + .dump for every file here
```

Each run writes `<file>.proof-log` (raw structured log) and `<file>.dump`
(reconstructed tree as rendered by `dump-proof-tree`) alongside the source.
