# ACL2Lean

**Replaying ACL2 proofs as kernel-checked Lean 4 proofs.**

ACL2Lean imports theorems from [ACL2](https://www.cs.utexas.edu/users/moore/acl2/)
into Lean 4 with the **Lean kernel as the sole trust anchor**: ACL2 acts as an
untrusted proof-search oracle, and every imported result is re-certified by a
Lean proof object that *mirrors ACL2's own proof* — the actual clause tree its
waterfall produced, replayed step by step. Genuine, faithful replay is the
product: a proof that passes the kernel but does not mirror ACL2's reasoning
does not count here.

## How it works

Importing a theorem runs through a pipeline; every stage except ACL2's own
proof search is this repo's code:

1. **ACL2 source** — a `.lisp` file of `defun`s and `defthm`s; ACL2 searches
   for proofs (untrusted oracle).
2. **Instrumented ACL2** — the `acl2/` submodule (branch `acl2-lean-output`)
   adds logging to ACL2's rewriter/simplifier that emits a structured
   **proof log**: runes, rewrite steps, substitutions, induction schemes,
   type-prescription corollaries, decision-procedure discharge nodes. Every
   inserted region carries a `TRACE-LOG[...]` tag (`just check-acl2-tags`
   enforces the convention).
3. **Proof-log parser** (`ACL2Lean/ProofLog.lean`) — log text → structured
   trace events.
4. **Proof-tree reconstruction** (`ACL2Lean/ClauseTree.lean`,
   `ACL2Lean/ProofTree.lean`) — events → a single proof tree for the whole
   development: the clause tree ACL2's waterfall actually is, with per-literal
   rewriter detail. Unlinkable structure hard-fails.
5. **Source translation** (`ACL2Lean/WorldGen.lean`,
   `ACL2Lean/Translator.lean`) — the same ACL2 source → a Lean `World`
   (function definitions) and the **mirror-theorem statement**: that the
   formula is eventually *true* in ACL2's sense — `∃ N, ∀ f ≥ N, ∃ v,
   evalOpt f world env <formula> = some v ∧ v ≠ nil` (truthiness, not
   exact-`t`; non-`nil` is ACL2's notion of truth).
6. **ACL2-logic interpreter** (`ACL2Lean/EvalOpt.lean`,
   `ACL2Lean/Logic.lean`) — the fuel-bounded semantic model that defines what
   the mirror theorem means (differential-tested against real ACL2).
7. **Proof replay** (`ACL2Lean/Replay/Driver.lean`,
   `ACL2Lean/Replay/EvalLemmas.lean`) — recurses the reconstructed tree and
   emits a Lean proof object for the mirror theorem, node by node; the Lean
   kernel checks it. The replay does **no inference**: if the tree lacks the
   information to replay a step, the fix is more instrumentation at the ACL2
   source, never a heuristic in Lean. The sole ratified exception is
   decision-procedure *leaves* (clauses ACL2 itself closes by a verdict-only
   procedure), which are discharged by a kernel-checked decision procedure on
   the precisely-stated leaf obligation.
8. **Native bridge** (`ACL2Lean/Imported/`) — the mirror theorem is decoded
   into a *native Lean statement* (e.g. `(xs ++ ys).length = xs.length +
   ys.length`), so the imported fact is usable as an ordinary Lean theorem.
   `Imported/Lifting.lean` is the lifting library: representations of Lean
   types in ACL2's value space (`Rep`, with ACL2 recognizers as the type
   discipline), correspondences between ACL2 functions and Lean operations
   (`Implements`), and the generic decode lemmas. `Imported/NativeMirrors.lean`
   is the catalog of native theorems proved end-to-end through the driver —
   its header scoreboard is the live status.

## Trust model

The kernel certifies the proof object *for the mirror theorem exactly as
stated by stages 5–6*. Until a native-theorem bridge exists for a given
result, a bug in stages 2–6 could yield a kernel-accepted proof of a subtly
wrong statement — so each stage is validated against the real artifacts
(differential testing of the interpreter, log↔tree fidelity checks,
adversarial audits). Once a result is decoded to a native Lean statement, the
entire ACL2 pipeline becomes untrusted for it: a bug anywhere makes the
composed proof fail to typecheck; it can never certify a false native theorem.

## Getting started

**Prerequisites.** [Lake + the pinned Lean toolchain](lean-toolchain)
(installed automatically by [`elan`](https://github.com/leanprover/elan)),
[`just`](https://github.com/casey/just) for the convenience recipes, and a
Common Lisp (SBCL is what the build uses) to build the instrumented ACL2.

**Clone with the submodule** (the `acl2/` fork is required):

```sh
git clone --recursive https://github.com/septract/ACL2Lean.git
# or, in an existing clone:  git submodule update --init --recursive
```

**Important — proof logs are a build input.** The Lean sources embed proof
logs at compile time (`include_str`), and the logs (`acl2_samples/**/*.proof-log`)
are *gitignored generated artifacts*. A fresh clone therefore will **not**
`lake build` until the logs are generated. Build the instrumented ACL2 once,
then capture the logs:

```sh
# 1. Build the instrumented ACL2 (SBCL + a full ACL2 build — this is slow)
just build-acl2

# 2. Regenerate the compile-critical proof logs. This uses only the ACL2
#    image, no Lean — so it avoids the build bootstrap cycle.
./scripts/capture-proof-log.sh acl2_samples/simple.lisp acl2_samples/recon-tests/*.lisp

# 3. Fetch the prebuilt mathlib cache (otherwise lake builds mathlib from
#    source, which takes hours), then build.
lake exe cache get
lake build
```

`just capture-all-logs` additionally recaptures the larger `books.txt` corpus
(needed for the full coverage sweep); it is not required just to build.

## Building and commands

The toolchain is pinned in `lean-toolchain`; build with
[Lake](https://github.com/leanprover/lean4/tree/master/src/lake) and
[just](https://github.com/casey/just):

```sh
lake build                              # type-check everything (incl. tests)
just test                               # unit tests
just ci                                 # conformance gate: build + tests + driver coverage
just driver-coverage                    # replay the driver over the whole sample corpus
lake exe acl2lean dump-proof-tree <f>   # inspect a reconstructed proof tree
lake exe acl2lean parse-proof-log <f>   # parse/display a raw proof log
lake exe acl2lean gen-world <file>      # generate World + theorem stubs from .lisp
lake exe acl2lean eval "<expr>"         # evaluate an s-expression
```

If a build fails with a missing-`.proof-log` error, regenerate the logs as in
*Getting started* above (the capture script force-invalidates the Lean modules
that embed them, so there is no silent staleness).

## Repository layout

| Path | Contents |
| --- | --- |
| `acl2/` | The instrumented ACL2 fork (submodule, branch `acl2-lean-output`) |
| `ACL2Lean/` | Parser, s-expression core, interpreter, translator |
| `ACL2Lean/Replay/` | The replay driver and its atomic evaluation lemmas |
| `ACL2Lean/Imported/` | The lifting library and the native mirror catalog |
| `Tests/` | Unit tests, driver tests, the corpus-wide coverage harness |
| `acl2_samples/` | The sample corpus (`recon-tests/` is the reconstruction suite) |
| `docs/plans/` | Design plans — `2026-06-10_generality-design.md` is the governing plan |
| `docs/notes/` | Investigation notes and surveys |
| `TODO.md` | The running backlog across all tracks |
| `CLAUDE.md` | The working rules (fidelity requirements, audit practices) |

## Status & limitations

**This is a research prototype.** The architecture is validated end-to-end —
proof logs are parsed and reconstructed into the real clause tree, whole
theorems (including well-founded induction with induction hypotheses,
preprocess/clausify composition, and decision-procedure leaves) replay into
kernel-checked Lean proof objects, and a catalog of results is decoded to
native Lean statements. What remains is *breadth*, and the frontiers are
enumerable rather than open-ended.

Concretely, on the sample corpus the driver fully replays a subset of
theorems; every theorem it cannot yet replay stops at a **named frontier**
(an explicit `throwError`, never a silent skip or a `sorry`) that maps to a
specific backlog item. The largest open area is **induction generality**
(multi-literal pushed clauses, multiple induction hypotheses, multi-variable
and non-`acl2-count` measures, merged/mutual schemes). Other frontiers:
previously-proved theorems used as rewrite rules, some `:use`/`:induct` hint
shapes, and a handful of decision-procedure leaves awaiting an SMT backend.

Beyond the corpus, the **translator** (stage 5) currently handles
`defun`/`defthm`/`mutual-recursion`; `encapsulate`, `include-book`,
`defconst`, macros, and guard verification are not yet supported, so the
larger ACL2 books in `acl2_samples/` are aspirational targets, not passing
imports. The intended scope (a CORE tier targeting roughly the Milawa
fragment plus the ratified decision-procedure carve-out, with EXTENDED and
OUT tiers) is set out in `docs/plans/2026-06-10_generality-design.md`.

**Live status lives in the repo, not here:** the scoreboard at the top of
`ACL2Lean/Imported/NativeMirrors.lean` lists the native theorems proved
through the driver (each a build-enforced regression), the coverage table
from `just driver-coverage` reports per-theorem replay status over the whole
corpus, and `TODO.md` tracks the frontiers.

## License

BSD 3-Clause — see [LICENSE](LICENSE). Copyright (c) The ACL2Lean Authors.
(The `acl2/` submodule is upstream ACL2 plus our instrumentation and carries
its own license — see `acl2/LICENSE`.)
