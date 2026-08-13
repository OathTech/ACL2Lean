# ACL2Lean

**Replaying ACL2 proofs as kernel-checked Lean 4 proofs.**

ACL2Lean imports theorems from [ACL2](https://www.cs.utexas.edu/users/moore/acl2/)
into Lean 4 with the **Lean kernel as the sole trust anchor**: ACL2 acts as an
untrusted proof-search oracle, and every imported result is re-certified by a
Lean proof object that *mirrors ACL2's own proof* — the actual clause tree its
waterfall produced, replayed step by step. Genuine, faithful replay is the
product: a proof that passes the kernel but does not mirror ACL2's reasoning
does not count here.

**The words matter here** — *replayed statement* (the metric's unit),
*waypoint* (ACL2-like Lean, the scoreboard, never a result), and
*mirror* (the product: pure Lean theorems, zero ACL2 notions) name
three different things: see [`docs/LEXICON.md`](docs/LEXICON.md).

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
5. **Statement derivation** — the stage that decides *what theorem we are
   proving*. **As wired today this is the PROOF-LOG path** (audit
   2026-07-26 F5b): the certified `World` is `Development.toWorld` from
   the log's `:DEFUN` events and the replayed statement is truth of the
   log's root Goal clause — i.e. the statement comes from the same
   untrusted emission as the proof, anchored to the `.lisp` source by the
   sidecar source hashes and the hand statement pins.
   `ACL2Lean/WorldGen.lean` / `ACL2Lean/Translator.lean` translate the
   source directly and are the intended INDEPENDENT frontend, but they
   are NOT in the certified pipeline yet (tracked; the follow-on arc's
   statement-identity gate).
6. **ACL2-logic interpreter** (`ACL2Lean/EvalOpt.lean`,
   `ACL2Lean/Logic.lean`) — the fuel-bounded semantic model that defines what
   the replayed statement means (differential-tested against real ACL2).
7. **Proof replay** (`ACL2Lean/Replay/Driver.lean`,
   `ACL2Lean/Replay/EvalLemmas.lean`) — recurses the reconstructed tree and
   emits a Lean proof object for the replayed statement, node by node; the Lean
   kernel checks it. The replay does **no inference** as its governing
   rule: if the tree lacks the information to replay a step, the fix is
   more instrumentation at the ACL2 source, never a heuristic in Lean.
   Current deviations are EXPLICIT, not silent: the ratified
   decision-procedure *leaf* carve-out (clauses ACL2 itself closes by a
   verdict-only procedure, discharged by a kernel-checked decision
   procedure on the precisely-stated leaf obligation), and a small set of
   expiry-held mechanisms (marked `DRIFT MARKER` in
   `ACL2Lean/Replay/Driver/`, each retiring against a queued fork
   emission — see the 2026-08-05 branch drift audit).
8. **Waypoint decode** (`ACL2Lean/Imported/`) — the replayed statement is
   decoded into a **waypoint**: an ACL2-like Lean restatement (ACL2's own
   notions in Lean clothes — `SExpr` lists, `isortL`). A waypoint is part
   of the METRIC, the legible scoreboard of how far the machinery reaches;
   per `docs/LEXICON.md` it is **never a result** and is never presented as
   a top-level theorem. `Imported/Lifting.lean` is the lifting library:
   representations of Lean types in ACL2's value space (`Rep`, with ACL2
   recognizers as the type discipline), correspondences between ACL2
   functions and Lean operations (`Implements`), and the generic decode
   lemmas. The LIVE catalog is `liftCatalog` in
   `Imported/Waypoints/Catalog.lean` (one decision per green sweep row,
   enforced by build-failing coverage/seam/axiom/criterion gates);
   `Imported/WaypointCatalog.lean` is the module facade, and its header
   narrative covers only the first 18 entries (historical).
9. **Mirror** (`ACL2Lean/Mirrors/` + `ACL2Lean/MirrorProofs/`) — **the
   PRODUCT**, and the only stage whose output is a result: a Lean-idiomatic
   theorem with ZERO ACL2 notions (e.g. `(xs ++ ys).length = xs.length +
   ys.length`), mirroring a property an ACL2 book proves and proved VIA the
   replay, through the transfer kit (`mirror_iso%` / `mirror_transport%`).
   A user of a mirror knows nothing about ACL2 and never needs to;
   `just check-mirrors-pure` pins the layer's imports, and an ACL2 notion
   in a mirror is definitionally a bug. **Three mirrors are proved today** —
   `app_assoc_int`, `len_app_int`, `len_revAcc_int` (all at `Int`,
   trio-clean: axioms `{propext, Classical.choice, Quot.sound}`).

The pipeline in the project's own words (`docs/LEXICON.md`):
ACL2 book → proof log → **replayed statement** (metric) → **waypoint**
(metric, legible) → **mirror** (product).

## Trust model

Three DISTINCT properties, separately enforced (rewritten 2026-08-06 after
the overall-project audit — the earlier text conflated them):

1. **Lean logical soundness** — the declared Lean theorem follows from
   Lean's trusted basis plus its listed axioms (`propext`,
   `Classical.choice`, `Quot.sound`; the build-failing axiom gate). This
   one the kernel gives us outright: no pipeline bug can ever certify a
   FALSE Lean theorem.
2. **Statement authenticity** — the proved proposition really is the named
   ACL2 theorem (same formula, functions, scope, value universe). The
   kernel does NOT check this: a bug in instrumentation, parsing, world
   construction, or statement derivation can produce a kernel-accepted
   proof of a *different but true* statement presented under the intended
   name (BUG-019 was a concrete incident of exactly this class). Enforced
   instead by: source/include-closure hash provenance + fatal capture
   (`scripts/check-log-provenance.sh`), hand statement pins per book
   (the `Tests/*Pins*.lean` class — `Tests/SortingPins.lean`,
   `Tests/SortingPinsEndgame.lean`, `Tests/ParametricPins.lean`,
   `Tests/PatternPins.lean`), tamper tests, and adversarial audits.
3. **Replay fidelity** — the proof follows ACL2's recorded reasoning
   rather than a stronger Lean-side derivation. Enforced by the replay
   drivers' hard-fail frontiers, the waypoint criterion + seam gates
   (`Imported/Waypoints/Catalog.lean`), and the drift-test discipline.

A waypoint narrows the API surface a reader must trust to the native
statement itself, but does NOT retroactively make stages 2–6 irrelevant:
authenticity and fidelity remain separately-enforced invariants, and the
current deviations from perfection are explicit (the expiry-held
mechanisms marked `DRIFT MARKER` in the drivers, each retiring against a
queued fork emission; the ratified decision-procedure leaf carve-out).

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
| `ACL2Lean/Imported/` | The lifting library and the waypoint catalog |
| `Tests/` | Unit tests, driver tests, the corpus-wide coverage harness |
| `acl2_samples/` | Authored corpus sources (`recon-tests/` is the reconstruction suite) + captured logs; upstream books are referenced directly from the `acl2/` submodule (see `books.txt`) |
| `ACL2Lean/Mirrors/` | **The product layer**: pure Lean statements (specs), zero ACL2 notions — imports pinned by `just check-mirrors-pure` |
| `ACL2Lean/MirrorProofs/` | The mirror proofs + the transfer kit (`mirror_iso%` / `mirror_transport%`) that discharge them from replayed statements |
| `docs/plans/` | Design plans — `2026-08-12_master-plan.md` is the governing plan |
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
specific backlog item. Multi-literal pushed clauses, cross-product induction
schemes, pool subsumption, generalization, and previously-proved theorems
used as rewrite rules (replayed as conditional statements with `rule:<thm>`
hypotheses) all replay; the largest open areas are **induction-measure
generality** (multi-variable and non-`acl2-count` measures, merged/mutual
schemes), discharging the `rule:<thm>` hypotheses from their own replayed
statements, some `:use`/`:induct` hint shapes, and a handful of
decision-procedure leaves awaiting an SMT backend.

Beyond the corpus, the **translator** (stage 5) currently handles
`defun`/`defthm`/`mutual-recursion`; `encapsulate`, `include-book`,
`defconst`, macros, and guard verification are not yet supported, so the
larger ACL2 books in `acl2_samples/` are aspirational targets, not passing
imports. The intended scope (a CORE tier targeting roughly the Milawa
fragment plus the ratified decision-procedure carve-out, with EXTENDED and
OUT tiers) is set out in `docs/plans/2026-06-10_generality-design.md`
(the architecture reference — its L1–L3 invariants bind; its status and
sequencing are superseded by `docs/plans/2026-08-12_master-plan.md`, the
governing plan).

**Live status lives in the repo, not here:** `liftCatalog` in
`ACL2Lean/Imported/Waypoints/Catalog.lean` is the LIVE catalog (one entry
per green sweep row, enforced by build-failing coverage/seam/axiom/
criterion gates — the narrative header on `Imported/WaypointCatalog.lean`
is historical and covers only the first 18 entries, so do not read status
off it); `just driver-coverage` reports per-theorem replay status over the
whole corpus; `just waypoint-metrics` reports the ruled waypoint-layer
metrics (kept-condition census + hand lines per catalog native); and
`TODO.md` tracks the frontiers.

## License

BSD 3-Clause — see [LICENSE](LICENSE). Copyright (c) The ACL2Lean Authors.
(The `acl2/` submodule is upstream ACL2 plus our instrumentation and carries
its own license — see `acl2/LICENSE`.)
