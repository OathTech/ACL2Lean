# ACL2Lean — technical overview

**Replaying ACL2 proofs as kernel-checked Lean 4 proofs.**

ACL2Lean imports theorems from [ACL2](https://www.cs.utexas.edu/users/moore/acl2/)
into Lean 4 with the **Lean kernel as the sole trust anchor**: ACL2 acts as an
untrusted proof-search oracle, and every imported result is re-certified by a
Lean proof object that *mirrors ACL2's own proof* — the actual clause tree its
waterfall produced, replayed step by step. Genuine, faithful replay is the
product: a proof that passes the kernel but does not mirror ACL2's reasoning
does not count here.

This document is the technical entry point: the pipeline, the trust model, the
product layer, how to build and reproduce, and what the system cannot yet do.
The root [`README.md`](../README.md) is the short front page;
[`CLAUDE.md`](../CLAUDE.md) is the binding working rules.

**The words matter here.** *Replayed statement* (the metric's unit), *waypoint*
(ACL2-like Lean, the scoreboard, never a result), and *mirror* (the product:
pure Lean theorems, zero ACL2 notions) name three different things — see
[`LEXICON.md`](LEXICON.md), which is canonical and wins where a dated document
conflicts with it.

Paths in prose are repo-root-relative; markdown links are relative to this
file's location in `docs/`.

## The pipeline

Importing a theorem runs through nine stages. **Every stage except ACL2's own
proof search is this repository's code**, and can contain bugs.

1. **ACL2 source** — a `.lisp` file of `defun`s and `defthm`s; ACL2 searches
   for proofs (untrusted oracle).
2. **Instrumented ACL2** — the `acl2/` submodule (branch `acl2-lean-output`)
   adds logging to ACL2's rewriter/simplifier that emits a structured
   **proof log**: runes, rewrite steps, substitutions, induction schemes,
   type-prescription corollaries, decision-procedure discharge nodes. Every
   inserted region carries a `TRACE-LOG[...]` tag; `just check-acl2-tags`
   enforces the convention, so the whole delta against upstream ACL2 is
   greppable.
3. **Proof-log parser** (`ACL2Lean/ProofLog.lean`) — log text → structured
   trace events.
4. **Proof-tree reconstruction** (`ACL2Lean/ClauseTree.lean`,
   `ACL2Lean/ProofTree.lean`) — events → a single proof tree for the whole
   development: the clause tree ACL2's waterfall actually is, with per-literal
   rewriter detail hanging off the simplification nodes. Linking is
   deterministic and unlinkable structure hard-fails.
5. **Statement derivation** — the stage that decides *what theorem the replay
   discharges*. **As wired today this is the PROOF-LOG path** (audit
   2026-07-26 F5b): the certified `World` is `Development.toWorld` from the
   log's `:DEFUN` events, and the replayed statement is truth of the log's
   root Goal clause — i.e. it comes from the same untrusted emission as the
   proof, anchored to the `.lisp` source by the sidecar source hashes and the
   hand statement pins. **This is not a trust surface on the product path**
   (ruled 2026-08-19): the user writes the idiomatic Lean `Prop` they want,
   and the kernel covers it end to end — a divergent replayed statement either
   fails to close the transport (loud incompleteness) or closes it, in which
   case it still entails the user's `Prop`. What the stage does bear on is
   ATTRIBUTION (that a product is the ACL2 theorem it is named for —
   review-checked, with the statement pins as honest-mistake tripwires) and
   the METRIC layer, where no user-authored `Prop` sits downstream; see
   [*Trust model*](#trust-model) and
   [*Known limitations*](#known-limitations). `ACL2Lean/WorldGen.lean` /
   `ACL2Lean/Translator.lean` translate the `.lisp` source directly and would
   derive the statement without the fork's help; they are **not** wired in
   today, and that is **automation convenience** — saving the user from
   writing the statement — not a trust prerequisite.
6. **ACL2-logic interpreter** (`ACL2Lean/EvalOpt.lean`,
   `ACL2Lean/Logic.lean`) — the fuel-bounded semantic model that *defines*
   what the replayed statement means. It is run as a PEER of ACL2 (same
   interface: forms in, one value per form out) and differentially tested
   against the real thing (`Tests/differential/`, `just diff-test`); a
   divergence is definitionally a bug and is logged in [`BUGS.md`](BUGS.md).
7. **Proof replay** (`ACL2Lean/Replay/Driver.lean`,
   `ACL2Lean/Replay/EvalLemmas.lean`) — recurses the reconstructed tree and
   emits a Lean proof object for the replayed statement, node by node; the
   Lean kernel checks it. The replay does **no inference** as its governing
   rule: if the tree lacks the information to replay a step, the fix is more
   instrumentation at the ACL2 source, never a heuristic in Lean. Where the
   replay does deviate, the deviation is explicit and enumerable — see
   [*Known limitations*](#known-limitations).
8. **Waypoint decode** (`ACL2Lean/Imported/`) — the replayed statement is
   decoded into a **waypoint**: an ACL2-like Lean restatement (ACL2's own
   notions in Lean clothes — `SExpr` lists, `isortL`). `Imported/Lifting.lean`
   is the lifting library: representations of Lean types in ACL2's value space
   (`Rep`, with ACL2 recognizers as the type discipline), correspondences
   between ACL2 functions and Lean operations (`Implements`), and the generic
   decode lemmas. The LIVE catalog is `liftCatalog` in
   `ACL2Lean/Imported/Waypoints/Catalog.lean`, one decision per green sweep
   row, enforced by build-failing coverage/seam/axiom/criterion gates.
   (`Imported/WaypointCatalog.lean` is only the module facade; its narrative
   header covers the first 18 entries and is historical — do not read status
   off it.) A waypoint is part of the METRIC, the legible scoreboard of how
   far the machinery reaches; per the lexicon it is **never a result**.
9. **Mirror** (`ACL2Lean/Mirrors/` + `ACL2Lean/MirrorProofs/`) — **the
   PRODUCT**, and the only stage whose output is a result. See
   [*The product layer*](#the-product-layer) below.

In the project's own words:
ACL2 book → proof log → **replayed statement** (metric) → **waypoint**
(metric, legible) → **mirror** (product).

## Trust model

The kernel is the sole trust anchor, but it does not certify everything a
reader might assume. Three properties are DISTINCT and separately enforced;
conflating them is the standing documentation hazard here.

**Independent validation.** The mirror products are additionally checked by
[leanprover/comparator](https://github.com/leanprover/comparator) — statement
match against a zero-import challenge file, a permitted-axioms check pinned to
the classical trio, and replay of the exported proof terms from an empty
environment by BOTH Lean's kernel and [nanoda](https://github.com/ammkrn/nanoda_lib),
an independently developed Rust kernel. `just validate-products` runs it; the
harness, its trust boundaries, and the tool-fetch instructions are in
[`validation/README.md`](../validation/README.md).

1. **Lean logical soundness — kernel-certified.** A declared Lean theorem
   follows from Lean's trusted basis plus its listed axioms (`propext`,
   `Classical.choice`, `Quot.sound`; a build-failing axiom gate pins the
   receipts). No bug anywhere in stages 1–8 can certify a FALSE Lean theorem:
   a wrong pipeline produces a proof object that fails to typecheck, never a
   false result.
2. **Statement authenticity — engineering evidence, not kernel-certified.**
   That the proved proposition really is the named ACL2 theorem (same formula,
   functions, scope, value universe) is not something the kernel checks: a bug
   in instrumentation, parsing, world construction, or statement derivation
   can produce a kernel-accepted proof of a *different but true* statement
   presented under the intended name (BUG-019 was a concrete incident of
   exactly this class). Enforced instead by source/include-closure hash
   provenance with fatal capture (`scripts/check-log-provenance.sh`), hand
   statement pins per book (the `Tests/*Pins*.lean` class — honest-mistake
   tripwires, never trust anchors), tamper tests, review of the spec-against-
   book reading, and adversarial audits. Note what this property is *not*: on
   the product path the user's own idiomatic `Prop` is what the kernel
   certifies, so a divergence here costs ATTRIBUTION (the right theorem under
   the wrong name, or a failure to close), never the truth of the theorem the
   user reads.
3. **Replay fidelity — engineering evidence, not kernel-certified.** That the
   proof retraces ACL2's recorded reasoning rather than taking a stronger
   Lean-side route is enforced by the replay drivers' hard-fail frontiers, the
   waypoint criterion and seam gates, the mirror seam gate, the generated
   transport templates, and the drift-test discipline.

Both (2) and (3) are strong engineering evidence and must never be reported as
kernel guarantees. The most recent adversarial review of exactly these claims
is [`audits/2026-08-19_top-level-claims-audit.md`](audits/2026-08-19_top-level-claims-audit.md);
the earlier trust-boundary audit it builds on is
[`audits/2026-08-16_eob-audit-a1-tcb-trust.md`](audits/2026-08-16_eob-audit-a1-tcb-trust.md)
§Q4. Both are dated records; where they conflict with this page, check the
live artifact.

**Where the property is live.** The fully-untrusted reading of the pipeline
holds *once a mirror bridge exists*, and for the demonstrated corpus it does:
each mirror product is a self-contained Lean statement over zero-import
definitions, kernel-checked with the standard trio, and consumes a replayed
statement through the build-failing mirror seam gate. Outside that corpus a
replayed statement or waypoint is stated in `evalOpt` terms and the kernel
certifies only that the proof object is valid *for the statement exactly as
stages 5–6 produced it* — see [*Known limitations*](#known-limitations).

**METRIC vs PRODUCT.** Replayed statements and waypoints are the METRIC: the
scoreboard of how far the machinery reaches, valuable, never presented as
results. Mirrors are the PRODUCT. The two-category model is the governing
frame ([`plans/2026-08-12_master-plan.md`](plans/2026-08-12_master-plan.md)).

As a trust-boundary view of the code:

```
Lean kernel (sole trust anchor)
├── Layer 1: SExpr semantic model + Logic primitives + evalOpt (trusted core)
├── Layer 2: Book translator: ACL2 .lisp → Lean World + replayed statement (untrusted)
└── Layer 3: Proof replay from ACL2 proof logs (untrusted)
```

## The product layer

A **mirror** is a Lean-idiomatic theorem with ZERO ACL2 notions — e.g.
`(xs ++ ys).length = xs.length + ys.length` — that mirrors a property an ACL2
book proves and was proved VIA the replay, through the transfer kit
(`mirror_iso%` / `mirror_transport%` in
`ACL2Lean/MirrorProofs/IsoGen.lean`). A user of a mirror knows nothing about
ACL2 and never needs to.

- **The specs** live in `ACL2Lean/Mirrors/` — pure Lean statements, imports
  pinned by `just check-mirrors-pure`; an ACL2 notion in a mirror is
  definitionally a bug. Spec names are additionally checked against
  core/Std/Batteries/Mathlib for collisions (`Tests/MirrorNameCheck.lean`), so
  a library lemma cannot be mistaken for replayed content.
- **The proofs** live in `ACL2Lean/MirrorProofs/`, each followed by a
  `#guard_msgs`-pinned receipt reading exactly
  `{propext, Classical.choice, Quot.sound}`.
- **The seam gate** (`ACL2Lean/MirrorProofs/SeamGate.lean`) fails the build
  unless every product theorem's proof term transitively consumes a registered
  replayed statement. It enumerates both products and seams mechanically, so a
  new mirror joins with no edit to the gate. Its threat model is stated in the
  file and binds: it catches DETACHMENT (a mirror cited from a library lemma or
  a hand restatement), not MIS-PAIRING — it is a speedbump against the honest
  mistake, not a barrier, and is not to be hardened.

**Read the live inventory off the tree, not off this page:** the product set is
whatever is in `ACL2Lean/MirrorProofs/`, and the seam gate reports the count and
each product's witness at build time. At the 2026-08-19 claims audit that was 21
products — six from the `Basics` books and fifteen from J Moore's sorting corpus
(fourteen instantiated at `Int`, one at `Option Int`; one bundles three replayed
theorems, the equivalence-relation conjuncts). The products are INSTANCE
mirrors: the polymorphic `Prop` schemas in `ACL2Lean/Mirrors/` are real and
useful, but a schema is not a proof for every `α`, and the order-generic
capstone is still future work.

## Getting started

**Prerequisites.** [Lake + the pinned Lean toolchain](../lean-toolchain)
(currently `leanprover/lean4:v4.28.0`, installed automatically by
[`elan`](https://github.com/leanprover/elan)),
[`just`](https://github.com/casey/just) for the convenience recipes, and a
Common Lisp (SBCL is what the build uses) to build the instrumented ACL2.

**Clone with the submodule** (the `acl2/` fork is required):

```sh
git clone --recursive https://github.com/septract/ACL2Lean.git
# or, in an existing clone:  git submodule update --init --recursive
```

**Important — proof logs are a build input.** The Lean sources embed proof
logs at compile time (`include_str`), and the logs
(`acl2_samples/**/*.proof-log`) are *gitignored generated artifacts*. A fresh
clone therefore will **not** `lake build` until the logs are generated. Build
the instrumented ACL2 once, then capture the logs:

```sh
# 1. Build the instrumented ACL2 (SBCL + a full ACL2 build — this is slow)
just build-acl2

# 2. Regenerate the proof logs — the WHOLE surface (sorting corpus +
#    simple + recon-tests + pattern-tests). This uses only the ACL2
#    image, no Lean, so it avoids the build bootstrap cycle.
just recapture-all

# 3. Fetch the prebuilt mathlib cache (otherwise lake builds mathlib from
#    source, which takes hours), then build.
lake exe cache get
lake build
```

**Why the whole surface.** `lakefile.toml` makes the `acl2lean` exe and the
`Tests` library the default targets, `Main.lean` imports the root `ACL2Lean`
library, that imports the sorting mirror proofs and the seam gate, and the
waypoint modules embed their books' logs at compile time (e.g.
`ACL2Lean/Imported/Waypoints/Msort.lean` `include_str`s
`acl2_samples/sorting/msort.proof-log`; the pattern waypoints likewise embed
the `pattern-tests/` logs). A reduced capture cannot build the default
targets. `just recapture-all` is `capture-all-logs` (the `books.txt` sorting
corpus) plus `simple.lisp` + `recon-tests/` + `pattern-tests/` in one shot —
which is also the surface the provenance gate expects.

The one genuinely smaller cone is the FOCUSED replay CLI: `lake build
acl2lean-replay` (what `just replay` runs) imports only
`ACL2Lean.Replay.Runner`, whose sole compile-time log is
`acl2_samples/simple.proof-log` — it reads the book you name from disk at
runtime. That is a dev loop, not a way to build the library.

**Fresh-clone reproduction inventory** — what it actually takes to re-derive
the coverage claim from nothing:

| you need | why |
| --- | --- |
| the `acl2/` submodule, checked out at its pinned commit (currently `e8d78e513d6867d04002f0df644da1723cc96e89`) | without it three of the static checks cannot run (`check-acl2-tags`, `check-log-provenance`, `test-provenance-gates` — all three fail CLOSED, correctly) and the `sorting/*` logs' source identity cannot be checked |
| every `.proof-log` and its `.proof-log.meta` sidecar — **GITIGNORED** (91 of them at the 2026-08-19 audit) | a fresh clone has the claim without the corpus. Regenerate with `just recapture-all` against a fork image built from the pinned submodule commit, or copy them from a working tree. `check-proof-logs` fails loudly first, which is the right behaviour |
| `.lake/packages` (mathlib/batteries/aesop/…) | network, or a pre-populated cache (`lake exe cache get`) |
| a long cold build — budget for it | the sweep's critical path is the two heaviest coverage modules, both single-threaded: `Tests.Coverage.BSsortsEquivalent` **~8 min** (476,930 ms) and `Tests.Coverage.BSqsort` **~7 min** (422,680 ms), measured from the 2026-08-19 claim-gate log. Total wall-clock has not been re-measured since the 2026-08-18 perf arc; see the [archive note](archive/2026-08-19_overview-historical-notes.md) for the pre-arc figures |

Note also that `.gate-runs/*.log` — the claim-gate artifacts commit messages
cite — is gitignored: a fresh clone of a branch has the claim but not that
evidence, and must re-run `just claim-gate` to reproduce it.

## Building and commands

```sh
lake build                              # type-check everything (incl. tests)
just test                               # unit tests
just ci                                 # conformance gate: static checks + build + tests + coverage
just claim-gate                         # the full gate, recorded to .gate-runs/ (slow)
just driver-coverage                    # replay the driver over the whole sample corpus
just waypoint-metrics                   # the ruled waypoint-layer metrics
just diff-test                          # differential-test the interpreter against real ACL2
lake exe acl2lean dump-proof-tree <f>   # inspect a reconstructed proof tree
lake exe acl2lean parse-proof-log <f>   # parse/display a raw proof log
lake exe acl2lean gen-world <file>      # generate World + theorem stubs from .lisp
lake exe acl2lean eval "<expr>"         # evaluate an s-expression
```

`just validate-products` re-checks the mirror products through the external
comparator + nanoda kernels (see *Trust model*; tools fetched per
`validation/README.md`). `just ci` is the conformance gate for a merge; `just claim-gate` is the full
recorded gate required at any commit claiming green (see `CLAUDE.md` on the
two gating tiers). When inspecting a proof, use `dump-proof-tree` — the flat
log misleads about how nodes compose.

If a build fails with a missing-`.proof-log` error, regenerate the logs as in
[*Getting started*](#getting-started) above; the capture script
force-invalidates the Lean modules that embed them, so there is no silent
staleness.

**Diagnostics.** Two env-gated diagnostic sinks exist in the replay driver,
both OFF by default, both `stderr`-only, and **neither is read by any gate,
golden, or test** — they cannot affect a result, and per the two-standard rule
they are not to be hardened into one:

| variable | prints |
| --- | --- |
| `ACL2LEAN_TP_DIAG` | the `tp:`-prover frontier messages a kept condition would otherwise discard (the discard had blinded two audits) |
| `ACL2LEAN_XBOOK_DIAG` | the cross-book pre-pass's otherwise-silent skips: demanded names offered by no book, and refused transfers |

Set either to any value to enable, e.g.
`ACL2LEAN_XBOOK_DIAG=1 lake build Tests.Coverage.BSqsort 2>diag.log`.

## Repository layout

| Path | Contents |
| --- | --- |
| `acl2/` | The instrumented ACL2 fork (submodule, branch `acl2-lean-output`) |
| `ACL2Lean/` | Parser, s-expression core, interpreter, translator |
| `ACL2Lean/Replay/` | The replay driver and its atomic evaluation lemmas |
| `ACL2Lean/Imported/` | The lifting library and the waypoint catalog |
| `ACL2Lean/Mirrors/` | **The product layer**: pure Lean statements (specs), zero ACL2 notions — imports pinned by `just check-mirrors-pure` |
| `ACL2Lean/MirrorProofs/` | The mirror proofs + the transfer kit (`mirror_iso%` / `mirror_transport%`) that discharge them from replayed statements |
| `Tests/` | Unit tests, driver tests, statement pins, the corpus-wide coverage harness |
| `acl2_samples/` | Authored corpus sources (`recon-tests/` is the reconstruction suite, `pattern-tests/` the pattern corpus) + captured logs; upstream books are referenced directly from the `acl2/` submodule (see `books.txt`) |
| `scripts/` | The gate scripts (provenance, tags, dark files, file weight, …) |
| `docs/README.md` | The index of `docs/`, with the live-vs-dated reading rule |
| `docs/plans/` | Design plans and arc charters — `2026-08-12_master-plan.md` is the governing plan |
| `docs/notes/` | Investigation notes, surveys, dated findings |
| `docs/audits/` | Dated audit reports |
| `docs/archive/` | Retired material kept verbatim (passages moved out of live docs, the pre-2026-08-19 `TODO.md` journal) |
| `docs/reference/` | Parked material — not built, not trusted, not part of any result |
| `TODO.md` | The live backlog across all tracks (open items only) |
| `CLAUDE.md` | The working rules (fidelity requirements, audit practices) |

## Known limitations

**This is a research prototype.** The architecture is validated end to end —
proof logs are parsed and reconstructed into the real clause tree, whole
theorems replay into kernel-checked Lean proof objects, and the demonstrated
corpus is carried across the mirror bridge. What remains is *breadth*, and the
frontiers are enumerable rather than open-ended.

**Breadth beyond the demonstrated corpus.** A replayed statement or waypoint
that has not been carried across a mirror bridge is stated in `evalOpt` terms;
the kernel certifies only that its proof object is valid for the statement as
stages 5–6 produced it — not that the statement faithfully restates the ACL2
theorem, nor that `evalOpt` faithfully models ACL2. There, a bug in stages 2–6
can still produce a kernel-accepted proof of a subtly wrong statement.

**Replay frontiers.** On the sample corpus the driver fully replays a subset
of theorems; every theorem it cannot yet replay stops at a **named frontier**
(an explicit `throwError`, never a silent skip or a `sorry`) that maps to a
specific backlog item. Multi-literal pushed clauses, cross-product induction
schemes, pool subsumption, generalization, and previously-proved theorems used
as rewrite rules (replayed as conditional statements with `rule:<thm>`
hypotheses) all replay; the largest open areas are induction-measure
generality (multi-variable and non-`acl2-count` measures, merged/mutual
schemes), discharging the `rule:<thm>` hypotheses from their own replayed
statements, some `:use`/`:induct` hint shapes, and a handful of
decision-procedure leaves awaiting an SMT backend.

**Declared fidelity exceptions.** These are explicit, not silent:

- the ratified **decision-procedure leaf carve-out** — where ACL2 itself
  closes a clause by a verdict-only procedure (tau, type-set/forward-chain
  contradiction, linear arithmetic) with no internal proof record, the replay
  discharges that LEAF by a kernel-checked decision procedure in Lean on the
  leaf's precisely-stated obligation. It applies only to such leaves and to
  the analogous admission decrease obligations; using `omega`/`decide`/SMT to
  shortcut a step ACL2 *did* record is still forbidden. See
  [`plans/2026-06-09_direct-proof-emission.md`](plans/2026-06-09_direct-proof-emission.md);
- a small set of **expiry-held mechanisms** marked `DRIFT MARKER` in
  `ACL2Lean/Replay/Driver/`, each retiring against a queued fork emission —
  including `destructorChainOk`, which as a route discriminator is a
  calibrated heuristic that predicts which replay route can discharge rather
  than reading a recorded route choice.

**Translator scope.** `gen-world` (the source-side frontend — automation
convenience, not a trust prerequisite; see stage 5) currently handles `defun` /
`defthm` / `mutual-recursion` / `local` / `in-theory`; `encapsulate`,
`include-book`, `defconst`, macros, stobjs and guard verification are rejected
fail-closed, so the larger ACL2 books are aspirational targets rather than
passing imports. The intended scope (a CORE
tier targeting roughly the Milawa fragment plus the ratified carve-out, with
EXTENDED and OUT tiers) is set out in
[`plans/2026-06-10_generality-design.md`](plans/2026-06-10_generality-design.md)
— the architecture reference, whose L1–L3 invariants bind while its status and
sequencing are superseded by the governing plan.

**Known interpreter divergences from real ACL2** are indexed in
[`BUGS.md`](BUGS.md) — the single canonical index, cross-checked against the
self-enforcing differential corpus by `scripts/check-bugs.sh` so an entry can
neither rot nor be silently dropped.

## Where live status lives

Not on this page. Read it off the artifacts:

- `just driver-coverage` and `Tests/driver-coverage.golden` — per-theorem
  replay status over the whole corpus; the golden's header line carries the
  current count (`REPLAYED 116/116 (116 unconditional + 0 conditional)` at the
  2026-08-19 gate).
- `liftCatalog` in `ACL2Lean/Imported/Waypoints/Catalog.lean` — the live
  waypoint catalog; `just waypoint-metrics` for the ruled metrics.
- `ACL2Lean/MirrorProofs/` and the seam gate's build-time report — the live
  product inventory.
- [`notes/2026-07-22_pattern-map.md`](notes/2026-07-22_pattern-map.md) — the
  COVERAGE source of truth (ci-gated by `just check-pattern-map`): the
  top-down frame over ACL2's situation space, the authored pattern books, and
  the pinned frontiers per pipeline layer. Consult it before building support.
- [`../TODO.md`](../TODO.md) — the running backlog and the named frontiers.

For how the system got here, including what went wrong along the way, see
[`notes/2026-08-18_project-history.md`](notes/2026-08-18_project-history.md).
Retired passages from this document are in
[`archive/`](archive/README.md).

## License

BSD 3-Clause — see [LICENSE](../LICENSE). Copyright (c) The ACL2Lean Authors.
(The `acl2/` submodule is upstream ACL2 plus our instrumentation and carries
its own license — see `acl2/LICENSE`.)
