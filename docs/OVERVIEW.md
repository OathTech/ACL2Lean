# ACL2Lean — technical overview

**Replaying ACL2 proofs as kernel-checked Lean 4 proofs.**

*This document was the repository's `README.md` until 2026-08-19, when the
README was rewritten as a short front page and the technical detail moved
here. Paths in prose are repo-root-relative; markdown links are relative to
this file's location in `docs/`.*

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
three different things: see [`docs/LEXICON.md`](LEXICON.md).

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
   in a mirror is definitionally a bug. **The product layer's live
   inventory is `ACL2Lean/MirrorProofs/`** — every `mirror_transport%`
   declaration there is a proved mirror, each followed by a
   `#guard_msgs`-pinned receipt reading exactly
   `{propext, Classical.choice, Quot.sound}`; read the count off the
   files rather than off this page. (It covers the `Basics` books and,
   since the 2026-08-18 close-out, the whole of J Moore's sorting
   corpus.)

The pipeline in the project's own words (`docs/LEXICON.md`):
ACL2 book → proof log → **replayed statement** (metric) → **waypoint**
(metric, legible) → **mirror** (product).

## Trust model

**The two-sentence version** (adopted 2026-08-16 from the end-of-branch
TCB audit, `docs/audits/2026-08-16_eob-audit-a1-tcb-trust.md` §Q4, whose
wording this reproduces):

> Every mirror theorem is a self-contained statement over its own
> zero-import definitions, kernel-checked from exactly
> propext/Classical.choice/Quot.sound — so nothing in the ACL2 pipeline,
> however wrong, can make one false; you need only read that one spec
> file and trust Lean's kernel. The further claim that these theorems
> were proved *via ACL2 replay* rather than by a Lean-side shortcut is
> not kernel-certified: it rests on generated proof templates,
> build-failing seam/axiom gates at the waypoint layer (whose per-book
> granularity and absence at the mirror level are known), and review —
> that audit verified it holds today for all nine live artifacts by
> direct proof-term inspection, and also demonstrated that a deliberate
> author could evade the template gate, so treat "via replay" as
> strongly-evidenced engineering, not mathematics.

*Current disposition (2026-08-19) — the quote above is DATED and stays as
historical record.* Two of its particulars have moved: the mirror-level seam
gate it records as ABSENT now exists (`ACL2Lean/MirrorProofs/SeamGate.lean`,
build-failing) and mechanically finds **21** mirror products, each with a
replayed-statement witness — not nine artifacts checked by hand. Its
CONCLUSION is unchanged and still governs: "via replay" remains
strongly-evidenced engineering, not mathematics — the gate catches detachment,
not mis-pairing, and nothing in it makes attribution kernel-certified (see
`docs/audits/2026-08-19_top-level-claims-audit.md`).

The long form — three DISTINCT properties, separately enforced (rewritten
2026-08-06 after the overall-project audit — the earlier text conflated
them):

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

**Prerequisites.** [Lake + the pinned Lean toolchain](../lean-toolchain)
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

# 2. Regenerate the proof logs — the WHOLE surface (sorting corpus +
#    simple + recon-tests + pattern-tests). This uses only the ACL2
#    image, no Lean, so it avoids the build bootstrap cycle.
just recapture-all

# 3. Fetch the prebuilt mathlib cache (otherwise lake builds mathlib from
#    source, which takes hours), then build.
lake exe cache get
lake build
```

**Why the whole surface** *(corrected 2026-08-19 — the instruction here used to
capture only `simple.lisp` + `recon-tests/*.lisp` and call the rest optional,
which cannot build the default targets; found by the external claims audit,
`docs/audits/2026-08-19_top-level-claims-audit.md`)*: `lakefile.toml` makes the
`acl2lean` exe and the `Tests` library the default targets, `Main.lean` imports
the root `ACL2Lean` library, that imports the sorting mirror proofs and the seam
gate, and the waypoint modules embed their books' logs at compile time (e.g.
`ACL2Lean/Imported/Waypoints/Msort.lean` `include_str`s
`acl2_samples/sorting/msort.proof-log`; the pattern waypoints likewise embed the
`pattern-tests/` logs). `just recapture-all` is `capture-all-logs` (the
`books.txt` sorting corpus) plus simple + recon-tests + pattern-tests in one
shot — which is also the surface the provenance gate expects (the 91 logs in the
inventory below).

The one genuinely smaller cone is the FOCUSED replay CLI: `lake build
acl2lean-replay` (what `just replay` runs) imports only
`ACL2Lean.Replay.Runner`, whose sole compile-time log is
`acl2_samples/simple.proof-log` — it reads the book you name from disk at
runtime. That is a dev loop, not a way to build the library.

**Fresh-clone reproduction inventory** (what it actually takes to
re-derive the coverage claim from nothing — measured by the
end-of-branch claims audit, 2026-08-16):

| you need | why |
| --- | --- |
| the `acl2/` submodule, checked out at its pinned commit (currently `e8d78e513d6867d04002f0df644da1723cc96e89`) | without it 3 of the 13 static checks cannot run (`check-acl2-tags`, `check-log-provenance`, `test-provenance-gates` — all three fail CLOSED, correctly) and the `sorting/*` logs' source identity cannot be checked |
| the **91** `.proof-log` + `.proof-log.meta` files — **GITIGNORED** | a fresh clone has the claim without the corpus. Regenerate with `just recapture-all` against a fork image built from the pinned submodule commit, or copy them from a working tree. `check-proof-logs` fails loudly first, which is the right behaviour |
| `.lake/packages` (mathlib/batteries/aesop/…) | network, or a pre-populated cache (`lake exe cache get`) |
| a long cold build — budget for it | The sweep's critical path is the two heaviest coverage modules, both single-threaded: `Tests.Coverage.BSsortsEquivalent` **~8 min** (476,930 ms) and `Tests.Coverage.BSqsort` **~7 min** (422,680 ms), measured from the 2026-08-19 claim-gate log. *These were ~50 min and ~8 min before the 2026-08-18 perf arc, which is what the ~2 h cold-build figure measured 2026-08-16 was dominated by; the whole-build figure has not been re-measured since.* |

Note also that `.gate-runs/*.log` — the claim-gate artifacts commit
messages cite — is gitignored: a fresh clone of a branch has the claim
but not that evidence, and must re-run `just claim-gate` to reproduce it.

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

**A known non-fatal toolchain PANIC in the build output — ELIMINATED at
v4.31.0+ (upstream leanprover/lean4#13202); bumped to v4.33.0 2026-08-19**
*(originally classified 2026-08-19 at the external claims audit's request,
P2; the toolchain-bump gate artifact
`.gate-runs/c68bb1f-20260819T121241Z.log` greps CLEAN — zero
`SymbolFrequency` occurrences with the heavy modules freshly rebuilt)*.
The remainder of this section is the HISTORICAL record of the v4.28.0-era
panic and its diagnosis. A full build then printed, while building the
heaviest coverage modules (`Tests.Coverage.BSsortsEquivalent` was the
usual one):

```
PANIC at _private.Lean.LibrarySuggestions.SymbolFrequency.0.Lean.Environment.unsafeRunMetaM
Lean.LibrarySuggestions.SymbolFrequency:75:24: (deterministic) timeout at `whnf`,
maximum number of heartbeats (200000) has been reached
```

*What it is:* Lean's own `symbolFrequency` persistent environment extension —
the premise-frequency index behind library-suggestion tactics — runs its
`exportEntriesFnEx` over the module's constants **at export**, i.e. after all
elaboration is done. On our largest modules that post-pass exceeds its heartbeat
budget and panics out of the extension.

*Why it is not a warning being tolerated* (the "warnings are unacceptable" rule
in `CLAUDE.md`): it is not our elaboration and carries no semantic content —
it happens strictly after the module's declarations are elaborated and
kernel-checked, the module still writes its `.olean` and the build reports
`Build completed successfully`; nothing we check depends on that extension (no
proof, no `#print axioms` receipt, no `#guard_msgs` pin, no golden row, no gate
reads it — its only consumers are suggestion tactics this project does not use);
and the full claim gate records the panic alongside `TRUE_EXIT=0`.

*Why it is not fixed here:* there is no project-local switch, and — measured
2026-08-19, when elimination was attempted rather than assumed — no
module-split route either.

*(a) No switch.* The extension is registered by `builtin_initialize` in the
Lean shared library, has no `register_builtin_option` gate and no `lean` CLI
flag, and its heartbeat budget is not user-reachable —
`Lean.Environment.unsafeRunMetaM` builds a FRESH `Core.Context` with
`options := {}`, and `maxHeartbeats` defaults off *those* options
(`Lean/CoreM.lean:217,225` in the pinned v4.28.0 source), so neither
`set_option maxHeartbeats` in the module nor `-DmaxHeartbeats=…` on the command
line reaches it (checked against the toolchain source, 2026-08-19).

*(b) No split — and the reason kills the whole class.* The budget is not
compared against the export pass's OWN cost. That same fresh `Core.Context`
also takes `initHeartbeats := 0` (the field default, `Lean/CoreM.lean:224`),
so `checkMaxHeartbeatsCore` compares the **absolute** thread heartbeat count —
everything the module burned during its entire elaboration — against the fixed
200 000 000. Reproduced directly: a `run_cmd` that burns heartbeats and then
runs a `MetaM` job inside a replica of that context returns the byte-identical
timeout string *only* after the burn. Calibrated against real work,
`Runner.runBook` costs ~16 heartbeat-units/ms, so the budget is spent after
~12 **seconds** of replay elaboration. `Tests.Coverage.BSsortsEquivalent`
replays for ~477 s (~38x the budget); `BSqsort` at ~423 s (~35x) does *not*
panic, so module weight is not even the discriminator at the margin. Bringing
a module under budget would take ~40 pieces — and the coverage harness has no
sub-book unit to split into: `coverage_book%` is one module per BOOK per
golden section, and the aggregate's tiling check requires exactly one section
per `corpusOrder` entry, so a partial-book split is new machinery, not a use
of the existing mechanism.

The one surface left is the extension's own deny lists (`nameDenyListExt` /
`typePrefixDenyListExt`, both documented for `run_cmd modifyEnv …`): deny every
local theorem and the pass has nothing to do. **Not taken** — measured on the
offending module, a `typePrefixDenyListExt` entry for `ACL2` covers 79 of its
81 processed theorems but not the 2 with `Eq`-headed statements, and one
survivor re-triggers the panic; the alternative is an enumerated name list over
our generated namespaces, i.e. exactly the rotting name-predicate cruft the
audit practices say to delete rather than add.

One artifact-reading note: the panic text is stored in **Lake's job log** and
replayed by every later build that finds the module up to date — the three
copies in a single gate artifact are one panic replayed by three lake
invocations, not three failures — so any future fix only shows up once that
module actually rebuilds.

The real fix WAS upstream, exactly as this note predicted:
leanprover/lean4#13202 (v4.31.0) sets `maxHeartbeats := 0` in the export
pass's context — the same mechanism the diagnosis above isolated. The
2026-08-19 toolchain bump to v4.33.0 removed the panic from our builds.

**Diagnostics.** Two env-gated diagnostic sinks exist in the replay
driver, both OFF by default, both `stderr`-only, and **neither is read by
any gate, golden, or test** — they cannot affect a result, and per the
two-standard rule they are not to be hardened into one:

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

BSD 3-Clause — see [LICENSE](../LICENSE). Copyright (c) The ACL2Lean Authors.
(The `acl2/` submodule is upstream ACL2 plus our instrumentation and carries
its own license — see `acl2/LICENSE`.)
