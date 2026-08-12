# Part 3 — How it works

Downward, into the machinery. None of this is trusted (see
[part 1](1-tcb.md)); it is what has to *work* for a proof to exist at all.

---

## The pipeline

Importing one theorem runs through seven stages. Every stage except ACL2's own
proof search is our code.

1. **ACL2 source** — a `.lisp` file of `defun`s and a `defthm`. ACL2 searches
   for a proof. *(untrusted oracle)*
2. **ACL2 instrumentation** — our additions in the `acl2/` submodule (logging
   points in `rewrite.lisp` / `simplify.lisp` / `axioms.lisp`, every inserted
   region carrying a `TRACE-LOG[<ns>/<label>]` tag, enforced by
   `just check-acl2-tags`). Emits a structured **proof log**: runes, lhs/rhs,
   `:SUBST`, the induction `:SCHEME`, `:TYPE-PRESCRIPTION` corollaries, the
   per-literal rewrite chains.
3. **Proof-log parser** — `ProofLog.lean`: text → structured trace events.
4. **Proof-tree reconstruction** — `ClauseTree.lean` (`buildDevelopment`):
   events → a single proof tree for the whole development. Each theorem's proof
   is the **clause tree** ACL2's waterfall actually walked, addressed by
   clause-ids (`ClauseProof → ClauseNode`), with induction pool-roots
   synthesized from the push→induct adjacency; the per-literal rewriter detail
   hanging off SIMPLIFY nodes is built by `ProofTree.lean`. Linking is
   deterministic — clause-id lineage is the inverse of ACL2's `waterfall1-lst`
   — and unlinkable structure hard-fails. **This tree, not the flat log, is
   what the replay consumes**; inspect it with
   `lake exe acl2lean dump-proof-tree`.
5. **Statement derivation** — the `World` is `Development.toWorld` (from the
   log's `:DEFUN` events, provenance-gated) and the replayed statement is
   `EvTrue w env (disjoinTerm root.inputClause)` over the log's root Goal
   clause. Note what this means: the statement comes from the same untrusted
   emission as the proof, anchored to the `.lisp` source through the hand
   statement pins in `Tests/SortingPins.lean` and friends.
   (`WorldGen.lean`/`Translator.lean` are the intended independent frontend and
   are not in the certified pipeline yet.)
6. **ACL2-logic interpreter** — `EvalOpt.lean` (`evalOpt`, fuel-bounded) +
   `Logic.lean` (the primitives): the Lean semantic model that *defines what
   the replayed statement means*. Because it defines that meaning, it is run as
   a PEER of ACL2 — same interface, `acl2lean eval < forms` mirroring
   `acl2 < forms` — and differentially tested against real ACL2
   (`just diff-test`, corpus in `Tests/differential/`). Divergences are logged
   as numbered bugs in `docs/BUGS.md`, each pinned by a self-enforcing
   `known-bug` corpus entry that `just check-bugs` cross-checks.
7. **Proof-object builder** — `Replay/ProofProducer.lean` and the
   `Replay/Driver/` walkers: recurse the tree and emit a Lean `Expr`; the
   kernel checks it.

**The checker does no inference.** ACL2 already did the reasoning; Lean replays
it deterministically. If the tree lacks the information for a step, that is
missing instrumentation to fix at the source, not a licence to guess — the
driver hard-fails at named frontiers.

The one ratified carve-out: **decision-procedure leaves**. Where ACL2 itself
closes a clause by a procedure with no internal proof record (tau-system,
type-set/forward-chain contradiction, linear arithmetic — ACL2 records only a
verdict plus a rune set), the replay discharges that leaf by a kernel-checked
decision procedure in Lean (`omega`) on the leaf's precisely-stated obligation.
The clause tree — which *is* ACL2's proof — stays mirrored exactly; a leaf with
no emitted discharge node at all is still an emission gap and hard-fails. The
same carve-out covers a defun's emitted admission decrease obligations.

## From replayed statement to native theorem

The four layers between "the driver produced a proof" and "here is a Lean
theorem you can read" are, in order:

| layer | module | what it does |
| --- | --- | --- |
| definitions | `Demo/Sorting/TCB.lean`, `Demo/Sorting/AclSource.lean` | the native readings and the ACL2 bodies |
| correspondence | `Imported/Sorting/Iso.lean`, `IsoAdmission.lean` | stage 1 (`*_exec_corr`): the ACL2 call converges to a total Lean function. stage 2 (`*Exec_enc`): that function on encoded inputs computes the native reading |
| decode | `Imported/Sorting/Decode.lean`, `DecodeSorts.lean` | the ONLY layer that touches replayed statements: transports each into its native form |
| assumptions | `Demo/Sorting/Assumptions.lean` | the facts ACL2 discharged that the replay cannot yet construct |

The correspondence layer states nothing relating two *different* ACL2
functions — that is the mirror criterion's "ornamental import" ban, and such
facts may arrive only through a replayed statement.

## The generators

Hand-written correspondence proofs were the original bottleneck, so both stages
are generated from a declarative spec:

* **`derive_exec%`** — given a symbol, formals, body and measured argument,
  generates the total `*Exec` function and the stage-1 `*_exec_corr`
  convergence proof. Callees resolve through an exec-kit registry
  (`register_exec_kit%`), so books compose. Where the recursion is not on the
  template (a CONS-argument call site, a non-structural measure) the exec is
  hand-written — `msortExec`, `qsortExec`, `bnextExec`, `oLtExec`.
* **`derive_sim%`** — given the exec, the variable kinds, the native reading
  and an induction principle (`structural` or `functional`), generates the
  stage-2 `*Exec_enc` iso.
* **`load_development%` / `derive_world` / `driver_replayed%`** — the
  compile-time front end: parse+reconstruct, build the `World`, run the driver.

The metric that tells whether this is industrialising is **hand lines per
catalog native** (`just mirror-metrics`): it must fall as books land.

## The catalog and the gates

`liftCatalog` (`Imported/Mirrors/Catalog.lean`) carries **one decision per
green row** of the corpus sweep: `.native` (with the constant), `.nativeSorried`
(native, with named debt), or `.replayedOnly` (no non-vacuous native content,
with the reason). A newly green row with no decision fails the build.

Six build-failing gates keep it honest:

* **Lift-coverage** — every green golden row has a catalog decision, and every
  named constant exists.
* **Seam** — each native's proof term must transitively consume its own
  `driver_replayed%` constant, so a "mirror" cannot be detached from the ACL2
  proof it claims to import.
* **Axiom-exactness** — every mirror theorem's axiom set is checked exactly:
  the classical trio, plus `sorryAx` only where a catalog entry declares the
  debt — and an entry that *stops* carrying `sorryAx` also fails, forcing a
  promotion review rather than letting debt retire unnoticed.
* **Criterion-1** — a mirror's *statement* may not mention the evaluator layer
  (`evalOpt`, `EvTrue`, `World`, `boolEnc`) or any `*Exec` function: no mixed
  vocabulary, so the statement is readable without knowing ACL2.
* **Provenance** — no Lean-side content discharger may exist in the mirror
  layer outside the registered debt set, and a registered entry whose `sorry`
  is replaced by a hand proof fails. ACL2 must do the reasoning.
* **`hreplayed`-usage** — a decode that *takes* a replayed statement must
  actually *use* it, not prove its content beside it.

Plus the static ones in `just ci`: `check-trust-imports` (the demo import
boundary, part 1), `check-file-weight` (the 1500-line module ratchet),
`check-dark-files` (every tracked `.lean` reachable from a build root),
`check-log-provenance` (every corpus log stamped at the current submodule
HEAD), `check-bugs`, `check-acl2-tags`, `check-pattern-map`.

**These gates are speedbumps, not barriers — deliberately.** Each carries its
own threat-model comment. They are reviewed to the deterrent standard (does it
catch the honest mistake? is it simple enough never to be wrong? could we
delete it?), never to "could a motivated construction evade it" — that question
manufactures infinite hardening. The load-bearing trust is the design: the
kernel, plus small exact axiom checks over a small TCB.

## Census and metrics

Measured, never asserted:

* `just mirror-metrics` — the kept-condition census by class (computed by the
  driver from the proof term, so Lean-side effort cannot move it), hand lines
  per catalog native, and the decode count.
* `Tests/MirrorCensus.lean` — the mirror-layer shape census, printed as a
  watched number that can never fail the build (the demoted shape gate: a
  growing `support/other` bucket is the signal an audit reads).
* `Tests/driver-coverage.golden` — the corpus sweep itself, byte-exact in `ci`,
  with `just golden-review` as the structural review lens.

## Where the remaining trust sits

The kernel does **not** check that the replayed statement faithfully restates
the ACL2 theorem, nor that `evalOpt` faithfully models ACL2. Those are enforced
separately — source-hash provenance on every log, hand statement pins per book,
differential testing of the interpreter against real ACL2, and adversarial
audits. The README's *Trust model* section spells the properties out. The
governing plan is `docs/plans/2026-06-10_generality-design.md`; the coverage
source of truth is `docs/notes/2026-07-22_pattern-map.md`.

---

Back to **[Part 1 — what's the TCB](1-tcb.md)** or
**[Part 2 — replaying a book](2-replay.md)**.
