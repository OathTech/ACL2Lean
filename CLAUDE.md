# ACL2Lean

ACL2-to-Lean 4 bridge: import ACL2 theorems as kernel-checked Lean proofs, with
**Lean as the sole trust anchor**. ACL2 is an untrusted proof-search oracle.

The point of the project is *genuine, faithful* replay. A proof that passes the
kernel but does not mirror ACL2's reasoning is worthless here — fidelity is the
product, not a quality bar on top of it.

## The pipeline

Importing one theorem runs through these stages. **Every stage except ACL2's own
proof search is our code and can contain bugs or discrepancies** — and several of
those failures are invisible to the Lean kernel (see the trust note below).

1. **ACL2 source** — a `.lisp` file of `defun`s and a `defthm`; ACL2 searches for
   a proof. *(untrusted oracle — its proof search is taken as given, but ACL2 is
   not a trust anchor)*
2. **ACL2 instrumentation** *(our addition — the `acl2/` submodule; logging points
   across 12 files — 228 tags; see the tagging survey for the full map)* —
   emits a structured
   **proof log** (`.proof-log`, e.g. `acl2_samples/simple.proof-log`): runes,
   lhs/rhs, `:SUBST`, the induction `:SCHEME`, `:TYPE-PRESCRIPTION` corollaries,
   and the per-literal rewrite chains.
3. **Proof-log parser** — `ProofLog.lean` (`ProofLog.parse`): proof-log text →
   structured trace events.
4. **Proof-tree reconstruction** — `ClauseTree.lean` (`buildDevelopment`):
   events → a **single proof tree** for the whole development, `Development`: a
   right-nested sequence of world events in file order (`defun` /
   `type-prescription` / `theorem`), each binding (scoping) over the rest —
   definitions as let-bindings over the later theorems that use them. Each
   theorem's proof, and each defun's termination proof, is the **clause tree**
   ACL2's waterfall actually is, addressed by clause-ids: `ClauseProof →
   ClauseNode` (each clause processed by a sequence of processors, with child
   clauses; induction pool-roots like `*1` are synthesized from the push→induct
   adjacency). The per-literal **rewriter detail** that hangs off SIMPLIFY nodes
   (`ProofNode`/`LiteralProof`, with the IH linked to its solidify use) is built
   by `ProofTree.lean` (`buildLiteralProofs`). Linking is deterministic —
   clause-id lineage is the inverse of ACL2's `waterfall1-lst`; unlinkable
   structure hard-fails. This tree — not the flat log — is what the replay
   consumes.
5. **Statement derivation** — the stage that decides *what theorem we are
   proving*. **As wired today this is the PROOF-LOG path, not `gen-world`**
   (audit 2026-07-26 F5b — the earlier text here mis-aimed auditors): the
   certified `World` is `Development.toWorld` (from the log's `:DEFUN`
   events, provenance-gated per BUG-019) and the replayed statement is
   `EvTrue w env (disjoinTerm root.inputClause)` over the log's root Goal
   clause (`Replay/Driver/Harness.lean`) — i.e. **the statement comes from
   the same untrusted fork emission as the proof**, anchored to the `.lisp`
   source only through the hand-written statement pins in
   `Tests/DriverTests.lean` (a handful of theorems; the rest are
   type/axiom-checked but compared to nothing). `WorldGen.lean` /
   `Translator.lean` (`gen-world`) translate the `.lisp` source directly
   and are NOT wired in — which is **automation convenience, not a trust
   prerequisite** (Mike, 2026-08-19: the user writes the idiomatic Lean
   `Prop` themselves, and the kernel covers it end to end, so a divergent
   replayed statement either fails to close or still entails the user's
   `Prop`; what remains at stake is ATTRIBUTION and the un-mirrored METRIC
   layer — `docs/notes/2026-08-19_versioning-policy.md`). The reader they
   use had a fail-open tokenizer gap (BUG-020, fixed 2026-07-26) that was
   a prerequisite for that wiring.
6. **ACL2-logic interpreter** — `EvalOpt.lean` (`evalOpt`, fuel-bounded) +
   `Logic.lean` (the primitives): the Lean semantic model that *defines what the
   replayed statement means*. If this diverges from ACL2's semantics, a "correct"
   proof proves the wrong thing. **Long-term fidelity objective — TOTAL ACL2
   MASQUERADE:** this interpreter should be indistinguishable from real ACL2 as
   a black box (feed randomly-generated ACL2 programs to both, string-compare
   output). Because `evalOpt` *defines* the replayed statement's meaning, any divergence is
   a latent soundness hole — so the interpreter is run as a PEER of ACL2 (same
   interface: a stream of forms in via stdin, one value per form out —
   `acl2lean eval < forms` mirrors `acl2 < forms`) and differentially tested
   against it. The harness (`Tests/differential/`, `just diff-test`) feeds the
   same ACL2 forms to both and diffs the value streams; its `unsupported`/`known-bug`
   corpus classes document exactly how far the masquerade currently reaches.
   Growing a trusted-core primitive means pinning it there first (see the
   corpus README and the roadmap H3).
7. **Proof-object builder** — `Replay/Driver.lean` + the `Replay/Driver/`
   modules (a `MetaM` procedure, the eventual `acl2_replay` tactic) +
   `Replay/EvalLemmas.lean` (atomic step lemmas): recurses the proof tree and
   emits a Lean **`Expr`** discharging the replayed statement; the **Lean
   kernel** then checks it.

**End goal — ACL2 as an untrusted Lean tactic.** The reason to produce the replayed
statement is to discharge a *native Lean theorem* we actually want — a **MIRROR**.
Terminology (restored 2026-08-12 to Mike's original meaning; the
two-category model = METRIC vs PRODUCT; the canonical glossary is
`docs/LEXICON.md` — where dated docs conflict with it, it wins).
Three distinct things:
- a *replayed statement* is the deep-embedded theorem
  `EvTrue w env ⟦formula⟧` over `evalOpt` — the METRIC's unit;
- a *WAYPOINT* is the ACL2-like Lean restatement of a replayed fact
  (`Imported/Waypoints/`, catalogued by `Imported/WaypointCatalog.lean`):
  Lean notions over `SExpr`/`lexorderB` — the ACL2 value universe in Lean
  clothes. Waypoints are the METRIC's SCOREBOARD — how far the replay
  machinery reaches — and are **never a result**: presenting one as a
  top-level theorem is forbidden;
- a *MIRROR* is ONLY and exclusively the PRODUCT: a Lean-idiomatic theorem
  with **zero ACL2 notions** (`ACL2Lean/Mirrors/`, purity-gated by
  `just check-mirrors-pure`), mirroring a property an ACL2 book proves and
  proved VIA replay — the sole first-class artifact establishing that a
  replayed theorem means what the user intends.

**Vocabulary practice (Mike, 2026-08-13 — disambiguate hard, as design
practice).** A shared NAME is the channel by which a library lemma, or a
reader, can be mistaken for content that must come via replay. Three layers,
each binding: (1) **waypoint READINGS** (`derive_exec%` isos, `Imported/`)
must be OWN-DEFINITIONS — a reading spelled in library names is closable by
library simp lemmas, which is exactly the leak; (2) **mirror SPEC BODIES** —
a construct that mirrors a BOOK FUNCTION is an own-definition (its iso square
arrives with its mirror); pure-Lean idiom is FULLY QUALIFIED (`List.find?`,
`List.length`) or an own device; operator notation (`++`, `∈`) is permitted as
unambiguous; (3) **NAMES** — a mirror-spec name must have ZERO overlap with a
core/Std/Batteries/Mathlib name, at the root or dot-notation-reachable on a
type the spec uses; `Tests/MirrorNameCheck.lean` is the collision linter and
enforces it at build time.

**THE FOUR-LINE CANON (Mike, 2026-08-14)** — persisted here 2026-08-16
because it is cited as binding (charter priority ranks, delegated goals)
and was defined nowhere:
(1) NO Lean-side theorems specific to each example (generic lifting
excepted);
(2) ALL mirrors proved COMPLETELY;
(3) mirrors are idiomatic Lean, ZERO ACL2 taint;
(4) the proofs are accomplished BY REPLAYING the ACL2 theorems.

(Dated docs/notes/audits predating this restoration use "mirror"/"native
mirror" for the waypoint layer; read those as WAYPOINT.) Given a desired
Lean statement (e.g. `1 + 1 = 2` in Lean's own terms), we prove **in Lean,
kernel-checked**, that it follows from the replayed statement under the
interpreter — turning an ACL2 proof into a Lean proof of the same fact. Because
that final bridge is kernel-checked and the desired theorem is stated in Lean's
native semantics, **the entire ACL2 pipeline (stages 1–7) becomes untrusted**: a
bug anywhere makes the composed proof fail to typecheck — it can never yield a
false theorem. ACL2 then serves as a sound (if incomplete) untrusted tactic inside
Lean proofs.

**Trust note — read this (refreshed 2026-08-19).** That fully-untrusted property
holds *only once the final MIRROR bridge exists* — and for the DEMONSTRATED
CORPUS it now does. As of the sorting close-out there are **21 mirror products**
(6 `Basics` + 15 `Sorting`, `ACL2Lean/MirrorProofs/`): Lean-idiomatic theorems
with zero ACL2 notions, each carrying the pinned
`{propext, Classical.choice, Quot.sound}` receipt and each consuming a replayed
statement through the build-failing mirror seam gate
(`ACL2Lean/MirrorProofs/SeamGate.lean`). For THOSE theorems the property is live:
no bug anywhere in stages 1–7 can make one of them false.

The caution this note exists for now has two targets, and both still bind:

- **Breadth — anything outside the demonstrated corpus.** A replayed statement or
  waypoint that has not been carried across a mirror bridge is stated in
  `evalOpt` terms, and the kernel certifies only that the proof object is valid
  *for the replayed statement exactly as stated in stages 5–6* — NOT that the
  replayed statement faithfully restates the ACL2 theorem, nor that `evalOpt`
  faithfully models ACL2. There, a bug in stages 2–6 can still produce a
  kernel-accepted proof of a subtly wrong statement.
- **Attribution and fidelity — even for the 21.** The kernel does NOT certify
  that a product is the named ACL2 theorem (**statement authenticity**), nor that
  its proof retraces ACL2's recorded reasoning rather than taking a Lean-side
  shortcut (**replay fidelity**). Both are enforced one level down — source-hash
  provenance, hand statement pins, generated transport templates, seam/axiom
  gates, and review — which is strong ENGINEERING EVIDENCE, not a kernel
  guarantee. Never report it as one. See
  `docs/audits/2026-08-19_top-level-claims-audit.md` and the 2026-08-19
  three-auditor round (`docs/plans/2026-08-18_close-out-arc-charter.md`).

So when something looks off — and for every NEW import, where no bridge exists
yet — **suspect any stage**: wrong
instrumentation, a mis-parsed or mis-shaped tree, a mistranslated `World` or
replayed statement, an `evalOpt` that diverges from ACL2, or a replay that proves
something slightly different. Do not assume the bug is where it is most convenient
to look; only ACL2's proof *search* is off the table.

**Current status.** Stages 1–4 — ACL2 instrumentation (incl. induction measure
justifications, preprocess chains + clausify checkpoints, and decision-procedure
discharge nodes), proof-log parsing, and proof-tree reconstruction
(`buildDevelopment`) — are built and validated against the sample corpus
(`acl2_samples/`, incl. `recon-tests/` 00–17 (18 books)). The proof-object builder (stage 7)
replays whole theorems end-to-end from the real logs — including WF-induction
(`my-len-my-app`, `app-assoc`), preprocess/clausify composition, and (under the
ratified carve-out) DP leaves — kernel-checked, conditional on emitted
totality/TP facts; the coverage harness (`just ci`) is the scoreboard. The
WAYPOINT layer — the ACL2-like Lean restatements the metric scores itself
against — exists as validated HAND proofs (`Imported/`, live catalog
`Imported/Waypoints/Catalog.lean`). The PRODUCT layer (`ACL2Lean/Mirrors/` +
`ACL2Lean/MirrorProofs/`, Lean-idiomatic zero-ACL2 theorems) is **no longer
just the north star**: the sorting close-out landed 2026-08-19 — FIFTEEN
sorting `Prop`s, fifteen proven-via-replay products (fourteen at `Int`,
`permWitness_complete` at `Option Int`), 21 products in all with the `Basics`
books; the record is `docs/plans/2026-08-18_close-out-arc-charter.md` (ARC EXIT
+ the post-merge audit round) and the spec's bijection is
`docs/notes/2026-08-18_sorting-spec-reshape.md`. What remains at the product
layer is BREADTH beyond that corpus — read live counts off
`ACL2Lean/MirrorProofs/` and the mirror seam gate's build-time report, never
off this page (and no longer off `TODO.md`, which since its 2026-08-19
restructure is a backlog and carries no counts).
**The governing plan is `docs/plans/2026-08-12_master-plan.md`** (ruled
2026-08-13): the two-category model (METRIC vs PRODUCT), Track FREE / Track
REAL, and the phase sequencing to the sorting close-out.
`docs/plans/2026-06-10_generality-design.md` is the **architecture
reference** — its L1–L3 invariants (below) bind; its status and sequencing
are superseded — carrying the hybrid architecture (certifying walkers as the
lane, fragment-local consolidation) and the core/extended/out import tiers,
built on `docs/notes/2026-06-10_acl2-architecture-survey.md`. The trust note above
still applies as refreshed — outside the mirrored corpus a kernel-accepted proof
object certifies only the replayed statement as stated, and even inside it the
kernel certifies neither attribution nor replay fidelity — so keep checking each
stage against the real artifact.
**The COVERAGE source of truth is the pattern map**
(`docs/notes/2026-07-22_pattern-map.md`, ci-gated by
`just check-pattern-map`): the top-down frame over ACL2's situation space,
61 authored pattern books (`acl2_samples/pattern-tests/`), the pinned
frontiers per pipeline layer, the driver fake-replay inventory, and the MDD
support triage. Consult it BEFORE building support;
`docs/notes/2026-07-23_mapping-plan-impact.md` carries the post-mapping
sequencing (capture/emission hardening first; LET/lambda is
core-path-blocking; prefer fork emission + recorded-step replay over
Lean-side reconstruction — retire, don't grow, the bridge inventory).

## Design invariants (binding — from the generality plan §7)

- **L1 — the open interface is the JUDGMENT layer.** Consolidations are
  fragment-local (own datatype, own soundness lemma) behind judgment `Prop`s;
  a monolithic `Derivation` inductive with one soundness theorem is prohibited.
- **L2 — `R` is an abstract relation, never an enum.** The rewrite judgment is
  parameterized by a value-level equivalence relation (equal/iff as instances);
  congruence lemmas indexed by (fn, position, R-in, R-out); user equivalences
  must land additively as congruence-rune recipes.
- **L3 — mandatory world-parametricity.** Every lemma/fragment is stated over
  an arbitrary `w : World`; concrete-world constants inside fragments are
  prohibited (keeps the encapsulate trajectory a statement-builder change).

## Fidelity (non-negotiable)

- **A verdict may gate ADMISSIBILITY (which lemma applies); it may NEVER
  substitute for proof.** Trusting ACL2 is forbidden in all circumstances, no
  exceptions. Assumed facts exist only as visible `sorryAx` debt (registered,
  receipt-carried, gate-retired) — acceptable during buildout ONLY; the win
  state is ZERO `sorryAx` anywhere (Mike, 2026-08-13).
- **Known fidelity bugs go in `docs/BUGS.md` — the SINGLE canonical index.**
  Total faithfulness to ACL2 is the goal, so any interpreter/trusted-core
  divergence from real ACL2 is definitionally a bug. Log it in `docs/BUGS.md`
  (numbered `BUG-NNN`), don't scatter it in prose. Where it can be, pin it with
  a self-enforcing differential `known-bug` entry tagged `bug:BUG-NNN`
  (`Tests/differential/`); `scripts/check-bugs.sh` (in `just ci`) cross-checks
  the index against the corpus so a bug can neither rot nor be silently dropped.
- **No skipped proofs in anything claimed done.** No `sorry`/`admit`/`axiom`/
  `native_decide` (native_decide is unsound) in work reported as complete. A goal
  is closed only when actually closed. `sorry` is allowed *only* as an explicit,
  called-out placeholder in acknowledged WIP — never silently, never in something
  presented as finished.
- **Mirror the tree; never shortcut to the goal.** The replay must reproduce
  ACL2's actual node chain (definition/recognizer/if-simplification/rewrite/
  equal-self/IH-as-rewriting-equivalence, etc.). Proving the theorem by a route
  the tree does not take — e.g. computing both sides and equating with `omega`/
  `decide`, or collapsing a node's children into one evaluator step — is a
  shortcut and does not count, even though the kernel accepts it.
- **Don't weaken the statement.** The replayed statement must be the real ACL2
  theorem — no contradictory/vacuous premises, no generalizing away the
  interesting case, while presenting it as the original.
- **No faking results.** Never claim a build passes, a proof checks, or
  `#print axioms` is clean without running it and seeing it. Report tool output
  faithfully; if a step was skipped or failed, say so with the output.
- **Fix, don't disable.** Never comment out / delete / skip a failing proof,
  lemma, test, or warning to make a target look green. Warnings (other than a
  called-out `sorry`) are unacceptable — fix the underlying code; never disable a
  linter.
- **The checker does no inference.** ACL2 already did the reasoning; Lean replays
  it deterministically — no heuristics, no search, no "figure it out." If the
  tree lacks the information to replay a step, that is missing ACL2 instrumentation
  to fix at the source (emit more), NOT a license to infer or paper over in Lean.
  **Hard-fail at frontiers.**
  - **Sole carve-out — decision-procedure LEAVES (ratified 2026-06-09).** Where ACL2
    itself closes a clause by a decision procedure with no internal proof record
    (tau-system, type-set/forward-chain contradiction, linear arithmetic — ACL2
    records only a verdict + rune set), the replay discharges that LEAF by a
    kernel-checked decision procedure in Lean (`omega`; `lean-smt` where needed) on
    the leaf's precisely-stated obligation (the emitted clause, lifted to the Logic
    primitives, with ACL2-emitted type facts as hypotheses). This is faithful at
    clause granularity — the clause tree, which IS ACL2's proof, stays mirrored
    exactly, and the leaf is discharged the way ACL2 itself regards it (a
    closed-form check). The carve-out applies ONLY to such leaves: rewrite chains,
    inductions, and every step ACL2 does record remain fully mirrored, and using
    `omega`/`decide`/SMT to shortcut THOSE is still forbidden (the anti-example
    above). A leaf with no emitted discharge node at all is still an emission gap —
    hard-fail. See `docs/plans/2026-06-09_direct-proof-emission.md`.
    **Extension — admission decrease obligations (MDD-ratified 2026-06-11).**
    The carve-out also covers a defun's ADMISSION decrease obligations: the
    EMITTED raw termination clauses (the per-recursive-call-site
    `(o< (acl2-count …) (acl2-count …))` facts under their ruling tests),
    which ACL2 closes at admission by the same verdict-only procedures. The
    totality prover discharges each emitted clause by the Count library +
    the in-scope branch facts — never an obligation ACL2 did not emit, and a
    call site with no covering emitted clause hard-fails. When ACL2 runs a
    REAL waterfall for a non-trivial admission, that proof should be logged
    and replayed instead (the `termination` field; tracked follow-up) — the
    carve-out covers only the verdict-class obligations.
- **Type facts come from ACL2, not Lean inference.** Consume the emitted
  `:TYPE-PRESCRIPTION` / type-set data (already parsed); if it is insufficient,
  add instrumentation rather than re-deriving types in the checker.
- **Never specialize the translator on particular examples.**
- **Never silently skip malformed input.** Parsers/processors hard-crash on
  unexpected input — no default-case swallowing, no `| _ => none`, no "skip
  unknown forms." Unexpected input means the input is wrong or the code is
  incomplete; surface it immediately.
- **Don't hand-edit generated artifacts** (generated worlds, theorem statements,
  proof objects) to make downstream proofs easier — fix the source or the proof.

If a task genuinely cannot be done honestly, say so and explain why, rather than
papering over it.

## Goal design (binding — MDD 2026-08-05)

Any goal the AGENT proposes MUST include an escape-hatch early-exit
condition that the agent itself can declare (e.g. "stop and report if the
remaining work all gates on user decisions, a ratified design boundary, or
a fork round-trip"). Any goal the USER proposes that lacks such an
early-exit condition MUST be flagged by the agent immediately, before
execution begins. Rationale (the 2026-08-05 close-out run): a
completion-only goal-keeper combined with an exit that requires user
sign-offs converts "no legal work remains" into open-ended grinding on
whatever is still touchable — the exact pressure under which per-case
accretion (the carve-out drift failure mode) happens.

## Working discipline (proof-directed, long-cycle)

Proof construction here is long-cycle work that has **failed more than once** by
building plausible pieces in isolation and only discovering they don't fit after a
large investment. The failure mode is structural, not a knowledge gap — guard
against it structurally:

- **Drive off the real artifact, never synthetic or mental-model shapes.** The
  ACL2 output is a *recursive clause tree* (`ClauseProof → ClauseNode`, with
  child clauses, induction pool-roots, and the per-literal `ProofNode` rewrite
  detail), not a flat list. Inspect the real thing —
  `lake exe acl2lean dump-proof-tree <file>` — before reasoning. Never validate
  against hand-built nodes or the flat `:REWRITE-STEP` log; both mislead about
  real shapes and how nodes compose.
  **Amendment (mapping arc, MDD-ratified 2026-07-22): synthetic BOOKS yes,
  synthetic ARTIFACTS never.** Deliberately-authored ACL2 books are allowed and
  encouraged when run through real ACL2 and the capture pipeline (the pattern
  corpus): anchor each family at a wild corpus occurrence, and draw its axes
  from what the generating ACL2 source actually branches on — never from
  imagination. Hand-built nodes, fabricated logs, and any artifact that did not
  come out of a real ACL2 run remain banned.
- **The real theorem is the unit of work.** Do not prove a lemma unless it is
  closing a specific goal in the actual target proof at that moment, with its
  statement read off the real goal. Write the proof skeleton first — one `sorry`
  per real tree node — then fill one `sorry` at a time. This makes "the lemma
  fits" true by construction.
- **A green lemma in isolation is a non-signal.** The only progress that counts is
  a `sorry` discharged *in the real theorem*, with the theorem building and
  `#print axioms` clean (`{propext, Classical.choice, Quot.sound}` — no `sorryAx`,
  no `native_decide`).
- **Banned anti-pattern: "build the infrastructure now, wire it into the real
  proof later."** There is no "later" where it gets validated; the wiring *is* the
  work, and skipping it is exactly what has caused the repeated failures.
- **Report mechanically, not with adjectives.** Do not say "faithful / complete /
  1:1 / on track" unless the real theorem builds with no `sorry` on its path and
  you can name the tree node each step replays. Otherwise report counts: "base
  case replays nodes 1–4 of 11; rest is `sorry`."
- **Small, checkable increments — surface them, don't run long.** Discuss design
  decisions and seek review before committing a proof as done or before building
  further on new infrastructure. Verify green + check `#print axioms` before any
  "done" claim. Commit/claim only what is verified.
- **Never merge (or push) without explicit, direct sign-off at the point of merge.**
  Do feature work on a branch (`mdd/...`), never directly on `main`. When a branch is
  ready to integrate, **pause, report it, and ask** — then merge ONLY if approved right
  then. Approval is never inferred from an earlier "merge it" or from the branch being
  green; it must be given at the moment of merge, for that specific merge. Same for
  `git push`. Prefer linear history (fast-forward merges); `--no-ff` is allowed but not
  the default.
  **Two-tier gating (MDD-ratified 2026-08-07).** The FULL `just claim-gate`
  (TRUE_EXIT=0 recorded in the commit) is REQUIRED at: phase/arc exits,
  merge candidates, golden re-pins, and any commit claiming green or
  complete. INTERMEDIATE commits inside a fix round may instead use a
  FAST-GATE — static checks (`lint-sh`, the check-* recipes) + build of
  the affected targets + focused `just replay` of the books the diff
  touches — and MUST say `fast-gate` (never `TRUE_EXIT=0`) in the commit
  message, so the tiers cannot masquerade. Batch gates within a fix
  round: intermediate builds catch compile errors; one full gate at the
  round's end is the honest claim point. (Rationale: the full gate is
  ~30 min and was serializing every increment; the masked-red-build
  incident that created the rule is covered by the claim-point tier.)
  **Sandbox protocol (MDD 2026-07-28): merges gate on LOCAL `just ci`, not remote CI.**
  Development runs inside a network-blocked sandbox, so autonomous remote-CI checks are
  impossible: a merge to local `main` requires local `just ci` green + sign-off, nothing
  more. Remote CI is validated at the next networked push (fix-forward if it breaks —
  revisit the protocol if that starts happening). Pushes themselves happen outside the
  sandbox and keep their full gate: run `just check-push-ready` (submodule pointer
  reachable from the fork remote — push the fork FIRST — plus the remote-CI conclusion),
  or the published main breaks every fresh checkout and CI at submodule init.
- **Keep `TODO.md` current.** The repo-root `TODO.md` is the running backlog across
  all tracks (A: the rewriting-replay driver; B: type-set/decision-procedure
  instrumentation; and the rest of the pipeline). Update it whenever a milestone
  lands, scope changes, or a new gap/frontier is found — don't let it drift from
  reality. **It is a BACKLOG, not a journal (restructured 2026-08-19):** per-arc
  narrative lives in the arc's charter (`docs/plans/`) or a dated note
  (`docs/notes/`), and the pre-2026-08-19 journal is preserved in
  `docs/archive/todo-history-2026.md`. In-flight arcs prepend short entries to
  the marked IN-FLIGHT ZONE at the head of the file; at arc exit, fold what
  survives into the live backlog and leave the narrative in the charter. When an
  item is done, DELETE it — the record is the charter's, not the backlog's.
- **Module-size norm (perf arc 3d, 2026-08-07).** New `.lean` modules stay
  under ~1500 lines and new LEMMA FAMILIES get their own module; the ci
  ratchet (`just check-file-weight`, baseline in
  `scripts/file-weight-baseline.txt`) enforces it — grandfathered giants
  may only shrink.
- **Heartbeat/resource-limit raises are a BAD SMELL (Mike, 2026-08-19).**
  An explicit heartbeat or recursion-limit increase indicates
  NON-SCALABLE tool design — usually a monolithic grind where a
  decomposed route exists. The default budget IS the tripwire, and we
  WANT it to fire: it is a sign of a performance issue to resolve.
  Raises are permitted only as TRANSITORY fixes and are by definition
  DEFECTS — each carries a minimal measured/bound comment plus a
  pointer to the TODO triage list, where it stays until the underlying
  shape is decomposed — unless judged unsolvable and explicitly
  approved by the user. No raise exists where the default suffices
  (deleted without residue), and no budget engineering in either
  direction: never snug corpus-calibrated bounds, never padded
  envelopes — the fix for an expensive site is decomposition, not a
  bigger number.
- **Take clean engineering-quality opportunities as you go.** Arc-by-arc buildout
  accumulates near-clones (the same helper re-derived in two walkers, the same
  composition idiom pasted at a third site). When a clean de-duplication /
  abstraction opportunity is NOTICED, take it — either immediately or as an
  end-of-arc increment on the branch that created it. Not an obsession, and never
  speculative generalization: extract only what exists in 2–3 concrete copies,
  behavior-preserving (golden byte-identical), each extraction its own verifiable
  step. The risk this manages is real: a fix applied to one clone silently missing
  its twin.

## Audit practices

Reviewers add the most value exactly where you cannot self-certify — and on this
project self-certification has been unreliable, so audit early and adversarially.

**The two-standard rule (MDD 2026-08-11) — what gets adversarial review.**
Adversarial, refute-by-default review (the pattern below) is reserved for the
things where wrongness matters regardless of intent: **semantics** (the
interpreter/trusted core vs real ACL2), **claims** (statements, axiom receipts,
goldens, anything reported as done), and **records** (proof logs, captured
artifacts, provenance). **Gates/lints/speedbumps are reviewed to the DETERRENT
standard instead**: does it catch the honest mistake, is it simple enough to
never be wrong, could we delete it — never "can a motivated construction evade
it" (it always can, by construction; that question manufactures infinite
hardening — gate whack-a-mole, where each hired adversary's escape breeds the
next, more fragile gate). Trust is discharged by DESIGN — kernel-checked
statements over the small trusted core — not by gates: a gate is a lightweight
speedbump against honest mistakes, never a barrier against circumvention, and
each one carries a comment saying exactly that ("do not harden it"). Fragile
gate cruft (count floors, name predicates, enumerated censuses that rot) is
ruthlessly deleted, never fixed by adding another gate; gate-cruft audits are
deletion reviews under the honest-mistake standard, not attack rounds.
Run the audit *before* claiming a milestone, not after building a mountain on it.
**Seek sign-off on the audit plan BEFORE triggering any subagent**: present the
plan (dimensions, agent count, model choice) together with a clean read on the
relative cost tradeoffs (e.g. N parallel reviewers + verification vs a couple of
Opus agents vs a single Fable agent), and launch only after approval. Audits are
token-expensive; the scale is the user's call, not an inferred default.
The proven pattern (encode it as a `Workflow` script; worked examples live in the
sibling `libsignal-theory` project):

1. **Ground-truth first.** Establish the factual state before any opinion: run the
   real build, capture `#print axioms` of the target theorem, note what actually
   fails. Don't let a reviewer reason from prose.
2. **Parallel adversarial reviewers, one per dimension.** Give each a skeptical
   persona ("the work is *probably subtly wrong* — find where," not "check it
   looks fine"), point it at **primary sources** (the real tree, the proof file,
   the upstream ACL2), and **decorrelate** — do not feed it your conclusions,
   confidence, or framing. For high stakes run an *inside* reviewer (faithful to
   our own sources/process?) and an *outside* reviewer (is it the right thing at
   all, judged independently?).
3. **Demand grounding.** Every finding anchored to `file:line`, tagged
   verbatim-vs-reconstructed, with an explicit list of what it could *not* verify.
   Have reviewers actually build and check axioms, not trust prose.
4. **Independently verify each finding.** A separate skeptic re-checks each
   falsifiable finding against the source, defaulting to *refute* if the evidence
   is thin or reconstructed.
5. **Synthesize honestly.** Don't average reviewers — drop refuted findings,
   adjudicate disagreement, and **spot-check the highest-stakes survivors
   yourself** before acting (a confident reviewer can be confidently wrong, and
   can miss things by searching one subtree). Credit what is genuinely strong.

## ACL2 instrumentation tagging (the `acl2/` submodule)

Our additions to ACL2 (stage 2) live in the `acl2/` submodule (branch
`acl2-lean-output`) as the diff vs upstream `master`. **Every region we insert carries
exactly one tag**, in a comment directly above it, that names and explains it:

```
; TRACE-LOG[<ns>/<label>]: <one-line purpose — what this instruments and why>
```

`<ns>` is one of three namespaces:
- **`emit/`** — writes to the structured proof log. Rewrite-step pushes (to
  `*structured-rewrite-log*` with `:origin '<sym>`) use `emit/<sym>` and obey the
  **round-trip rule**: the part after `emit/` MUST equal the emitted `:origin`. Direct
  top-level `fms` events use the keyword, lower-cased (`emit/step`, `emit/defthm`,
  `emit/induction`, `emit/defun`, `emit/qed`, …).
- **`suppress/`** — silences normal ACL2 output in `:structured` mode so stdout stays
  machine-parseable (`suppress/warnings`, `suppress/clause-body`, …).
- **`infra/`** — plumbing that emits nothing itself (globals, depth/path helpers, gstackp
  forcing, speculative rollback, the safe-mode list) — `infra/rewrite-log`,
  `infra/gstackp`, `infra/saved-log-tail`, …

Rules: **tag EVERYTHING** the fork inserts (so `grep -rn "TRACE-LOG\[" acl2/*.lisp` finds
every delta vs upstream — the maintenance/upstreaming invariant); one `;`-comment, above
the region, with a real purpose sentence; comments are inert in Lisp so tagging is a
zero-behavior change. The convention + the full survey are in
`docs/notes/2026-06-09_acl2-tagging-survey.md`; `just check-acl2-tags` enforces it
(no bare `; TRACE-LOG:`, all tags namespaced, every emitted origin round-trips) — run it
when adding instrumentation.

## Architecture

The module→stage map is the pipeline above. As a trust-boundary view:

```
Lean kernel (sole trust anchor)
├── Layer 1: SExpr semantic model + Logic primitives + evalOpt (trusted core)
├── Layer 2: Book translator: ACL2 .lisp → Lean World + replayed statement (untrusted)
└── Layer 3: Proof replay from ACL2 proof logs (untrusted, partially built)
```

Core type: `SExpr` (nil/atom/cons). Browse with `ls`/search rather than trusting a
static file map here.

## Build & commands

```sh
lake build                              # type-check everything (incl. tests)
just test                               # unit tests (#guard)
just ci                                 # conformance gate — build + tests; run before pushing
lake exe acl2lean dump-proof-tree <f>   # inspect the reconstructed proof TREE (use this)
lake exe acl2lean parse-proof-log <f>   # parse/display a raw proof trace
lake exe acl2lean gen-world <file>      # generate World + theorem stubs from .lisp
lake exe acl2lean eval "<expr>"         # evaluate an s-expression
```

Build system: Lake (`lakefile.toml`); toolchain pinned in `lean-toolchain`.
