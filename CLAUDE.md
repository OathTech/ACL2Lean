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
   in `rewrite.lisp` / `simplify.lisp` / `axioms.lisp`)* — emits a structured
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
5. **Source translation** — `WorldGen.lean` / `Translator.lean` (`gen-world`):
   translates the *same* ACL2 source into a Lean **`World`** (function name →
   (formals, body) as `SExpr`) and the **mirror-theorem statement**, of the form
   `∃ N, ∀ f ≥ N, evalOpt f world env <thm>Formula = some t`. This stage decides
   *what theorem we are proving*.
6. **ACL2-logic interpreter** — `EvalOpt.lean` (`evalOpt`, fuel-bounded) +
   `Logic.lean` (the primitives): the Lean semantic model that *defines what the
   mirror theorem means*. If this diverges from ACL2's semantics, a "correct"
   proof proves the wrong thing.
7. **Proof-object builder** — `Replay/ProofProducer.lean` (a `MetaM` procedure,
   the eventual `acl2_replay` tactic) + `Replay/EvalLemmas.lean` (atomic step
   lemmas): recurses the proof tree and emits a Lean **`Expr`** discharging the
   mirror theorem; the **Lean kernel** then checks it.

**End goal — ACL2 as an untrusted Lean tactic.** The reason to produce the mirror
theorem is to discharge a *native Lean theorem* we actually want. Given a desired
Lean statement (e.g. `1 + 1 = 2` in Lean's own terms), we prove **in Lean,
kernel-checked**, that it follows from the mirror-theorem statement under the
interpreter — turning an ACL2 proof into a Lean proof of the same fact. Because
that final bridge is kernel-checked and the desired theorem is stated in Lean's
native semantics, **the entire ACL2 pipeline (stages 1–7) becomes untrusted**: a
bug anywhere makes the composed proof fail to typecheck — it can never yield a
false theorem. ACL2 then serves as a sound (if incomplete) untrusted tactic inside
Lean proofs.

**Trust note — read this.** That fully-untrusted property holds *only once the
final native-theorem bridge exists*. Today there is no such bridge: the mirror
theorem is stated in `evalOpt` terms, and the kernel certifies only that the proof
object is valid *for the mirror theorem exactly as stated in stages 5–6* — NOT
that the mirror faithfully restates the ACL2 theorem, nor that `evalOpt` faithfully
models ACL2. So at present a bug in stages 2–6 can produce a kernel-accepted proof
of a subtly wrong statement. When something looks off, **suspect any stage** —
wrong instrumentation, a mis-parsed or mis-shaped tree, a mistranslated `World` or
mirror statement, an `evalOpt` that diverges from ACL2, or a replay that proves
something slightly different. Do not assume the bug is where it is most convenient
to look; only ACL2's proof *search* is off the table.

**Current status.** Stages 1–4 — ACL2 instrumentation (incl. induction measure
justifications, preprocess chains + clausify checkpoints, and decision-procedure
discharge nodes), proof-log parsing, and proof-tree reconstruction
(`buildDevelopment`) — are built and validated against the sample corpus
(`acl2_samples/`, incl. `recon-tests/` 00–16). The proof-object builder (stage 7)
replays whole theorems end-to-end from the real logs — including WF-induction
(`my-len-my-app`, `app-assoc`), preprocess/clausify composition, and (under the
ratified carve-out) DP leaves — kernel-checked, conditional on emitted
totality/TP facts; the coverage harness (`just ci`) is the scoreboard. The
native-theorem bridge exists as validated HAND proofs (`Imported/`).
**The governing plan is `docs/plans/2026-06-10_generality-design.md`** (ratified;
built on `docs/notes/2026-06-10_acl2-architecture-survey.md`): the hybrid
architecture (certifying walkers as the lane, fragment-local consolidation), the
six-step sequencing, and the core/extended/out import tiers. The trust note still
applies — a kernel-accepted proof object certifies only the mirror theorem as
stated, not that the mirror/`evalOpt` faithfully model ACL2 — so keep checking
each stage against the real artifact.

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
- **Don't weaken the statement.** The mirror theorem must be the real ACL2
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
- **Keep `TODO.md` current.** The repo-root `TODO.md` is the running backlog across
  all tracks (A: the rewriting-replay driver; B: type-set/decision-procedure
  instrumentation; and the rest of the pipeline). Update it whenever a milestone
  lands, scope changes, or a new gap/frontier is found — don't let it drift from
  reality.

## Audit practices

Reviewers add the most value exactly where you cannot self-certify — and on this
project self-certification has been unreliable, so audit early and adversarially.
Run the audit *before* claiming a milestone, not after building a mountain on it.
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
├── Layer 2: Book translator: ACL2 .lisp → Lean World + mirror statement (untrusted)
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
