# Master plan — from sorting to reusable word and machine-code proofs

**Governing plan, dated 2026-09-05.** The user accepted the direction of the
[assessment](../notes/2026-09-05_next-north-star-assessment.md) and requested
this goal sequence and an ambitious first goal for a long autonomous run.
This plan supersedes the **sequencing** of the
[2026-08-12 master plan](2026-08-12_master-plan.md). It retains that plan's
METRIC/PRODUCT distinction and Track FREE / Track REAL objectives. The
[lexicon](../LEXICON.md), [working rules](../../CLAUDE.md), and architectural
invariants L1–L3 remain binding.

**Current position:** **NS1 selected and its preflight choices settled.** The
[execution charter](2026-09-05_bvchop-foundation-charter.md) contains the
concrete first-goal contract. The long run started at C0 on 2026-09-05. On that date
the user authorized the full complex-rational migration and the proposed
two-reviewer design and final checkpoints. The charter records that standing
authorization; it is not to be requested again during the run.

**2026-09-07 execution update:** following the paused project check-in, the
next slice is [NS1-R](2026-09-07_ns1-replay-mechanisms-plan.md): source-based
probing and consolidation of reusable type-query and clause-edit replay,
validated by complete arithmetic dependencies and separate reuse witnesses.
It continues in the existing NS1 worktree. Its bounded acceptance criteria
do not change the three NS1 native targets or constitute C2 completion;
the broader mirror campaign remains paused while this plan is prepared.

## Destination and operating model

Make ACL2Lean a tool with which a Lean developer can import a useful ACL2 book,
declare native definitions and correspondence information, and receive
kernel-checked native theorems through replay. Subsequent books within a
supported family should require declarations, not changes to the replay
driver or handwritten theorem-specific proofs.

The near-term product is a small Kestrel word-arithmetic library. The
longer-term product is the native counterpart of **`x86-popcount-32-correct`**
from `projects/x86isa/proofs/popcount/popcount.lisp`: execution of the specified
instruction bytes reaches the specified halt address with the population
count in the result register. Neither importing the ISA definitions nor
proving a standalone arithmetic identity meets that target.

**Target-selection preference (user clarification, 2026-09-05):** choose
native statements that are easy to understand but substantial to prove,
requiring the algorithmic or program-specific reasoning supplied by the
book. A useful "shop window" should be unlikely to close accidentally through
routine Lean automation or existing library lemmas. This reduces the chance
of an unnoticed alternative proof and demonstrates the value of importing
the book. It is additional evidence, never a substitute for checking the
actual replay route and attribution. NS1's elementary modular-arithmetic
laws remain the agreed foundation targets; later target selection should
give this criterion more weight, within the declared supported family.

Two measures govern the work:

- **Track FREE:** source/capture → replayed statement → waypoint, with no
  per-theorem handwritten Lean assembly for an established family.
- **Track REAL:** native definitions/statements plus refinement declarations
  → mirrors, with generated correspondence and transport proofs. Count all
  required user input, including setup, not just the final transport command.

Broaden the machinery at a real blocked theorem. Validate that broadening on
a different example before claiming a reusable capability. Sorting remains
the regression corpus. The assessment's successful capture of `bvchop` is
not replay coverage: its full log currently fails parsing at `#C`, BUG-009.
Dependencies beyond that boundary are still to be measured.

## Goal sequence

The `NS` prefix distinguishes these goals from the historical G/R/B/C arc
labels. Every row states a success condition and a non-success early exit.
A checkpoint or blocker report never counts as completing its parent goal.

| Goal | Dependency | Concrete end state | Agent-declarable early exit |
| --- | --- | --- | --- |
| **NS1 — Three complete word-truncation mirrors** | First goal | Replay and mirror `bvchop-upper-bound`, `bvchop-of-bvchop-same`, and `bvchop-identity` from the unmodified Kestrel book, including every required dependency. Repair the complex-number semantic boundary within the agreed charter. Preserve all existing products and replay coverage. | Stop if the only remaining routes require a new trust/fidelity policy, an excluded proof mechanism, unavailable external state, or a change to the approved native statements. Report the exact obstruction and remaining obligations. |
| **NS2 — Word addition and concatenation** | NS1 | Add `bvplus-associative`, `bvplus-commutative`, and `bvchop-of-bvcat-same`, for **six selected word-library mirrors in total**. Add the required four-argument correspondence and width/word refinements through those proofs. | Stop if a new semantic or proof-backend boundary outside the agreed word-library scope is unavoidable. Do not replace a target with an easier identity or hand-prove a missing dependency. |
| **NS3 — Reusable book importer** | NS2 | The existing book preparation, dependency reuse, generation, and transport become a reusable import path. A previously unworked book, selected after the supported-family contract is frozen, imports without editing replay internals or writing theorem-specific Lean proof glue. Same-named functions in independent developments are safely scoped. | If the held-out import requires a missing mechanism, record the failed experiment. Extend that family only with an explicit new target, then test another held-out book; do not silently move the acceptance boundary. Stop if the necessary extension leaves the agreed domain. |
| **NS4 — A usable word-library release candidate** | NS3 | A fresh checkout and a separate Lean consumer reproduce the supported imports with documented commands, pinned inputs, checked artifacts, and useful diagnostics. A consumer derives a small application fact using the imported results. Core tooling builds without every example log. | Stop the readiness claim if reproduction requires undocumented local state, hand-editing the coverage harness, unreported proof conditions, or an unavailable validation dependency. Preserve the working candidate and report the missing requirement. |
| **NS5 — A checked GL proof on the x86 route** | NS4; scheduled before expensive ISA integration | Capture and replay the actual `x86-popcount-32-symbolic-simulation-helper` in `popcount-general.lisp`, including the GL transformations and final checked obligation, with an explicit account of the supported GL fragment. This is a proof-capability milestone, not x86 program correctness. | First produce the evidence/translation design. Stop before implementing any route that expands the ratified DP-leaf exception or introduces a trust assumption without a new ruling. Stop if the chosen fragment cannot cover this actual proof. |
| **NS6 — Native x86 state operations** | NS4; normally after NS5 validates the proof route | Replay the real `xr`/`xw` same-field, different-field, and read-back laws needed by popcount, with a native state representation and generated operation correspondence. Capture the generated declarations and required stobj/record constraints from the pinned world. | Stop if the abstract/nested state interface cannot be represented with the agreed logical semantics, if required evidence is unavailable, or if the only route changes the intended state observations. A toy substitute state does not close this goal. |
| **NS7 — Native x86 popcount program correctness** | NS5 + NS6 | A complete native mirror of `x86-popcount-32-correct`, including setup, final register value, halt address, and the source theorem's other conclusions. All machine, arithmetic, GL, and state dependencies are discharged through the supported routes. | Stop for an unavoidable unapproved mechanism, source/spec mismatch, or external blocker. A partial symbolic simulation or arithmetic popcount lemma is reported only as partial progress. |
| **NS8 — Reuse on a second machine-code program** | NS7 | Import a distinct program chosen within the demonstrated ISA/proof fragment, using the same state and instruction refinements. Publish the supported scope, user work, and changed-program performance with a release candidate. | If the second program needs new ISA/proof support, record that as a failed reuse test and scope the extension explicitly. Do not present one program's success as full x86isa support. |

NS5 and NS6 have partly independent prerequisites; this does not authorize
parallel agents. Prefer settling the GL evidence route first, since it could
invalidate a large investment in state and interpreter integration. Each
later goal gets a concrete execution charter before its long run, using
the artifacts and measurements produced by its predecessors.

## Scope of the word-library goals

The selected books are the pinned sources under `acl2/books/kestrel/bv/`:

| Book | Required selected results | Native content |
| --- | --- | --- |
| `bvchop.lisp` | `bvchop-upper-bound`, `bvchop-of-bvchop-same`, `bvchop-identity` | Truncation bound, idempotence, identity on bounded inputs |
| `bvplus.lisp` | `bvplus-associative`, `bvplus-commutative` | Modular-addition algebra |
| `bvcat.lisp` | `bvchop-of-bvcat-same` | Concatenation fits the combined width |

These six results and their transitive proof obligations are the commitment,
not every theorem in those books or all of `kestrel/bv`. Ingest complete,
well-formed captures; report nonselected unsupported rows explicitly. Do not
filter malformed records, edit logs, or remove upstream hypotheses to create
an accepted input. An included theorem statement without its proof tree is
a dependency demand, not evidence of its truth.

NS1 begins with a natural width and integer input/result, matching the
book's total logical truncation on that typed domain. Its charter pins the
three native formulas. Width-indexed `BitVec` interfaces can be added when
their refinement is needed by NS2 or an actual consumer. Representational
choices must not restrict the replayed statement's ACL2 value domain or
quietly narrow a native theorem to width 32, positive inputs, or positive
widths.

The named opportunities from the assessment are part of the goal that first
requires them: primitive/exec/lift consistency, arity-generic correspondence,
emitted measure extraction, scoped kit registration, generated decode
assembly, dependency orchestration, and retiring sorting-specific route
tests. They are not separate infrastructure projects with a promise to find
a consumer later.

## What makes NS3 and NS4 a tool rather than another demonstration

Freeze an explicit supported-family contract before choosing the held-out
book: source environment, data/operation families, replay mechanisms, and
representation shapes. The new book's source and theory remain unchanged.
Report both accepted selected results and unsupported surface; a book is
not “supported” merely because one easy theorem succeeds.

The importer must own the setup currently spread across the coverage harness
and waypoint modules: dependency identities and source hashes, package and
certification context where needed, world construction, existing checked
world transport/re-replay, totality and rule discharge, execution generation,
decode assembly, and artifact registration. Reuse the current working
mechanisms. The supported caller should not need to reproduce `covDeps` or
the functional-instantiation pre-pass by hand.

Acceptance includes explicit status for the requested theorem: a checked
result, a conditional/unsupported result with its obligations, or a capture,
parse, or reconstruction error. A process exit of zero accompanied by failed
rows is not a successful import. Record the proof/source mapping and axiom
receipt with the result. Invalidation must follow the real source, fork,
toolchain, representation, and dependency inputs; a stale cached proof must
not masquerade as a newly imported theorem.

Keep the public workflow small: identify the book and requested result,
declare the native statement and refinements, build, then import the result
from another Lean module. A general Lean-to-ACL2 tactic frontend and a full
source-side `gen-world` replacement are not prerequisites. Nor is a large
new set of gates: extend the existing checks where there is a concrete need.

## Fidelity, regression, and evidence

Every completed proof goal requires the following evidence:

1. Source/fork provenance and the actual reconstructed proof trees, with the
   selected ACL2 statements and native counterparts reviewed together.
2. All selected replayed statements and their supporting obligations closed;
   no unresolved `rule:`, `total:`, `tp:`, or equivalent conditions on the
   delivered products. General native mathematical hypotheses are retained
   exactly as specified; they are not replay debt.
3. Complete mirror proofs through replay, with the established axiom receipts,
   seam, purity, and naming checks. No `sorry`, `admit`, `sorryAx`, extra
   axioms, or `native_decide` on delivered proof paths.
4. Existing products preserved. Semantic extensions may legitimately change
   internal proof terms and receipts about the expanded value space; they do
   not authorize weakening the existing native statements or deleting tests.
   Any required golden change is explained row by row and deliberately
   re-pinned under the existing full-gate protocol.
5. A recorded full `just claim-gate` at the required goal/arc exit, plus the
   existing independent product-validation route for new mirrors. During
   implementation, use focused builds and relevant tests, reserving full
   gates for meaningful claim points rather than every edit.

Capture ordinary book dependencies and replay their proofs instead of adding
new per-rune hand proofs to the uncaptured-book part of `GzRules`. Use the
ratified decision-procedure fallback only at the emitted obligations it
covers. Missing rewrite/induction evidence is an instrumentation task, never
permission for Lean-side search. GL and arbitrary clause processors do not
become permitted opaque leaves merely because a kernel-checked solver exists.

Measure one-time implementation cost separately from user effort per later
import. Record capture, parsing, reconstruction, proof construction/checking,
peak memory, artifact size, and warm rebuild cost at the precision available.
Do not call an aggregate runner timer kernel time. Fix expensive proof/data
shapes through decomposition; heartbeat inflation is not a milestone.

## Long-cycle execution and decisions

The first goal's charter is designed to settle substantive choices before
launch. Once its scope is agreed, ordinary implementation choices, focused
tests, source-compatible emission fixes, and repairs required by an agreed
semantic migration belong to the agent. Internal checkpoints produce durable
evidence and progress reports; they do not ask the user to authorize the same
work again. Keep a short in-flight TODO entry and a resumable charter record
of the current artifact, exact frontier, decisions, and next action.

Each goal has two distinct terminal reports: **completed**, with its evidence,
or **stopped incomplete**, with its early-exit reason and reviewable partial
work. A difficult proof or a newly encountered ordinary frontier is not by
itself an early exit: pursue the in-scope recorded route. If all remaining
legal work requires a new ruling or unavailable external state, stop rather
than work indefinitely on unrelated code. Resource exhaustion is not success.

Review allocation for NS1 is recorded in its charter. No implementation
subagents or recurring review campaigns are authorized merely by this plan.
Local branch work can proceed under the agreed scope. Merge, push, external
publication, and release actions retain their explicit sign-off boundaries;
an autonomous run should finish with a reviewable candidate before asking.

The records-book fallback remains available **by a new scope decision**, not
as an automatic way to call NS1 complete. M1, order-generic sorting, broad
package completeness beyond demanded imports, all pattern rows, system-view
x86, floating-point coverage, and the full ISA remain outside this sequence
unless a selected goal requires and explicitly scopes them.

NS4/NS8 produce release candidates under the
[versioning policy](../notes/2026-08-19_versioning-policy.md). This plan does
not assign a release number, authorize publication, or declare that one x86
program satisfies the policy's full-scale 1.0 bar.

## Planning record

- **2026-09-05:** assessment direction accepted; this successor sequence
  written; NS1 selected and chartered. The user then authorized ownership of
  the complex migration and the proposed subagent reviews. The approved docs
  were committed on `main` as `b452b70`, then NS1 launched in the
  `mdd/ns1-bvchop` worktree. C0 baseline, native specifications and both
  numeric-design reviews are checked; C1 semantic migration is next.
  No new mirror proof is complete. Receipts are in the NS1 charter.
