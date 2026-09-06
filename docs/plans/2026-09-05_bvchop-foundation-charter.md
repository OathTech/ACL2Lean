# NS1 charter — three word-truncation mirrors and their semantic foundation

Dated 2026-09-05. First goal of the
[post-sorting master plan](2026-09-05_master-plan.md).
**Status: C0 and C1 checked; C2 first-mirror work in progress. NS1 incomplete.**
The strategic direction and preflight choices are agreed. On 2026-09-05 the
user explicitly authorized ownership of the complex migration and the
subagents proposed below. Those authorizations persist throughout this goal;
do not ask for them again.

## The goal

From the pinned, unmodified `kestrel/bv/bvchop.lisp`, deliver **three complete
native Lean mirrors**: truncation is bounded, truncating twice is the same
as truncating once, and truncation preserves values already in range.
Their proofs must come through faithful ACL2 replay, with every required
dependency discharged. Include the semantic and generator repairs necessary
to make that import work, and preserve all existing sorting/Basics products.

This deliberately combines the assessment's feasibility work and first
product increment into one ambitious goal. Its end state is not a report,
parser support, a successful capture, or one isolated generic lemma. Internal
checkpoints make the prerequisite work reviewable without converting each
one into another user interaction.

**Early exit:** stop incomplete if every remaining route requires an
unapproved semantic scope, a new fidelity/trust ruling, an excluded proof
mechanism, a change to the three native specifications, or unavailable
external state. Name the actual artifact/node, remaining conditions, and
smallest decision that would reopen progress. A newly encountered replay
frontier within the agreed scope is work to do, not a reason to stop.

## Exact result contract

The source theorem names and formulas are in
[`bvchop.lisp`](../../acl2/books/kestrel/bv/bvchop.lisp). Its operation is
defined in [`bvchop-def.lisp`](../../acl2/books/kestrel/bv/bvchop-def.lisp) by
`(mod (ifix x) (expt 2 (nfix size)))` on the logical path.

The native specification uses **all natural widths and all integer
inputs**, including width zero and negative inputs. The following declarations
are implemented in [`Mirrors/WordOps.lean`](../../ACL2Lean/Mirrors/WordOps.lean);
their proofs remain the goal of NS1:

```lean
namespace ACL2Lean.WordOps

def wordClip (width : Nat) (value : Int) : Int :=
  value % (2 : Int) ^ width

def wordClipBound : Prop :=
  ∀ (width : Nat) (value : Int),
    wordClip width value < (2 : Int) ^ width

def wordClipIdempotent : Prop :=
  ∀ (width : Nat) (value : Int),
    wordClip width (wordClip width value) = wordClip width value

def wordClipIdentity : Prop :=
  ∀ (width : Nat) (value : Int),
    0 ≤ value → value < (2 : Int) ^ width → wordClip width value = value

end ACL2Lean.WordOps
```

| Native proposition | ACL2 theorem consumed |
| --- | --- |
| `wordClipBound` | `bvchop-upper-bound` |
| `wordClipIdempotent` | `bvchop-of-bvchop-same` |
| `wordClipIdentity` | `bvchop-identity`, with the generic correspondence between `unsigned-byte-p` and the stated integer bounds |

The names passed the existing collision linter at C0. The mathematical
formulas are the contract. The bound does not
silently add a separate nonnegativity theorem; additional useful results
belong to their own replayed source facts.

The `%`/power definition must be connected to the ACL2 logical operation by
a kernel-checked generic correspondence. Proving idempotence directly with
a Lean modulo lemma is not that correspondence and does not count as the
target proof. Generic representation/core-logic proofs are allowed; book
theorem content always enters through replay. The underlying replayed
statements retain their actual untyped ACL2 formulas. The native results
are explicitly typed restrictions, not claims of unrestricted equivalence
between the Lean and ACL2 value universes.

**Shop-window limitation (2026-09-05):** these are elementary modular laws,
so they offer limited protection against accidentally proving the result
through existing Lean arithmetic lemmas. They remain the agreed NS1 targets
because they exercise the semantic migration and the complete mirror path.
The master's target-selection preference favors more substantial proofs in
later goals. NS1 must establish faithful use of replay through the actual
proof route; the difficulty of its native propositions supplies little
independent evidence of that attribution.

## Starting evidence and the main risk

The [assessment](../notes/2026-09-05_next-north-star-assessment.md) records
the baseline at ACL2Lean `06ccb8e` / `v0.1.0`, Lean 4.33.0, and fork
`e8d78e513d6867d04002f0df644da1723cc96e89`. A fresh capture of `bvchop`
completed with 116 QEDs for 116 local theorem events, but the complete log
fails parsing on `#C(0 1)` in an included arithmetic theorem. No `bvchop`
proof tree or downstream replay frontier has yet been measured.

The agreed remedy is a proper repair of **BUG-009**, not a parser token
that represents complex values incorrectly or discards the offending event.
Adding values to `SExpr` changes the domain quantified over by existing
proofs. The migration must account for all of the following:

- Canonical exact complex-rational values: rational components, normalization
  to an existing rational when the imaginary component is zero, and no
  duplicate or nested-complex representations. Preserve the canonical
  rational guarantees established for BUG-012.
- Reader, printer, equality, reflection, and primitive evaluation on the
  enlarged numeric domain. This includes arithmetic, recognizers,
  real/imaginary parts, and ACL2's actual completion behavior outside guards;
  measure the behavior against the pinned ACL2 implementation.
- The distinction between `RATIONALP` and `ACL2-NUMBERP`, and all proofs or
  DP registrations that currently exploit their coincidence.
- `ACL2-COUNT`, numeric/order semantics and order proofs, and the totality
  and induction branches currently closed because `COMPLEX-RATIONALP` is
  constantly false. Those branches need real proofs on the enlarged domain.
- Type-set index 6 becoming inhabited. Remove the complex-bit discount in
  `TsFacts.tsAcl2MaskOk` in the same coherent migration; retaining it is not
  an acceptable transitional completed state.
- Existing native embeddings, correspondence lemmas, stored rule proofs,
  differential classifications, and all generated consumers affected by the
  type change. Finish with BUG-009 closed under its actual semantic scope.

These are known impact areas, not a claim that the complete repair is already
designed. The first internal checkpoint must inspect all relevant source
sites and produce the concrete numeric representation/design before changing
the value model. It must not infer ACL2's complex arithmetic from Lean's
ordinary ordered-field intuitions.

## Work included in the agreed autonomous scope

The run owns the following without repeated permission requests:

1. The coherent numeric migration above and repairs required to preserve
   existing semantics, proofs, and products. Choose the concrete canonical
   representation and module decomposition against the stated invariants.
2. Capture and provenance of the selected book and its actual dependency
   proofs, including the necessary certification/package setup for those
   dependencies. Establish the exact selected proof closure as real trees
   become available; do not assume inclusion captured their proofs.
3. Source-compatible fork instrumentation fixes needed to replay recorded
   rewrite, induction, admission, or existing DP-leaf shapes on that closure.
   Tag changes, rebuild the image, recapture affected inputs, and keep the
   source book's statements, definitions, and proof hints unchanged.
4. General primitive/definition correspondence, execution generation,
   hypothesis discharge, and decode/transport extensions required by the
   three results. Add new core semantics only for justified ACL2 core
   operations; an ordinary library function does not become a trusted
   primitive merely to shorten its proof. Reuse existing world transport.
5. Removal of special cases encountered on this route, extraction from real
   repeated implementations, focused tests, bug-index updates, and measured
   decomposition of expensive terms. No unrelated cleanup campaign.
6. Integration of the three mirrors with the existing statement, seam,
   purity, naming, axiom, provenance, and independent-validation machinery.
   Prepare local commits and a merge candidate under the existing gate tiers.

The generator work must pay off inside NS1: the second and third results use
the first result's operation/representation kit and common decode machinery.
Do not write three bespoke Lean proofs and defer the shared route to NS3.
A fully general import frontend or a separate external-user acceptance
experiment is not required until NS3/NS4.

## Boundaries fixed before launch

| Topic | Agreed disposition |
| --- | --- |
| Numeric-domain migration | **Include the full BUG-009 repair and its regression consequences in NS1. Explicitly authorized 2026-09-05.** Choose and validate its concrete canonical representation at C0. |
| Native representation | Use the Nat-width / Int-input / Int-result specification above. Preserve negative inputs and width zero. `BitVec` ergonomics can follow when a consumer requires them. |
| Targets | All three named source theorems. Choose their implementation order from actual proof dependencies; no substitution of easier targets. |
| Capture and fork | Local instrumentation/capture changes within the existing fidelity contract are in scope. No modification of upstream book content or hints; no log surgery. |
| Additional proof mechanisms | General GL, arbitrary metafunction/clause-processor replay, a new SMT backend, forcing-round composition, and guard-proof replay are excluded from NS1. If one becomes unavoidable, present its actual obligation and stop for a scope decision. Do not skip the record. |
| Trust and glue | Existing kernel/trust/fidelity rules remain. No new axioms, solver verdict trust, or hand proofs of ordinary book dependencies. |
| Resource use | Use normal focused development and full claim points. Optimize measured bottlenecks; do not solve the run by permanent heartbeat/recursion-budget inflation. No wall-time or token estimate is asserted before the unknown proof closure is visible. |
| Parallel agents | Four review-only tasks are authorized, as specified below. No implementation delegation or extra review campaign is implied. |
| Integration | Finish with verified local work and a reviewable candidate. Merge, push, and publication still require their explicit point-of-action authorization. |
| Fallback | `misc/records.lisp` remains a proposed alternative only after reporting why NS1 stopped. Switching does not make this goal complete. |

## Internal checkpoints and completion receipts

Checkpoints are evidence and review points, not separate goals or automatic
requests for user approval. Continue after resolving findings within the
agreed scope. Preserve a coherent checked commit before a broad migration;
temporary WIP is labeled and never presented as a completed product.

| Checkpoint | Required artifact |
| --- | --- |
| **C0 — Establish the contract and numeric design** | Fresh baseline checks; capture reproduction; pure native spec; source-based numeric behavior/impact inventory; concrete canonical representation; scoped test plan. Review the design before building downstream proofs on it. |
| **C1 — Semantic migration closes the ingestion boundary** | BUG-009 repaired across the model and its affected proofs; relevant differential tests pass; real `bvchop` capture passes the complex-number boundary; existing coverage/products restored. Record any next parse/reconstruction frontier rather than claim replay success. This checkpoint alone does not complete NS1. |
| **C2 — First complete mirror** | Complete reconstruction of the selected capture and the needed dependency trees; one of the three named targets replayed and transported, conditions discharged, axiom receipt and exact source/spec pairing checked. Record the shared kit now used by the next target. |
| **C3 — All three results** | Three checked native mirrors; replayed dependency closure complete; common operation and decode routes used across the results; unselected book frontiers separately reported. No all-book coverage claim. |
| **C4 — Verified candidate** | All acceptance checks below pass; final independent review findings resolved; fresh full claim-gate artifact and independent product-validation evidence; concise change/risk summary ready for merge review. |

**Completion is the conjunction of these requirements:**

- The three native propositions have complete proofs, each consuming the
  corresponding source theorem through replay; no theorem-specific content
  proved by an alternative Lean route.
- All required proof, totality, type, and dependency obligations are closed.
  Native mathematical hypotheses such as the identity theorem's bounds are
  exactly those of the contract, not hidden replay conditions.
- Full complex-rational semantics in scope are implemented and
  differentially checked; BUG-009 and its documented domain-restriction
  adaptations are retired. Existing supported behaviors are preserved or
  corrected with explicit source evidence and regression pins.
- The baseline 116 theorem rows remain unconditional and all 21 existing
  native products retain their statements and accepted axiom receipts.
  Any representation-induced golden/proof movement is explained under the
  normal protocol; no failing result is removed. The three new products
  also pass the relevant purity/naming/seam/axiom checks.
- A fresh full `just claim-gate` records `TRUE_EXIT=0`. Extend and run the
  existing comparator/nanoda validation for the new native propositions.
  Missing external validation is reported honestly; it is not a passed gate.
- The charter records commands/artifact locations, source/fork/toolchain
  identities, the actual dependency closure, before/after timings at the
  measured granularity, and remaining unselected frontiers. TODO contains
  only surviving work from this arc; detailed history stays here or in its
  linked notes.

## Authorized review allocation

**Authorized by the user on 2026-09-05:** two reviewers at C0, and two at C4,
using the current session model. Total: four planned reviewer tasks plus
the primary agent's independent verification of findings. C0 reviewers
cover (a) numeric semantics/canonicity against ACL2 and (b) migration effects
on type sets, replay, and existing products. C4 reviewers cover (a) implemented
semantics/regressions and (b) source/statement attribution, replay fidelity,
conditions, and final axiom receipts. They read primary sources and run the
relevant checks; they do not simply endorse this charter.

The user selected this over the cheaper solo-review option. It bounds review
to two specific checkpoints instead of a standing agent team. No model change,
extra audit wave, or implementation delegation is implied by approval of
these four tasks. Review findings must be verified before changing code;
gates themselves retain the simpler honest-mistake standard.

The authorization is explicit because [CLAUDE.md](../../CLAUDE.md) says:
“Seek sign-off on the audit plan BEFORE triggering any subagent.” No
subagents were launched during planning. This requirement is satisfied for
the allocation above. Both C0 reviews have now run; the two C4 tasks remain
authorized for their concrete checkpoint artifacts, without requesting the
same approval again.

## C0 execution evidence

- **Fresh baseline:** invalidated coverage and ran `TMPDIR="$PWD/.tmp" just
  claim-gate` before changing proof code. Receipt
  `.gate-runs/b452b70-20260905T221458Z.log`, `TRUE_EXIT=0`; 116/116 rows
  unconditional and golden byte-identical. All existing product checks passed.
- **Fresh ACL2 image and capture:** the image's system-books directory points
  inside this worktree. The unchanged BVCHOP source produced 436,039 log lines
  and 116/116 QED/local-theorem events. Parsing still rejects `#C`. Source and
  log hashes, commands and probe transcripts are recorded in the
  [numeric design](../notes/2026-09-05_ns1-numeric-design.md).
- **Native specifications:** the four WordOps declarations build, and the
  existing naming linter reports 59 names with no collisions. No new mirror
  proof or product is claimed.
- **Reviews:** [numeric semantics](../audits/2026-09-05_ns1-c0-numeric-review.md)
  and [migration consequences](../audits/2026-09-05_ns1-c0-migration-review.md)
  completed. The primary independently checked the substantive findings;
  the design note records the adopted repairs. Newly reproduced BUG-028
  (zero-denominator reader) and BUG-029 (numeric term-weight saturation)
  are included in C1, alongside BUG-009.
- **Design:** canonical core `Rat` components, nonzero imaginary part,
  existing rational constructors preserved; exact ACL2-value count for
  replay count measures, separate from structural `consCount`; coherent
  type-set, ordering and completion changes. No additional scope ruling
  or review task is needed before implementation.
- **C0 gate after adding specs:** `TMPDIR="$PWD/.tmp" just claim-gate`,
  `.gate-runs/b452b70-20260905T223811Z.log`, `TRUE_EXIT=0`. This run reused
  the freshly checked baseline coverage artifacts; WordOps and its naming
  consumer were newly built. All existing products remain unchanged.

## C1 execution evidence (2026-09-06)

**C1 complete.** The full claim gate records `TRUE_EXIT=0` in
`.gate-runs/31d8e42-20260906T010720Z.log`. This run consumed the fresh
coverage/product rebuilds below and the repaired diagnostic test. The
adopted design is implemented across the value model, evaluator, reader,
reflection, order proofs, type sets and count measures. WordOps still contains
specifications only: C1 adds no new mirror product.

- Canonical complex values use core `Rat` components and a nonzero imaginary
  part. Arithmetic preserves rational fast paths and normalizes complex
  results. Numeric comparison follows real/imaginary order; alphorder places
  rationals before complexes. Reader errors remain separate from arithmetic
  completion. The full domain inhabits type-set bit 6; its discount is gone.
- Count/sum-count admission measures use exact `SExpr.valueCount`, including
  numeric and string contributions; structural `consCount` remains separate.
  Complex-component decrease consumes the emitted COMPLEX-RATIONALP ruler
  and the recorded obligation. Rational/complex term weights preserve both
  source saturation limits, including the public 499-cons boundary case.
- Unchanged, freshly captured `cov-complex` replays 2/2 unconditionally and
  `cov-complex-defun` 1/1. `Tests/ComplexReplay.lean` independently pins their
  source statements and rejects forbidden axioms. Receipts:
  `.tmp/ns1/c1-replay-complex-3.log`,
  `.tmp/ns1/c1-replay-complex-defun-2.log`, and
  `.tmp/ns1/c1-independent-products-refl-build.log`.
  Actual `COMPLEX-ADD` also checks over an abstract world with precisely
  `noshadow:EQUAL` and `noshadow:BINARY-+` premises
  (`.tmp/ns1/c1-complex-parametric.log`). These are replayed statements,
  not mirrors.
- **Full differential suite:** ordinary `TMPDIR="$PWD/.tmp" just diff-test`
  passes: 529 matches, 138 unsupported cases, 10 known bugs, 25 refusals,
  zero failures (`.tmp/ns1/c1-full-differential-thin.log`). Focused reader,
  reflection, numeric type-set, count and saturation tests also build.
- **Fresh coverage:** invalidated consumers and rebuilt
  `Tests.DriverCoverage`: 116/116 unconditional rows across 29 books; sections
  tile the unchanged golden, and `cmp Tests/driver-coverage.golden
  Tests/driver-coverage.actual` exits zero. Receipt:
  `.tmp/ns1/c1-fresh-coverage-post-intersection.log`. Sorting equivalence
  replays 3/3 in 676,932 ms (1018 seconds for the full module build).
- **Product regression:** the full build in
  `.gate-runs/31d8e42-20260906T004820Z.log` passed all 21 mirror seams and
  sorting equivalence (1070-second module build), including the final
  type-set marker repair. Its only failure was the diagnostic test below;
  the subsequent full gate passed. All product and replay receipts stay within
  `{propext, Classical.choice, Quot.sound}`.

Three concrete regressions determined the replay changes:

1. **EQUAL-CONS:** its actual tau leaf consumed 142,633,845 internal
   heartbeats after the migration. Generic negative-equality normalization
   and variable substitution reduce it to 175,568, with only `propext` in
   both isolated proofs. Normalization applies to the unsplit DP attempt;
   the constructor fallback retains its original recognizer forms.
   OrderedPerms builds; equality/linear books replay 6/6 unconditionally.
2. **Qsort:** the actual `Subgoal *1/3.1` identifies the arguments of a
   supposedly false lexorder test. Including existing reflexivity and
   constructor discrimination in that normalization pass closes the leaf
   in 205,530 internal heartbeats with accepted axioms
   (`.tmp/ns1/c1-qsort-refl-leaf.log`). The complete Qsort module then builds
   in 513 seconds, including HOW-MANY-FILTER-1 under its unchanged default
   limit (`.tmp/ns1/c1-qsort-refl-build.log`). This build overlapped other
   checks; it is not a controlled comparison with historical baseline
   timings. No resource limit was raised.
3. **CLASSIFY-POS:** in the full numeric domain, positivity mask 78 and
   negative mask 112 both include complex bit 6. The recorded false-test
   marker needs INTEGERP (23) intersected with positivity (78), yielding 6
   and excluding 112. The marker consumer now calls the existing one/two-fact
   algebra for the registered test mask's exact complement. Marker, cited
   rule restrictions and final result check remain required. The real book
   replays 2/2 unconditionally (`.tmp/ns1/c1-classify-intersection-replay.log`),
   and the fresh full coverage above includes this repair.

The DP runner now disables elaborator recovery on optional attempts. Previously
an omega failure could return an admitted result, correctly rejected by the
axiom guard before the intended fallback could run. A failed attempt now throws
and permits that fallback. The parametric instantiation regression builds;
actual Qsort HOW-MANY-APPEND/HOW-MANY-FILTER-1 replay unconditionally, including
all six emitted DP leaves (`.tmp/ns1/c1-qsort-filter-strict.log`). Closed
executable arithmetic and closed emitted DP leaves use kernel reduction of
core Rat operations; no recorded rewrite chain is replaced by a DP call.

The CLI now imports its interpreter, source-world generator and proof-tree
modules directly. It has no product-consuming commands; the former root import
made numerical differential tests wait for regeneration of all product proofs.
The smaller build has 32 jobs (`.tmp/ns1/c1-thin-cli-build.log`); `ACL2Lean`
is an explicit default Lake target, preserving full product checks in the gate.
The superseded differential build was stopped before any tests ran and is not
counted as a pass. Metadata, log parsing and tree dumping ran on the simple
book. Compiling `gen-world` output exposed a pre-existing positional Symbol
constructor missing its canonicity proof; the generator now uses the record
constructor. Regenerated output compiles (`.tmp/ns1/c1-cli-world-check.log`).
Its theorem stubs explicitly retain `sorry`: that command emits scaffolding,
not checked replay products.

The first full claim gate, `.gate-runs/31d8e42-20260906T004820Z.log`, found a
stale printed axiom receipt in `Tests.SpikeTauOmega`: the proof now also uses
`Classical.choice`, within the existing accepted set. The receipt and explicit
complex constructor branch were updated; the focused build passes
(`.tmp/ns1/c1-cli-spike-build.log`). The subsequent full gate passed as
recorded above. BUG-009, BUG-028 and BUG-029 are closed with these receipts.

## C2 ingestion preparation (2026-09-06)

These are parser/capture findings. The selected BVCHOP dependency closure has
not yet been established from reconstructed trees.

- After the complex reader repair, the unchanged BVCHOP dump rejects
  `REWRITE-STEP :PATH frame bkptr not a number/symbol: (RHS . 2)`
  (`.tmp/ns1/bvchop-dump-c1.log`). The first raw occurrence is line 21988,
  `(:PATH (((RHS . 2) . MOD)))`. ACL2's `relieve-hyp` passes this indexed
  boundary when rewriting the RHS of a binding hypothesis
  (`rewrite.lisp:19049`; predicate `type-set-b.lisp:7480`). A small authored
  ACL2 book, `.tmp/ns1/binding-hyp-probe.lisp`, was captured normally (2/2
  local proofs) and reproduces the same parser error. Its proof log and
  sidecar are in `.tmp/ns1/binding-hyp-capture/`; no trace was fabricated.
- Unchanged `bvchop-def` and `unsigned-byte-p` were captured to
  `.tmp/ns1/dependencies/bv/` with normal sidecars
  (`.tmp/ns1/dependency-capture-bv.log`). The former is rejected because
  it includes a BVCHOP guard-obligation proof; the latter reaches
  reconstruction but reports an unexpected `endBranch` inside a literal.
  Receipts: `.tmp/ns1/dependency-tree-{bvchop-def,unsigned-byte-p}.log`.
  Guard-proof replay remains excluded. These findings do not establish
  that every route to a selected logical theorem needs guard-proof replay.
- Captured `arithmetic-light/mod` (92/92 proofs) and `mod-and-expt` (18/18)
  also stop at indexed binding-RHS paths, respectively `(RHS . 5)` and
  `(RHS . 3)`. Receipts: `.tmp/ns1/dependency-tree-{mod,mod-and-expt}.log`.
- `expt2` was not promoted: the capture counter demands 43 local events,
  but the source repeats the identical EXPT-HACK theorem and ACL2 emits
  42 distinct local proofs, with QED for the final EXPT-SPLIT-HACK and a
  `CAPTURE-END :STATUS :COMPLETE` record. The attempt remains
  `.tmp/ns1/dependencies/arithmetic-light/expt2.proof-log.tmp`. No sidecar
  was forged and no completeness check was weakened. Positive handling
  of redundant source events is a separate ingestion issue if selected
  dependency demand reaches this book.

### C2 execution evidence (in progress)

The parser now preserves indexed binding-RHS boundaries as a distinct path
frame. Hypothesis replay partitions those chains by their recorded hypothesis
index, replays each actual RHS chain, and checks that its endpoint equals the
variable's final recorded substitution. The small real capture replays 2/2
unconditionally with zero DP leaves (`.tmp/ns1/c2-binding-hyp-replay.log`).
The parser and hypothesis-relief code were extracted from the existing large
modules; Node shrinks from 1650 to 1471 lines.

Two fork emission defects then blocked the unchanged book (BUG-030/031).
Ordinary definitions inside a local include were tagged as local witnesses;
the emitter now distinguishes ACL2's LOCAL-INCLUDE-BOOK flag from actual LOCAL
events. A type-alist contradiction also returned before END-LITERAL despite
having emitted BEGIN-LITERAL; the opening now occurs only on the path that
actually rewrites the literal. Both are instrumentation changes. No selected
source statement, hint, ACL2 proof-search decision or generated trace was edited.

Fresh actual captures from the rebuilt image are in
`.tmp/ns1/c2-balanced-captures/`: BVCHOP 116/116 local QEDs, MOD 92/92,
MOD-AND-EXPT 18/18 and UNSIGNED-BYTE-P 42/42. All four reconstruct successfully
(`.tmp/ns1/c2-balanced-*-tree.log`). The three selected proofs are now visible.
The dependency closure and replay remain to be established; a reconstructed
tree is not a replay result. These captures honestly stamp the dirty fork:
commit, rebuild after commit, recapture and provenance checks remain required.

New real pattern books are `cov-binding-hyp`, `cov-local-include-helper` and
`cov-local-include`. `Tests.Ns1Ingestion` builds the two binding theorems and
the include theorem with independent source-formula pins and the accepted
axiom set (`.tmp/ns1/c2-ingestion-pins-build.log`). Existing encapsulate
controls retain LOCAL-WITNESS and scoped reconstruction
(`.tmp/ns1/c2-provenance-cov-encapsulate-tree.log`). These focused checks are
not a C2 exit or full-corpus gate.

The first BVCHOP retry after registering existing IFIX/EXPT evaluator
operations reaches 1/9 conditional statements, none unconditional
(`.tmp/ns1/c2-bvchop-upper-registry-replay.log`). IFIX now has a named Logic
operation with unchanged semantics and the existing ground-zero agreement
lemma in the definition registry. The selected upper-bound proof stops at
BUG-032: collapse folds EXPT before ACL2 does. Two emitted DP leaves check;
three remain assumed and one hits the existing heartbeat limit. No budget
was raised. A direct probe of the actual admission closure identifies the
quotient's subtraction decrease, reciprocal registration and FLOOR/MOD
totality as the numeric prerequisites (`.tmp/ns1/c2-bvchop-totality-probe.log`).

The emitter control Qsort capture reconstructs, but its focused replay reports
10 unconditional, one conditional and two failed statements
(`.tmp/ns1/c2-emitter-qsort-deps-replay.log`). Moving BEGIN-LITERAL makes its
TA-SUBST records clause-level; that existing data arm did not thread them to
the existing directed substitution consumer. The thread is repaired and a
rerun is pending. CONS-TERM-GUARDS emission/replay is being added to the same
uncommitted fork batch. The in-memory binding-index rejection test passes
(`.tmp/ns1/c2-ingestion-negative-retry-build.log`).

The rebuilt image emits CONS-TERM-GUARDS from the entries ACL2 compiled into
`*cons-term1-alist*`, preserving their original formals and guards. The
parser retains that table, the book config carries it, and ground collapse
checks it before folding. This is closed evaluation of cons-term's
admissibility condition, not guard-obligation proof replay. Ground executable
evaluation's two existing fuel-discovery loops now share one helper with
the same ceiling. Fresh captures are in `.tmp/ns1/c2-primitive-captures/`;
the CLI and replay executable build (`.tmp/ns1/c2-cons-term-final-build.log`).
The real `cov-cons-term-fold` probe reconstructs both mechanisms: EXPT
survives to the next processor, CAR of a quoted cons folds while CAR of 0
survives to its later executable step. Both replay unconditionally, zero DP
leaves (`.tmp/ns1/c2-cons-term-probe-{tree,replay}.log`). Permanent source and
statement/axiom pins are added; the large BVCHOP/Qsort reruns are pending.

### C2 follow-up evidence (2026-09-06, still in progress)

The first emitter batch is committed in the fork at `599841344d9e`. Qsort
returned to 13/13 unconditional with nine checked DP leaves
(`.tmp/ns1/c2-qsort-primitive-replay.log`). Rebuild and `just recapture-all`
from that clean commit completed; all 95 then-existing logs passed provenance,
and all 65 then-existing pattern books passed their map checks
(`.tmp/ns1/c2-clean-{recapture-all,capture-checks}.log`).

BVCHOP-UPPER-BOUND now traverses the recorded structural chain but remains
ASSUMED, including MOD totality/type, MOD-OF-0-ARG1 and three DP facts
(`.tmp/ns1/c2-bvchop-upper-primitive-replay.log`). That is not a replayed
target. One remaining tau leaf times out at the existing limit; no limit
was raised. A later lowercase CLI target accidentally selected the whole
book; it was stopped and is not a target receipt. The CLI target argument
is case-sensitive: use `BVCHOP-UPPER-BOUND`.

The arithmetic admission walk now checks the quotient's subtraction decrease
under its emitted rulers, then handles FLOOR's translated LETs compositionally.
The actual BVCHOP admission probe constructs quotient, FLOOR, MOD and BVCHOP
totalities (`.tmp/ns1/c2-bvchop-totality-lambda-probe.log`). The new real
`cov-numeric-admission` book exposed two further composition gaps: function-level
totality hypotheses in fresh lambda environments, and recorded abbreviation
paths inside unopened lambda bodies. Both are implemented with world-parametric
congruence; the body equality is replayed for every environment, with outer
clause/value pins removed. `Tests.Ns1NumericAdmission` builds both independent
statement pins and accepted axiom receipts
(`.tmp/ns1/c2-lambda-path-pins-checked-build.log`). Ground computation was
extracted into GroundFold; Ctx is 1450 lines.

Standard `cert.pl` certification of FLOOR and its dependencies resolved the
missing IHS/U package setup (`.tmp/ns1/floor-certify-complete.log`). FLOOR then
exposed BUG-033: quoted package-import lists polluted the snapshot collector
with APPLY$/EV$. The flat and pretty quote printers now suspend collection
while preserving their output. This second fork batch is committed locally at
`8898d3e872`; its clean-image rebuild/recapture is in progress. No selected
source or hint changed, and the unavailable APPLY$ admission was not skipped.

The complete capture then exposed BUG-034/035: diagnostic strings inside
definitions were mistaken for actual errors, NUL suppressed grep's event census,
and Latin-1 bytes were rejected by Lean's UTF-8 reader. Capture now distinguishes
diagnostic lines, counts literal data as text, and transcodes encoding before
hashing/promotion. The real `cov-quoted-snapshot` book captures four statements;
nine ingestion pins and the binding-index negative control build
(`.tmp/ns1/c2-nine-ingestion-pins-final-build.log`). Its string pin independently
specifies H, character 0 and character 255. Static gates and actual-error
negative control pass (`.tmp/ns1/c2-quote-encoding-fast-static.log`).

FLOOR captures 125 local theorem events and 133 QEDs to
`.tmp/ns1/c2-primitive-captures/floor.proof-log`
(`.tmp/ns1/c2-floor-utf8-capture.log`). It next hits existing BUG-010 on a
qualified escaped symbol, `ACL2::|(CAR REMAINDER)|`
(`.tmp/ns1/c2-floor-utf8-tree.log`). This is an ingestion frontier; no FLOOR
dependency proof or new native mirror is claimed. TIMES' real *-OF-0 leaf is
also still ASSUMED (`.tmp/ns1/c2-times-zero-clean-retry.log`, which ran all
57 statements because its target argument was lowercase). These concrete
numeric/reader prerequisites are the next work.

The second fork batch's clean image rebuild and full corpus recapture now
complete successfully (`.tmp/ns1/c2-quote-clean-{image-build,recapture-all}.log`).
All 97 logs carry clean fork `8898d3e872` provenance; the 29 coverage books,
67 pattern books and provenance controls pass
(`.tmp/ns1/c2-quote-clean-capture-checks.log`). All six selected dependency
books also capture from that image, including FLOOR and BVCHOP
(`.tmp/ns1/c2-quote-clean-dependency-captures.log`).

This intermediate C2 checkpoint uses the fast-gate tier, not a phase-exit
claim. Static checks pass (`.tmp/ns1/c2-parent-fast-static.log`); all eleven
permanent ingestion/admission pins build with their accepted axiom receipts
(`.tmp/ns1/c2-clean-eleven-pins-build.log`). Focused numeric-admission and
quoted-data replay check 2/2 and 4/4 unconditionally, zero DP leaves
(`.tmp/ns1/c2-clean-{numeric-admission,quoted-data}-replay.log`). Qsort's final
clean-capture rerun checks 13/13 unconditionally and all nine DP leaves in
363782 ms (`.tmp/ns1/c2-quote-clean-qsort-replay.log`). C2 remains open;
there is no new BVCHOP mirror or full gate claim at this checkpoint.

### C2 reader and selected dependency work (2026-09-06, in progress)

Intermediate checkpoint `aec7fcd` records the previous fast-gate batch. The
next batch repairs BUG-010 with a general token reader: mixed single/multiple
escapes, qualified escaped names, escaped colons, and explicit empty names.
`Tests.ParserTest` pins the decoded identities. The focused differential run
checks 88 matches, two unsupported, one unrelated known bug and five refusals,
zero failures (`.tmp/ns1/c2-reader-corrected-differential.log`). The full FLOOR
log then exposed BUG-036, explanatory forcing-round prose after the structured
boundary. Suppression is repaired in the current dirty fork; both the real
FLOOR and forcing-pattern captures now fail precisely at the excluded forcing
round (`.tmp/ns1/c2-{floor-forcing-frontier,force-pattern}-clean-prose.log`).

For earlier dependencies, capture now exposes ACL2's native LD name filter
(`basis-b.lisp:4375`, `ld.lisp:1542`). `CAPTURE_THROUGH=THEOREM` loads the original
file in its original order through that named event and then emits the normal
snapshots/end manifest. No source/hint changes or log edits occur. The sidecar
records the prefix scope and hashes the entire source/include closure. The
shared completeness check requires the unique source stop event and its last
local QED. Real scoped FLOOR captures pass; removing or changing the scope
fails (`.tmp/ns1/c2-scoped-provenance-controls.log`). `capture-ns1-logs` makes
the selected TIMES/FLOOR/MOD prefixes reproducible under `recapture-all`.

TIMES' actual *-OF-0 verdict leaf now checks via generic primitive-number
simplification. The focused run checks that target unconditionally; the
preceding two unrelated failures remain visible (2/4 unconditional overall,
one checked target DP leaf; `.tmp/ns1/c2-times-zero-generic-dp-replay.log`).
`Tests.Ns1Arithmetic.timesZeroReplayed` builds with an independent formula pin
and accepted axioms (`.tmp/ns1/c2-times-zero-permanent-pin-build.log`). FLOOR's
selected zero theorem reconstructs, but exposed BUG-037: duplicated quotient
calls have computation records without positions. The six corresponding
abbreviation-walker emission sites now carry their actual paths, and replay
checks those paths. FLOOR-OF-0-ARG1 then replays unconditionally from the
actual dirty capture (1/4 overall, no DP leaves, 18015 ms;
`.tmp/ns1/c2-floor-zero-directed-path-replay.log`).

The clean full BVCHOP rerun retains 1/9 conditional statements, no unconditional
target (`.tmp/ns1/c2-bvchop-upper-clean-lambda-replay.log`, 219922 ms). Numeric
admission work removes totality/type conditions from the upper theorem's final
receipt; MOD-OF-0-ARG1, three assumed DP facts and one tau timeout remain. These
are open obligations, not a product or C2 completion claim.

The third fork batch is committed at `02f57ab31e79`. Its clean image rebuild
and `recapture-all` succeed (`.tmp/ns1/c2-path-clean-{image-build,recapture-all}.log`).
The shared static checks verify 100 clean logs at that fork, all 29 coverage
books, all 67 pattern books, and the parser/size/tag/purity gates
(`.tmp/ns1/c2-path-clean-static-checks.log`). The thirteen then-existing pins
build with accepted axioms (`.tmp/ns1/c2-path-clean-thirteen-pins-build.log`).
The transfer pre-pass reports that the complete TIMES world is not included
in FLOOR; the dependency tree is replayed in the consumer world instead.
This is visible in the receipt and the resulting proof remains unconditional.

MOD-OF-0-ARG1 now replays unconditionally from its actual source prefix and
the TIMES/FLOOR dependency trees (1/5 overall, no target DP leaves, 4929 ms;
`.tmp/ns1/c2-mod-zero-clean-chain-replay.log`). The four preceding MOD
statements retain their reported frontiers. All three zero-chain pins
now build with independent statements and accepted axiom receipts
(`.tmp/ns1/c2-clean-zero-chain-three-pins-build.log`), bringing these NS1
regression pins to fourteen. Fresh scoped-provenance controls also pass
(`.tmp/ns1/c2-path-clean-provenance-controls.log`).

The actual upper-bound Subgoal 1 DP statement checks with the new generic
primitive exponent-positivity lemma (arbitrary positive integer base and every
ACL2 exponent value). The strict standalone probe uses the production DP
tactic, kernel-checks its term and audits it for forbidden axioms
(`.tmp/ns1/c2-upper-tau-directed-primitive-probe.log`). The complete upper-bound
rerun now checks all three tau leaves and discharges the zero chain; three
linear leaves remain ASSUMED. BVCHOP-OF-0-ARG2 is unconditional (1/9 overall;
three checked, three assumed DP leaves, zero failed leaves, 48675 ms;
`.tmp/ns1/c2-bvchop-upper-clean-zero-chain-replay.log`). This is not a mirror. The next known arithmetic limitation is the linear
premise consumer's one-hypothesis/EQUAL-or-< restriction: the actual
MOD-BOUND-LINEAR-ARG2-STRONG has three hypotheses and a negated-< conclusion.

The full differential suite passes: 549 matches, 138 unsupported, seven known
bugs, 30 refusals, zero failures (`.tmp/ns1/c2-reader-full-differential.log`).
The first full gate found an abstract equisort statement-pin change: the DP
registry extension adds exactly `hnoshadow_UNARY-/`, `hnoshadow_IFIX` and
`hnoshadow_EXPT`. Each type is `w.defs.get? <that symbol> = none`; the full DP
no-shadow bundle consumes every registered head (`Driver/Discharge.lean:870`).
A separate checked copy of the statement pins verifies the source conclusion,
all six stored-rule constraints, the strong abstract interface and both
canonical kept-premise inventories unchanged
(`.tmp/ns1/c2-parametric-registry-review.log`). The weak abstract interface is
explicitly extended by those three semantic no-shadow requirements; its pin is
updated accordingly. This does not add a mathematical premise to a native
product. The first full gate ended with `TRUE_EXIT=1`, solely on that pin
(`.gate-runs/aec7fcd-20260906T031929Z.log`). It is retained as a failed
receipt. The reviewed rerun passes: `.gate-runs/aec7fcd-20260906T034924Z.log`,
`TRUE_EXIT=0`, 116/116 unconditional baseline statements, golden byte-identical,
all 21 existing mirror products and all 14 NS1 regression pins checked.
This closes the reader/capture repair batch, not C2 or any new mirror.

The NS1 capture recipe now runs standard Community Books feature setup and
`cert.pl` on TIMES/FLOOR/MOD first. This makes the included package definitions
available without the exploratory manual certificate setup. The hermetic
wrapper supplies SBCL's same `--no-sysinit` startup used by capture.
`just certify-ns1` succeeds
(`.tmp/ns1/c2-standard-certification-recipe.log`); fresh diagnostic captures
after certification are byte-identical to all three pinned prefix logs
(`.tmp/ns1/c2-certified-prefix-capture.log`). This verifies the setup change
without changing the running gate's embedded artifacts.

The clean fork's full FLOOR capture also completes all 125 source theorem
events (`.tmp/ns1/c2-floor-clean-full-capture.log`); parsing reaches the
explicit FORCING ROUND 1 frontier instead of failing on stray prose
(`.tmp/ns1/c2-floor-clean-full-forcing-frontier.log`). BUG-036 is the prose
bug and is fixed; forcing-round composition remains excluded and unimplemented.

### C2 linear and case composition (2026-09-06, in progress)

Checkpoint `d676937` records the validated reader/capture batch above. The next
batch extracts `LinearPremises` from Totality: all stored hypotheses and any
truthy conclusion are transported under the emitted max-term match, then
booleanized for the existing DP premise interface. The first actual upper-bound
run caught an application mismatch between `Logic.if_` and the lift's `cond`;
the premise lemmas now state the lift's exact Boolean encoding. That corrected
run retained two DP assumptions plus three linear-rule conditions
(`.tmp/ns1/c2-upper-general-linear-cond-shape-replay.log`); it was not a result.

The widening exposed BUG-038: the old snapshot scan offered ARG1 and ARG2 rules
although these three clauses cite only MOD-BOUND-LINEAR-ARG2-STRONG. Clause
replay now carries its own rune set and filters linear injection against it,
refreshing the set on child entry without deleting their offers. The first
filtered run retains all three DP assumptions and no extraneous linear rule
conditions (`.tmp/ns1/c2-upper-cited-linear-first-replay.log`, 114220 ms).
The existing 03-linear book remains 3/3 unconditional, three checked DP leaves
(`.tmp/ns1/c2-cited-linear-baseline-replay.log`). Full regression validation of
this batch remains open.

The recorded `:cases` partition is now composed by a general adapter consuming
all child proofs and checking their exact clauses. Actual MOD-BOUND-LINEAR-ARG2
has one case/two children; `cov-cases-hint` has two cases/three children. The
latter now reaches its three assumed arithmetic DP leaves rather than failing
at the case node (`.tmp/ns1/c2-cases-pattern-first-replay.log`). Tautology-dropped,
deduplicated or differently normalized case outputs remain explicit frontiers.

MOD's bound next required its emitted disjoint type-set masks (zero versus
positive rationals). The shared type-test registry now consumes RATIONALP as
mask 63, intersects it with the sign test's mask, and requests later clause
assumptions through the existing checked hoist. The actual theorem now passes
that equality and stops at PREFER-POSITIVE-ADDENDS-<'s recorded known-true
ACL2-NUMBERP hypothesis for an arithmetic result
(`.tmp/ns1/c2-mod-bound-rational-hoist-replay.log`). No new native mirror is
claimed. The three upper-bound leaves are being decomposed through generic
primitive numeric-order/exponent facts, with the production limits unchanged.

The numeric-order Boolean normalization closes actual Subgoal 6' in the
composed upper-bound replay; two DP assumptions remain
(`.tmp/ns1/c2-upper-boolean-full-replay.log`). A separate actual-node probe
then closes Subgoal 2' through generic comparison transitivity and exponent
positivity (`.tmp/ns1/c2-upper-linear-sg2-order-probe.log`). Subgoal 3 still
needs the integer-exponent fact to survive the DP simplifier's normalization.
These probes check their proof terms and axiom closure but are not a completed
replayed theorem or a native product.

BUG-039 records the two missing hypothesis-relief bases. The first fork image
build caught the new raw instrumentation's missing registration for
KNOWN-WHETHER-NIL and TYPE-SET-REC; registering those exact functions fixes the
build (`.tmp/ns1/c2-known-basis-registered-image-build.log`). A diagnostic
capture records the root query's actual argument mask and enabled tuple,
without repeating the query. MOD replay now passes the arithmetic-result fact
and stops at a distinct successful type-alist lookup for ACL2-NUMBERP Y
(`.tmp/ns1/c2-mod-bound-known-basis-replay.log`). The next emitter records that
lookup's matched entry and requested mask using the search's returned list
tail; its diagnostic capture completes 58/58 scoped source events
(`.tmp/ns1/c2-hyp-basis-diagnostic-capture.log`). These diagnostic logs explicitly
carry dirty-fork provenance and are not corpus pins. Clean-fork recapture and
the full gate remain necessary before any completion claim.

The hypothesis-basis consumers now replay MOD-BOUND-LINEAR-ARG2's whole
recorded tree, conditionally on eight explicit stored-rule dependencies and
with its sole DP leaf checked
(`.tmp/ns1/c2-mod-bound-numeric-product-replay.log`, 67252 ms). The dependencies
are MY-FLOOR-LOWER-BOUND-ALT, NORMALIZE-ADDENDS, PREFER-POSITIVE-ADDENDS-<,
|(+ 0 x)|, |(- (- x))|, |(* y x)|, |(+ x (- x))| and BUBBLE-DOWN-+-MATCH-1.
Its STRONG successor retains those same conditions plus one actual arithmetic
DP assumption (`.tmp/ns1/c2-mod-strong-directed-replay.log`). Neither bound is
unconditional yet. The multiplication closure is a primitive numeric fact,
consumed at the recorded known-true hypothesis for |(- (- x))|.

A capture control rebuilds the old fork under the current certificates,
recaptures the same MOD prefix, then restores the working fork and image
(`.tmp/ns1/c2-hyp-basis-control-run.log`). All 2083 control/new events agree
after erasing only the added hypothesis bases and lookup provenance
(`.tmp/ns1/c2-hyp-basis-control-event-comparison.log`). The differences against
the older diagnostic capture — certificate metadata and two duplicate TA-SUBST
records — also occur with the old fork under the current certificates.

The broad conditional-order simp rules caused a performance regression:
03-linear remained 3/3 unconditional, but its separate LINEAR-CHAIN DP check
hit the existing guard (`.tmp/ns1/c2-hyp-basis-linear-regression.log`, 205281 ms).
A narrower, conclusion-directed branch restores all three DP checks
(`.tmp/ns1/c2-directed-linear-regression.log`, 73380 ms), but is still too slow
and loses one previously checked BVCHOP leaf. Primitive literal views and
recognizer-preserving normalization are being tested before this batch can be
validated. No resource limit has been raised.

The next ordinary arithmetic dependency captures expose two distinct capture
census frontiers: basic.lisp's three DEFTHMs inside block comments, and
simplify.lisp's two redundant declarations of already included theorems.
Both are complete ACL2 runs that the current source-vs-local-count guard
rejects. Their unpromoted diagnostic outputs are retained; no count has been
lowered or capture check disabled. Collect's prefix through
BUBBLE-DOWN-+-MATCH-1 and normalize's prefix through NORMALIZE-ADDENDS captured
successfully; tree reconstruction and replay remain to be measured.

The capture-census fix (BUG-040) now promotes both actual outputs through
normal capture checks: basic.lisp has 93 explicit, uncommented source
theorems and 93 QEDs; simplify's selected prefix includes two redundant
already-included declarations. All existing negative provenance controls
still fail closed (`.tmp/ns1/c2-theorem-census-negative-gates.log`). The
basic and collect trees reconstruct. Normalize refuses at VERIFY-GUARDS for
FACTORS, simplify at VERIFY-GUARDS for ADDEND-VAL. Guard-obligation replay
remains excluded; neither tree has been silently trimmed or promoted to a
replay result. These are ingestion boundaries to resolve without claiming
any guard proof.

The exponent tactic is being isolated to obligations whose lifted statement
actually contains Logic.expt. The ordinary DP engine is kept as its separate
branch so unrelated numeric leaves do not pay for the new normalization.
The first quotation of that branch failed to typecheck (tactic versus
tacticSeq); the corrected quotation uses an explicit tactic category. Failed
build/attempt receipts are retained. Full upper-bound and baseline replays
remain pending on the final compiled version.

### C2 continued: dependency closure and guard-tree retention

The exponent-directed engine restores 03-linear's three unconditional rows and
three checked DP probes in 10003 ms; adding the unit-shift selector retains that
result in 10460 ms (`c2-exponent-gated-linear-final.log` and
`c2-unit-shift-linear-regression.log`, under `.tmp/ns1/`). The full upper-bound
row still carries one ASSUMED DP fact and its strong MOD-bound condition
(`c2-upper-exponent-gated-full-replay.log`). Actual Subgoal 3 checks with exactly
its recorded linear premise and emitted TP fact
(`c2-upper-sg3-exponent-gated-probe.log`). Subgoal 6's focused probe hits the
default 200k elaboration budget; this is unresolved, not a reason to raise it.

Collect's prefix reconstructs and BUBBLE-DOWN-+-MATCH-1 replays unconditionally
(`c2-arithmetic3-collect-bubble-replay.log`). The full basic-book sweep was
stopped after several minutes to restrict the next replay to the cited prefix;
`c2-arithmetic3-basic-full-replay.log` is not a completed validation receipt.

Guard-proof replay remains excluded. The ingestion change under construction
retains each VERIFY-GUARDS wrapper, its exact clause set, and its reconstructed
waterfall as a separate WorldEvent. It enforces QED/block boundaries, never
registers that event as a logical theorem, rule, or termination proof, and
reports it as UNSUPPORTED in tree/replay output. This is reconstruction of
unselected records, not a new proof mechanism: ACL2's total logical function
semantics do not depend on executable guards. A selected logical proof needing
a guard theorem would still have no registered evidence. No source, hint, or
record is removed. The actual normalize/simplify trees and the existing
cov-verify-guards capture are the validation inputs. Initial compilation failed
on two unavailable convenience APIs; those calls were corrected, with the
rebuild still pending. No new completeness claim follows from this change.

The guard reconstruction and boundary validation now pass. The actual
normalize capture retains 13 guard trees and simplify retains 15; their
logical theorem trees reconstruct (`c2-guard-admission-{normalize,simplify}-tree.log`).
The existing GSUM capture yields one separately reported unsupported guard tree
and one unconditional GSUM-OF-NIL replay. `Tests/Ns1GuardTrees.lean` checks this,
exclusion from logical theorem offers, and rejection after removing the guard
QED in memory (`c2-guard-tree-pins-build.log`). The first arithmetic captures
revealed the real admission → QED → guard → QED → DEFUN ordering. Preserving the
pending admission tree across the guard block fixes that ordering without
turning a guard tree into termination evidence.

NORMALIZE-ADDENDS replays unconditionally with those guard records retained
(`c2-normalize-retained-guards-replay.log`, 12475 ms). PREFER-POSITIVE-ADDENDS-<
reconstructs but retains REWRITE-EQUAL-<-TO-IFF-< and two assumed DP facts
(`c2-simplify-retained-guards-replay.log`, 256304 ms). No guard proof is used by
either logical row. Other unselected rows retain their displayed frontiers.

Primitive UNICITY-OF-0 replay now proves the recorded intermediate FIX term on
arbitrary values, including complex numbers and nonnumbers, then follows every
recorded child. It replaces the old pinned-integer-only implementation.
ACL2-NUMBERP's two-valuedness is registered at the actual FIX expansion in the
basic book. The primitive associative-addition and commutative-multiplication
axioms (`acl2/axioms.lisp`, defaxioms at 4279/4302 before subsequent fork edits)
now use the same equation/child-chain composition. The cited basic prefix
replays 5/9 rows, 3 unconditional: (+ (+ x y) z), (+ 0 x), and (* y x)
(`c2-basic-primitive-equations-replay.log`, 44944 ms). Double negation still
requires its ordinary pass1/basic-arithmetic book proof; it is not a primitive
axiom and has not been hand-proved.

The actual Subgoal 6 and Subgoal 2' DP obligations check using a normalization
pass that retains their conditional linear premises
(`c2-upper-sg6-preserve-premise-once.log`, `c2-upper-sg2-preserve-premise.log`).
The same pass does not close Subgoal 3, including a two-pass attempt; its earlier
checked recognizer-preserving route is retained as the fixed fallback. The
production engine contains both routes and keeps the ordinary DP branch for
unrelated statements. 03-linear still passes all three unconditional rows and
three probes in 11137 ms (`c2-preserved-premises-linear-regression.log`). The
complete upper-bound run is pending, so no DP completion claim is made yet.

Capturing pass1/basic-arithmetic through FUNCTIONAL-SELF-INVERSION-OF-MINUS
exposes another BUG-040 case: its first COMMUTATIVITY-2-OF-+ declaration is
redundant with the bootstrap world and emits neither a fresh proof nor an
include-book declaration. The source-census check correctly rejects that
missing record. Instrumentation now emits an explicit :SOURCE :REDUNDANT
DEFTHM at ACL2's actual redundancy branch. Its formula/classes are retained in
a separate declaration event, with no QED and no new theorem/rule offer. The
image rebuild succeeds (`c2-redundant-declaration-image-build.log`); the fresh
capture, metadata-only control, and parser/replay validation are pending.

The complete upper-bound row now replays with only
`linear:MOD-BOUND-LINEAR-ARG2-STRONG`, with no assumed DP fact on the composed
row (`c2-upper-preserved-premises-full-replay.log`, 82483 ms). The standalone
informational probes still lack the linear-rule premises and report three
assumed leaves; that bracket is not the composed row's condition inventory.
The strong MOD bound and the native bridge remain open.

The redundant-declaration control preserves all 77 original events exactly,
adding only the declaration (`c2-redundant-event-comparison-final.log`). An
initial control exposed an extra cited-symbol snapshot introduced by printing
metadata; dynamically isolating that printer's collector removed the side
effect. The hypothesis-basis control separately preserves all 2083 original
events modulo its new fields. Fork commit `d03226496d` checkpoints both capture
changes under the fast gate. Its clean image was rebuilt before regenerating
the corpus (`c2-d032-clean-image-build.log`, `c2-d032-recapture-all.log`).

FUNCTIONAL-SELF-INVERSION-OF-MINUS now replays unconditionally from its ordinary
pass1 book tree, including both recorded tau leaves
(`c2-pass1-negation-components-replay.log`, 4062 ms). The DP normalization uses
canonical negation components on arbitrary ACL2 values; it does not introduce
a Lean proof of the book theorem. A clean scoped capture and source-formula /
axiom pins are being added to the permanent NS1 regressions. The INVERSE-OF-+
primitive handler builds, but its focused replay must be rerun: the first run
overlapped corpus invalidation and could not load ClauseTree. No full-gate
claim is made for this batch yet.

The clean permanent pass1 pin now builds with the exact source formula and
`{propext, Classical.choice, Quot.sound}` receipt
(`c2-d032-pin-build.log`, `c2-add-order-primitive-build.log`). Its ordinary
book proof transfers into basic and closes (- (- x)) unconditionally
(`c2-basic-pass1-dependency-rerun.log`, 49280 ms for the prefix). Collect's
(+ x (- x)) also replays unconditionally through the recorded primitive
INVERSE-OF-+ step (`c2-collect-inverse-core-rerun.log`, 4433 ms for the prefix).
The shared primitive equation/child-chain adapter has its own module; the
superseded commutative-addition evaluator lemma is removed.

The two PREFER-POSITIVE-ADDENDS-< leaves check through primitive component
normalization and rational addition cancellation. Its complete row is now
conditional only on REWRITE-EQUAL-<-TO-IFF-<; both standalone probes also check
(`c2-add-order-simplify-replay.log`, 98784 ms). The comparison-Boolean rule's
own recorded tau leaves remain under investigation. Fresh unchanged-source
captures of basic, collect, normalize, simplify, MOD bound and FLOOR bound
are under `.tmp/ns1/c2-d032-dependencies/`; their capture receipt is
`c2-d032-dependency-captures.log`.

The next quotient dependency captures through
NONNEGATIVE-INTEGER-QUOTIENT-LOWER-BOUND-LINEAR2, but reconstruction rejects a
LOCAL helper emitted as a witness outside ENCAPSULATE. BUG-041 records this
separately from BUG-030's inherited-local-include case. Its admission and
local provenance must be preserved; no witness exclusion has been relaxed.
Static checks pass after splitting the primitive adapter, including all 101
permanent log sidecars at d03226496d (`c2-d032-static-rerun.log`). These are
intermediate receipts; C2 and the native mirrors remain open.

The final comparison component branch checks all four recorded tau leaves of
REWRITE-EQUAL-<-TO-IFF-< and composes that theorem unconditionally. It uses
kernel-checked rational/propositional normalization only at verdict-only
leaves. PREFER-POSITIVE-ADDENDS-< and SIMPLIFY-SUMS-< then replay unconditionally
as well (`c2-comparison-simplify-replay.log`: 5/14 unconditional rows,
65849 ms; unselected frontiers remain displayed). 03-linear retains 3/3
unconditional rows and three checked probes in 11180 ms
(`c2-comparison-linear-regression.log`).

With the clean pass1/basic/collect/normalize/simplify/floor dependency captures
offered together, MOD-BOUND-LINEAR-ARG2's condition inventory contracts from
eight rules to just MY-FLOOR-LOWER-BOUND-ALT. The strong bound retains that
condition and one assumed DP fact (`c2-d032-mod-dependency-closure-replay.log`,
207648 ms). Whole-world transfer refuses the dependencies because of missing
helper names, with no differing shared definitions
(`c2-dependency-world-differences.log`); the existing tree replay fallback
closes the other dependencies without changing that policy.

The strong bound's current value abstraction supplies only ACL2-NUMBERP for
opaque MOD. Its exact extracted obligation has a kernel-checked countermodel
X=0, Y=1, opaque MOD=1/2
(`c2-strong-mod-abstraction-computed-countermodel.log`). This refutes that
abstraction, not the ACL2 theorem. The log's ALL-TPS already contains the
conditional INTEGERP-OF-MOD-TYPE prescription. Its actual three-step literal
chain unfolds MOD, replays multiplication commutativity, and asks the
recognizer for integer closure through addition/negation/multiplication with
the emitted FLOOR type fact. That producer and its downstream DP fact remain
open; no integer fact has been invented in Lean.

The full gate started in `.gate-runs/d676937-20260906T064419Z.log` catches a
stale fsq-unfolds condition pin: COMMUTATIVITY-OF-* is now discharged by its
recorded primitive step, leaving DISTRIBUTIVITY and UNICITY-OF-1. The actual
lambda/body tree was inspected (`c2-fsq-primitive-tree.log`). Both the exact
condition inventory and the independent statement pin are updated to remove
that hypothesis, preserving the source conclusion. The failed gate is still
finishing dependent builds; the corrected pin and full rerun are pending.

CI capture preparation now invokes the shared `just capture-ns1-logs` recipe,
with just installed before capture. The prior workflow regenerated only repo
and sorting captures, so a clean runner would lack the new include_str inputs.
The workflow YAML and ordering parse/check locally; its invoked certification
and four capture commands have already run locally. No remote CI execution or
push has been attempted. Main remains clean at the approved docs commit.

The corrected DriverTests source checks in a standalone Lean run
(`c2-fsq-corrected-driver-pins.log`): fsq-unfolds has exactly the two expected
conditions and the accepted axiom trio; the source-formula pin and the other
driver regressions pass. This run writes no Lake build products, so it does
not race the still-running failed gate. The next full gate must rebuild that
test before any batch-green claim.

The first capture/consumer full gate finished with `TRUE_EXIT=1`, solely at
the stale DriverTests pin described above. The rerun is in
`c2-capture-components-claim-rerun.log`; no passing receipt is claimed yet.

Closer inspection of the strong-bound leaf identifies its cited prescription
as **INTEGERP-MOD**, from arithmetic-3/floor-mod/floor-mod.lisp, rather than
the Kestrel INTEGERP-OF-MOD-TYPE alias discussed above. Both formulas occur in
the snapshot, but only the actual cited basis may license this leaf. A clean
unchanged-source capture through INTEGERP-MOD reconstructs its owning tree
(`c2-d032-integerp-mod-owner-capture.log`,
`c2-d032-integerp-mod-owner-tree.log`). Its recorded MOD/FLOOR expansion and
integer primitive closure remain to be replayed. The existing conditional
stored-TP body walker is also being inspected; its emitted masks, leaves and
hypotheses remain mandatory gates, with no new assumption or per-book proof.

The corrected DriverTests target passes in the rerun, but its combined Tests
import exposes a second failure (`.gate-runs/d676937-20260906T072357Z.log`,
`TRUE_EXIT=1`): PatternPins and BSmsort independently export the same
`Logic.consp.match_1.congr_eq_1._sparseCasesOn_2` auxiliary. Lean 4.33's grind
matcher-congruence realization creates it while attempting the new arithmetic
branch. That branch now limits grind to the rational/propositional residue
(`-matchEqs -splitMatch`); the existing constructor split fallback remains.
All six extracted actual comparison leaves still kernel-check with clean
axioms (`c2-comparison-no-match-probes.log`), and the affected CLI builds
(`c2-comparison-no-match-build.log`). Combined-module/full-gate validation is
running again; neither failed gate is a passing checkpoint.

The owning INTEGERP-MOD replay reaches the recorded RATIONALP recognizer for
`(BINARY-* M (UNARY-/ N))` inside EQUAL-DENOMINATOR-1's child chain
(`c2-integerp-mod-owner-first-replay.log`). Its fake-rune-for-type-set basis
requires the primitive rational multiplication/reciprocal cells. No native
proof or INTEGERP-MOD completion is claimed.

BUG-041 design inspection corrects the earlier phrase "witness exclusion":
`Development.toWorld` already includes witnesses as the canonical model.
The ratified R6 design and the 2026-08-08 addendum to the equisort charter
place BUG-019's protection at parametric statement abstraction and the
witness-dereference guard. Several parser/type comments still describe the
superseded mechanism. The local-helper repair must preserve those actual
protections, admission evidence and local provenance; it does not require a
new trust ruling. No implementation of that repair is present yet.

The simplified arithmetic replay still reports 5/14 unconditional rows with
the restricted comparison branch (`c2-comparison-no-match-simplify-replay.log`,
68687 ms). The full gate is still running. Primitive rational type-cell
prototypes check locally (`c2-rational-type-cells-probe-rerun.log`), but are
not yet wired into the owning INTEGERP-MOD node and do not count as a replay
result.

The owning INTEGERP-MOD rational node's reconstructed provenance is now
inspected directly: argument type-set 40, RATIONALP true mask 63, no IF leaves,
and the recorded fake-rune-for-type-set basis
(`c2-integerp-mod-rational-node-basis.log`). The pending primitive cells derive
63 from the actual context; the recognizer will check that ACL2's 40 lies
inside it. Their wiring patch is prepared under `.tmp/ns1/`, not applied while
the regression build is reading these modules.

The strong-bound leaf with its actual cited INTEGERP-MOD corollary also checks
under a prototype integer-view decomposition
(`c2-strong-mod-int-views2.log`). It extracts the integer atoms from the
clause's two recorded INTEGERP hypotheses, normalizes the conditional TP
premise, extracts the output integer, and closes the resulting Int arithmetic.
No resource limit was raised. This remains a conditional leaf probe: the
production cited-TP adapter and the owning prescription's proof are still
open, so it is not a completed strong-bound replay.

The conditional leaf's integer normalization is now exercised as a generic
loop (`c2-strong-mod-int-view-loop-rerun.log`), preserving the existing
nonnegative-integer view and removing one SExpr value binder per new round.
Its standalone module draft checks (`c2-integer-views-draft-build.log`). The
cited-type adapter draft also checks (`c2-cited-type-adapter-draft-rerun.log`):
leaf-cited rune and index, exact source-formula/stored-corollary matching,
stored TERM trigger, fully bound substitutions, and the existing checked
whole-formula transport. Actual owner/stored formula matching is recorded in
`c2-cited-type-owner-bindings-rerun.log`. These drafts remain outside Lake's
source graph until the current gate finishes; they have not changed the
production strong-bound row.

PatternPins and BSmsort now import together in a standalone check
(`c2-comparison-module-import-regression.log`), reproducing the previously
failing module pair without the auxiliary-name collision. The full gate is
still finishing the product build. A fresh d03226496d BVCHOP capture through
BVCHOP-UPPER-BOUND completes 9/9 local QEDs, retaining whole-source provenance
(`c2-d032-upper-current-capture-rerun.log`); its current tree/replay check is
running alongside the final gate work.

The capture/consumer batch now has a complete passing receipt:
**`.gate-runs/d676937-20260906T072938Z.log`, `TRUE_EXIT=0`**. All 116 baseline
theorem rows are unconditional, the live coverage assembly matches the golden,
and the 21 existing native products pass the seam gate (59 seams in scope).
The combined Tests import also builds, closing the auxiliary-declaration
collision. The source/provenance gate validates all 101 permanent captures at
fork d03226496d. BUG-038/039/040 are closed under these specific repairs and
the actual capture/replay/control receipts above; BUG-041 remains open.

This is an intermediate C2 checkpoint, not C2 exit: the first native BVCHOP
proof and all three new mirror products remain open. The next code increment
applies the prepared rational type-cell wiring and the cited-type/integer-view
consumer, then continues the owning arithmetic proof and FLOOR/NIQ closure.

The current scoped BVCHOP replay, supplied with the permanent times/FLOOR/MOD
zero dependency chain, again has exactly
`cond[linear:MOD-BOUND-LINEAR-ARG2-STRONG]` on BVCHOP-UPPER-BOUND, with no
assumed DP condition on that composed row
(`c2-d032-upper-current-with-deps-replay.log`, 85778 ms). The informational
standalone bracket still reports the three linear leaves without their rule
premise. Unselected prefix rows keep their reported frontiers; no whole-book
claim is made.

Commit `f0257a8` checkpoints the passing capture/consumer batch above. The
next increment has now applied the rational multiplication/reciprocal cells to
the existing type-set walker and RATIONALP recognizer registry; its affected
build and actual owning-theorem replay are pending. The prepared integer-view
module reuses the existing `Logic.integerp_int` fact rather than introducing
an identical lemma.

The rational type-cell build and four existing NS1 arithmetic pins pass
(`c2-rational-cell-wiring-build.log`). INTEGERP-MOD's actual replay crosses
the RATIONALP node and reaches the following if-finish/or-copy join
(`c2-integerp-mod-rational-cells-replay.log`). That join rejects an empty test
prefix even after checking that the unchanged then-copy equals the test.
The empty-prefix arm now uses the same reflexive fuel equality as empty
branch chains; its endpoint check and all actual branch/post steps remain.
The affected build and owning-theorem rerun are pending. No new whole row is
claimed complete.

The empty test-prefix change builds (`c2-empty-test-prefix-build.log`), and
ORDD-INS-MID remains unconditional with three passing informational DP leaves
(`c2-empty-test-prefix-bridge-regression.log`, 200675 ms). The INTEGERP-MOD
rerun crosses that join and reaches the Boolean result check. That check now
uses the existing shared `boolDisj?` walk, extended by INTEGERP's core
Boolean-result fact; the duplicate if1/boolean dispatch was removed.

The next applied batch adds leaf-cited, whole-formula TP premises and the
integer-witness context decomposition. The build and four NS1 arithmetic
pins pass (`c2-cited-tp-integer-views-build.log`); static checks pass
(`c2-rational-cited-tp-fast-static.log`); all three 03-linear rows remain
unconditional (`c2-integer-views-linear-regression.log`, 5854 ms). The owning
INTEGERP-MOD tree now reaches an IFF-continuation/EQUAL-parent composition
frontier (`c2-integerp-mod-cited-tp-batch-replay.log`). The prior
`c2-integerp-mod-boolean-replay.log` is an invalid run: a concurrent rebuild
removed Ctx.olean before the runtime import; it supplies no proof receipt.
The actual strong MOD-bound rerun with its cited owning dependency is in
progress. No new complete row or native mirror is claimed.

The strong-bound rerun now composes its actual linear leaf without an
ASSUMED DP hypothesis: **MOD-BOUND-LINEAR-ARG2-STRONG is REPLAYED conditional
on `rule:MY-FLOOR-LOWER-BOUND-ALT` and `tpthm:INTEGERP-MOD`**
(`c2-mod-cited-tp-integer-views-replay.log`, 193715 ms; 12/58 replayed,
2 unconditional and 10 conditional). Both remaining conditions name actual
book dependencies still to replay. The standalone informational discharge
probe, which lacks these premises, still reports an assumed leaf. This is
an intermediate fast-gate checkpoint, not C2 completion or a full-gate claim.

Intermediate checkpoint `9a73b92` contains the cited-TP/integer-view batch.
The next applied Boolean IFF/equality join crosses INTEGERP-MOD's recorded
EQUAL-DENOMINATOR-1 continuation; a shared relation-at-pinned-values lemma
replaces two existing duplicate proof bodies. The actual reciprocal
known-true marker supplies mask 59 inside RATIONALP's 63
(`c2-integerp-mod-reciprocal-basis.log`), now consumed by the existing type-set
walk. Its rerun reaches the subsequent nested IF-test collapse in the
`(< (* x y) 0)` RHS (`c2-integerp-mod-known-rational-replay.log`).

Fork `d97312a6ba` repairs the local-helper classification using ACL2's actual
encapsulate stack. The dirty-image NIQ control differs from d032 only at the
two private helpers' SOURCE fields; cov-encapsulate's proof events are
unchanged (`c2-local-helper-emission-comparison.log`). Both helpers now
reconstruct with their model definitions and admission evidence; they never
enter the constrained witness vocabulary. Controls reject witnesses outside
encapsulate, helpers inside encapsulate, and conflicting helper bodies
(`c2-local-helper-reader-controls.log`). The complete NIQ tree is retained at
`c2-local-helper-niq-tree.log`; the initial replay produced no receipt because
the filesystem filled. No NIQ theorem count is claimed from that run.

The first clean image build failed writing its core file because the shared
filesystem was full (`c2-local-helper-clean-image-build.log`). The corrupt
partial core was removed, and six superseded diagnostic capture directories
were archived and every file byte-verified before removing the loose copies:
`c2-pre-hypothesis-captures.tar.gz` contains `c2-primitive-captures`,
`c2-clean-captures`, `c2-path-clean-full`, `c2-balanced-captures`,
`c2-path-dirty-full`, and `c2-captures`. Earlier references to those directories
can be recovered from this archive. Current dependency captures and all
receipt logs remain loose. The clean image rebuild then passed
(`c2-local-helper-clean-image-build-space-rerun.log`). Corpus recapture and
the new permanent local-helper pin are pending.

The refreshed permanent corpus has 102 captures stamped at clean fork
`d97312a6ba18` (`c2-d973-corpus-recapture.log`,
`c2-d973-capture-static.log`). The CLI, new local-definition pin, and all four
existing NS1 arithmetic pins build (`c2-d973-reader-arithmetic-pins-build.log`).
The next full claim-gate is running for this combined capture/consumer batch;
C2 remains open. The current INTEGERP-MOD join is an existing recorded
`:IF-TEST-TRUE` for `(< '0 M)` in the false branches of `(EQUAL M '0)` and
`(< M '0)`, with `:FAKE-RUNE-FOR-TYPE-SET` justification. Its consumer needs
those enclosing branch facts while composing the nested IF result; this is
not an absent ACL2 proof step.

## Resume record

The next IF/type-set increment crosses INTEGERP-MOD's recorded nested
IF collapse, then its final integer recognizer. The collapse carries its
enclosing branch facts and intersects the three existing type facts. The
recognizer consumes its three emitted ARG-LEAVES, generic integer arithmetic
cells, and the step-cited quotient TP. Shared Boolean range proofs replace
the duplicate helpers; the collapse walker is extracted from Recognizer.

**INTEGERP-MOD now REPLAYS conditionally**
(`c2-integerp-mod-integer-leaves-replay.log`, 33101 ms), with ten remaining
rule conditions: FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT, DISTRIBUTIVITY,
DISTRIBUTIVITY-OF-MINUS-OVER-+, EQUAL-/-0, /-PRESERVES-POSITIVE,
/-PRESERVES-NEGATIVE, NUMERATOR-NEGATIVE, EQUAL-DENOMINATOR-1, `(* -1 x)`,
and `(< (* x y) 0)`. Its quotient TP closes; no assumed DP condition is on
this row. This is 1/7 replayed rows in that prefix, zero unconditional.
All other prefix failures remain reported; no native product is claimed.

The affected build and existing NS1 arithmetic pins pass
(`c2-integer-arg-leaves-build-rerun.log`, 6194 jobs), as do static checks
(`c2-if-type-leaves-fast-static.log`). The existing CLASSIFY-POS regression
has two unconditional rows (`c2-if-type-leaves-classify-regression.log`,
1984 ms); ORDD-INS-MID remains unconditional with all three DP leaves
(`c2-if-type-leaves-conjunction-regression.log`, 177418 ms).
The first build attempts failed on a namespace qualification and a local
Option-return elaboration; their failed receipts remain alongside the
successful reruns. This is a **fast-gate** increment, not a full-gate claim.

Fresh d973 dependency captures now cover pass1/basic-arithmetic-helper
through FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT (11 QEDs), pass1/basic-arithmetic
through EQUAL-/-0 (14), pass1/inequalities through /-PRESERVES-NEGATIVE (3),
pass1/numerator-and-denominator through EQUAL-DENOMINATOR-1 (7), and
bind-free/numerator-and-denominator through NUMERATOR-NEGATIVE (six QEDs,
including separate TP/admission records). Their trees are
`c2-d973-owner-{helper,basic,inequalities,numden,bind-numden}-tree.log`.
Two initial prefix captures stopped at an include that already provided
the requested name and were correctly rejected by the final-QED check;
the replacements above identify the actual proof owners.

The first inequalities replay leaves four actual reciprocal-sign tau
clauses assumed (`c2-pass1-inequalities-first-replay.log`). The numerator
sign rows replay conditional only on REWRITE-LINEAR-EQUALITIES-TO-IFF
(`c2-bind-free-numden-first-replay.log`). The fresh reciprocal dependency
has clause-composition frontiers and a missing associative USE premise
(`c2-times-and-divide-first-replay.log`). The NIQ local reciprocal row
reaches a stored-rule LHS substitution mismatch at `*-OF---ARG2`
(`c2-niq-local-reciprocal-first-replay.log`); private helper admission
failures remain separately reported. These are measured dependency
frontiers, not completed proofs.

The capture/consumer batch passes the full checkpoint gate:
**`.gate-runs/9a73b92-20260906T085449Z.log`, `TRUE_EXIT=0`**. All 116 baseline
rows remain unconditional, the assembled golden is unchanged, the combined
Tests import builds, and all 21 existing mirror products pass the seam gate
(59 seams). All 102 permanent captures carry clean fork d973 provenance.
BUG-041 is closed for the local-helper classification and its explicit
reconstruction checks. The arithmetic rows above retain their stated
conditions; no NIQ proof or new native mirror is claimed from this gate.
Next is the recorded nested IF collapse in INTEGERP-MOD, followed by the
selected FLOOR/NIQ dependency closure.

The reciprocal-sign increment closes both actual pass1/inequalities
proofs, retaining the recorded IFF rewrite, IF splits, and two tau leaves
per sign (`c2-pass1-inequalities-reciprocal-replay-rerun.log`: 3/3
unconditional rows, 13674 ms). The primitive reciprocal view is normalized
before component expansion; default proof budgets are unchanged. The new
permanent prefix has 305 lines and three QEDs, and the existing NS1
arithmetic test now pins both source formulas and clean axiom receipts.
The first pin build correctly rejected an IFF in the handwritten statement:
the source states EQUAL of the Boolean comparisons. The corrected pins
retain that EQUAL. Failed probe/build receipts remain explicitly failed.

The small pass1/mini-theories prerequisite is unconditional
(`c2-pass1-mini-first-replay.log`: 1/1, four DP leaves). With it, the
bind-free numerator-sign prefix is also unconditional
(`c2-bind-free-numden-with-mini-replay.log`: 3/3, five DP leaves).
Supplying these proofs and the reciprocal signs to INTEGERP-MOD reduces
its conditions from ten to seven
(`c2-integerp-mod-sign-dependencies-replay.log`: 49063 ms):
FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT, DISTRIBUTIVITY,
DISTRIBUTIVITY-OF-MINUS-OVER-+, EQUAL-/-0, EQUAL-DENOMINATOR-1,
`(* -1 x)`, and `(< (* x y) 0)`. It remains conditional, with no assumed
DP condition; C2 and the three new native products remain open.

The permanent reciprocal prefix replays with all eight DP leaves and
3/3 unconditional rows (`c2-reciprocal-permanent-replay.log`, 19322 ms).
The six arithmetic pins, including both new whole-proof axiom receipts,
build (`c2-reciprocal-sign-pins-build-rerun.log`, 3110 jobs); the affected
CLI build is `c2-reciprocal-sign-build-rerun.log` (6184 jobs). Static checks
pass (`c2-reciprocal-fast-static.log`, 103 clean d973 captures), with the
subsequent BUG-042 index check in `c2-reciprocal-bug-index-check.log`.
This checkpoint uses **fast-gate**; no full gate or native-product claim
is made for this increment.

The first multiplication-helper replay has 1/11 unconditional rows
(`c2-pass1-helper-first-replay-rerun.log`: 64901 ms). Its selected
FUNCTIONAL-COMMUTATIVITY dependency exposes BUG-042: raw source LMI
substitutions disagree with the translated hypothesis. Other helper
rows expose existing clause-composition, recognizer, and DP frontiers.
No helper proof is claimed beyond the one measured unconditional row.

The next arithmetic/USE batch reduces INTEGERP-MOD to **five** conditions:
FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT, EQUAL-/-0,
EQUAL-DENOMINATOR-1, `(* -1 x)`, and `(< (* x y) 0)`.
The primitive DISTRIBUTIVITY and ground-zero negation-of-sum equations
are applied only at their recorded nodes, then every recorded child is
replayed. The clean current-fork receipt is
`c2-2f0dd-integerp-mod-replay.log` (48765 ms); the earlier d032 artifact
rerun is `c2-integerp-mod-distributivity-replay.log` (49232 ms).
Both retain the same five conditions and no assumed DP condition.

Fork `2f0dd071ca0b` records ACL2's successful translated USE substitution
and preserves the raw source LMI (BUG-042). The helper's 105 parsed events
are unchanged after removing only the added translated-LMI metadata
(`c2-use-helper-emission-comparison.log`). The raw image build and clean
rebuild pass (`c2-use-substitution-image-build.log`,
`c2-translated-use-clean-image-build.log`). All 104 permanent captures
and all fifteen current diagnostic dependency captures have been refreshed
at clean 2f0dd (`c2-2f0dd-corpus-recapture.log`,
`c2-2f0dd-dependency-recapture.log`); the latter live under
`.tmp/ns1/c2-2f0dd-dependencies/`, preserving the old relative filenames.
The prior d032/d973 captures and failed experiments remain available.

The macro-instance regression's two rows replay unconditionally
(`c2-2f0dd-use-macro-replay.log`, 1065 ms). Its statement/axiom pins and
negative controls pass: dropping the translation, altering its term, or
misaligning the list is rejected at the consuming instance check.
The affected CLI, six arithmetic pins, USE pins, and existing tamper tests
build (`c2-2f0dd-affected-build.log`, 6213 jobs). Static checks pass
(`c2-2f0dd-fast-static.log`), including all 104 clean capture stamps.
Initial consumer and test builds failed on a misplaced documentation
comment and a reserved Lean identifier; their failed logs are retained.

The selected multiplication-helper proof now crosses its actual translated
instances and its primitive DISTRIBUTIVITY USE premise. It remains ASSUMED
on its earlier UNIQUENESS-OF-+-INVERSES-LEMMA and its own tau leaf
(`c2-2f0dd-helper-replay.log`, 106252 ms; 1/11 unconditional prefix rows).
The corresponding current recursive tree is `c2-2f0dd-helper-tree.log`.
Those two recorded tau leaves are the next proof target. This is a
**fast-gate** increment; the full checkpoint and BUG-042 close-out remain
pending. No new native mirror is claimed.

The following helper increment closes both recorded tau leaves. Numeric
equality is normalized through canonical components with explicit number
premises; the second leaf consumes the recorded USE implication after
primitive multiplication-by-zero normalization. Both whole statements now
replay unconditionally (`c2-helper-dp-literal-replay.log`: 3/11 prefix rows,
27432 ms). The other eight prefix rows retain their measured frontiers.
`Tests.Ns1Arithmetic` pins both source formulas, including the translated
SYNTAXP premise, and both axiom trios; the clean permanent capture remains
at fork `2f0dd071ca`. Supplying the helper reduces INTEGERP-MOD to **four**
conditions: EQUAL-/-0, EQUAL-DENOMINATOR-1, `(* -1 x)`, and `(< (* x y) 0)`
(`c2-helper-dp-integer-mod-replay.log`: 97741 ms).

The initial integration exposed two normalization issues. An incomplete
reciprocal-sign branch prevented fallback; requiring full closure restores
EQUAL-DENOMINATOR-1's two DP leaves (4659 ms), while the reciprocal-sign
prefix remains 3/3 unconditional with 8/8 DP leaves (22934 ms). The
multiplication-zero simp lemma must retain the reflected integer constructor
in its index. The actual production-handler probes now close both helper
leaves without a resource increase (`c2-helper-dp-literal-probe.log`).
Failed intermediate probes and replays remain as negative execution records.

The full gate `.gate-runs/5044b6d-20260906T104829Z.log` is **TRUE_EXIT=1**:
DriverTests still expected DISTRIBUTIVITY as an open FSQ premise, although
the recorded primitive now closes it. That exact statement pin is updated
to retain only UNICITY-OF-1. The remaining SortsEquivalent build job was
terminated after this failure so the fixes could be built; this run provides
no full-gate completion receipt. The affected build subsequently passes
(`c2-helper-dp-literal-build.log`, 6216 jobs), as do both new helper pins
(`c2-helper-statement-pins-build.log`, 3114 jobs). An earlier affected-build
command also named a nonexistent test target; its corrected rerun passes.
The final static suite passes (`c2-helper-dp-final-static.log`, 105 clean
capture stamps). This remains a **fast-gate** increment. BUG-042's full checkpoint and all
three native mirror proofs remain open.

- Approved docs are committed on `main` at `b452b70`; implementation lives
  in `/home/dev/projects/ACL2Lean/.claude/worktrees/ns1-bvchop`, branch
  `mdd/ns1-bvchop`. C0 is committed at `31d8e42`; C1 is `276f4b8` and carries
  the full gate receipt above.
- C0's two review tasks are complete. The two C4 tasks remain authorized;
  no preflight questions are pending.
- Next: close the actual arithmetic
  dependencies, and build the first native proof.
- C2–C4 and all three new mirror proofs remain open. NS1 is in progress;
  there is no merge or push approval for the implementation.
