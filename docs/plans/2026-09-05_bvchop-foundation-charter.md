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

### C2 denominator dependency (2026-09-06, in progress)

INTEGERP-MOD now retains **two** conditions, EQUAL-/-0 and
`(< (* x y) 0)` (`c2-denominator-closed-integer-mod-replay.log`, 94597 ms).
Its full statement still replays conditionally; no new native mirror exists.
The earlier minus-one-only increment reduced four conditions to three
(`c2-context-subst-integer-mod-replay.log`, 99028 ms).

Two additional dependency statements replay without conditions:
`(* -1 x)` from the unchanged bind-free/basic book
(`c2-minus-one-wired-replay.log`, 41631 ms; selected row's one tau leaf),
and EQUAL-DENOMINATOR-1 from unchanged pass1/numerator-and-denominator
(`c2-numberp-typeset-numden-replay.log`, 10116 ms; 2/7 prefix rows replay,
one unconditional and one conditional, and 2/2 reported DP leaves).
The permanent prefixes are clean captures at fork `2f0dd071ca0b`.
`Tests.Ns1Arithmetic` pins both unrestricted translated source statements
and their axiom trios. The minus-one leaf uses primitive component
congruence; the denominator proof consumes both actual primitive USEs,
RATIONAL-IMPLIES2 and COMPLETION-OF-DENOMINATOR.

The denominator proof exposed three composition gaps, each now crossed in
that actual proof:

- The type-alist contradiction is over `accClause ++ remaining.tail`, the
  exact clause assembled by ACL2's `rewrite-clause-type-alist`. The composer
  checks that shape, proves the emitted obligation, and peels the already
  false accumulator. Other shapes retain the existing strict checks.
- A recorded CONTEXT-SUBST transports type-set evidence along an in-scope,
  checked equality. The directed alias is retained through inline branches;
  its consumed record is removed during recursive type-set traversal.
  Primitive NUMERATOR/DENOMINATOR cells and the ACL2-NUMBERP type-set path
  consume the recorded TYPESET/TRUETS, including the earlier primitive
  UNICITY-OF-1 rewrite and its FIX/recognizer children.
- The residual branch substitutes DENOMINATOR X with 1, evaluates its
  reciprocal, and then pushes the transformed clause. The new small
  `ResidualPostpass` composer replays those records and requires a unique
  exact child match. ACL2's `crunch-clause-segments` calls
  `remove-trivial-equivalences` with `remove-flg = nil`
  (`acl2/simplify.lisp`, around 7232); the justifying equality stays in the
  clause. The shared term-replacement helper moves out of CoreSpine,
  reducing that grandfathered module from 1539 to 1508 lines.

The affected CLI and proof pins build
(`c2-numberp-typeset-build.log`, 6220 jobs). FSQ-UNFOLDS also loses its last
UNICITY-OF-1 condition through that actual primitive record
(`c2-unicity-one-fsq-replay.log`, 782 ms); DriverTests now pins its
unconditional statement. Three in-memory negative controls remove the
context alias, change the postpass equation, or alter the DP clause;
all reject at their consuming checks
(`c2-context-negative-controls-build.log`, 3116 jobs). Initial control
attempts used an incomplete optional-field pattern and changed no records;
those failed executions are not positive evidence. That mistake revealed
the same issue in two reporting helpers (BUG-043), now repaired and awaiting
the full checkpoint. The final build adds a real-capture check of both
reporting helpers and passes (`c2-denominator-final-build.log`, 6221 jobs).
The final static suite also passes (`c2-denominator-final-static.log`).
The final executable replays the denominator target unconditionally in
9977 ms (`c2-denominator-final-replay.log`); the FSQ focused replay is
`c2-denominator-final-fsq-replay.log`.

Static checks pass (`c2-denominator-static.log`, 107 clean fork stamps).
A first product-sign replay was terminated after approximately eleven
minutes with no completed result (`c2-product-sign-first-replay.log`,
process exit 143). The actual `<-*-0` tree and its verdict leaves are
retained under `.tmp/ns1/`; a rational-value decomposition is being tested
on those leaves, with no resource-limit increase and no product-sign proof
claimed. The selected minus-one CLI row passes, but distinct escaped
arithmetic theorem names can collide in Runner's sanitized constant names;
that completeness limitation is recorded in TODO.

The full gate `.gate-runs/ca5e1dd-20260906T123257Z.log` is **TRUE_EXIT=1**.
The main build passes 3233 jobs, including the 21 existing mirror products
and their 59-seam check. The subsequent forced coverage rebuild rejects
CD2-BOUND: the induction step retained an outer environment's clause fact,
which the recognizer selected by term alone (BUG-044). No golden is changed;
the failed run is not a full preservation receipt. A focused executable
reproduction confirms the same failure in 9314 ms
(`c2-denominator-cd2-regression-rerun.log`; the first command omitted Lake's
module environment and failed before replay). The induction-context repair
is in progress. BUG-042/043/044 and all three native products remain open.

While that checkpoint was frozen, probes of the seven actual product-sign
verdict leaves passed with the driver's context preparation, with a maximum
of 5988 heartbeat units against the existing 15000-unit direct budget
(`c2-product-sign-rational-scaffold-probe.log` and
`c2-bind-product-sign-rational-scaffold-probe.log`). These are isolated leaf
checks, not whole-product replay. The whole target fails at a residual
literal folded to NIL that has not been removed
(`c2-product-sign-focused-frozen-probe.log`). ACL2's
`add-literal-and-pt` removes that literal; the existing spine already has
the checked transport needed here. The ordinary macro probe first exceeded
its command budget while preparing unrelated dependency rows; the focused
probe uses the same untouched theorem and dependency trees through
`Runner.tryReplay`, with its existing budget.

Fresh diagnostic captures at clean fork `2f0dd071ca` also establish
TIMES-ZERO's whole unconditional replay and the FLOOR bound's actual
`<-OF-*-AND-*-CANCEL` dependency. The latter reaches its recorded primitive
POSITIVE USE frontier (`c2-product-cancel-focused-frozen-probe.log`).
The quotient helper's quoted-minus matching gap is ACL2's
`one-way-unify1-quotep-subproblems` behavior (`translate.lisp`, around 6613);
its evidence still needs emission. No matcher check has been weakened.
The induction fix restores CD2-BOUND unconditionally, with its three
recorded discharge leaves (`c2-induction-env-fixed-cd2-replay.log`, 15281 ms),
while EQUAL-DENOMINATOR-1 remains unconditional (10359 ms). The first build
had a structure-literal indentation error; the corrected build passes
6205 jobs. The follow-up extraction consolidates fourteen environment
resets in `ReplayCtx.clearEnvFacts`, including the new context aliases.
Its build passes 6220 jobs, the unchanged CD2 coverage pin, NS1 source/axiom
pins, and all context-tampering controls
(`c2-env-reset-extraction-build.log`). Final focused replays retain the same
results: CD2 in 15651 ms and denominator in 10552 ms
(`c2-env-reset-final-{cd2,denominator}-replay.log`). The final static suite
passes (`c2-env-reset-final-static.log`, 44 indexed bugs and 107 clean
capture stamps). This is a **fast-gate** repair; the full red checkpoint
remains red until the next full run.

Superseded diagnostic dependency captures are losslessly archived in
`.tmp/ns1/c2-superseded-dependency-captures.tar.gz`, with a verified SHA-256
manifest beside it; this reclaimed 178 MiB without discarding evidence.


The product-sign dependency now closes through the real whole proofs of
`<-*-0` and `(< (* x y) 0)`. The core proof consumes TIMES-ZERO, its five
recorded verdict leaves, and the recorded residual substitutions/folds.
The wrapper consumes that core proof, the recorded IFF-definition children,
its `< 0 X` IF decision, and two more verdict leaves. The shared residual
composer now uses the existing checked NIL-literal removal transport;
CoreSpine falls below the module norm at 1479 lines. Equality congruence lets
the IF-marker consumer descend into either operand without relaxing the
requirement for a recorded decision.

Inside the existing bounded DP attempt, `RationalViews` replaces only values
carrying actual RATIONALP premises by rational witnesses. A fresh goal
contains the attempt; it assigns the original only after every obligation
closes. This decomposition closes the seven actual sign leaves without a
resource-limit increase. The macro's optional `inline_deps` route uses the
existing conditional discharger directly, avoiding whole-book registry
preparation while keeping the same offered trees and rules. Its default
behavior is unchanged; unresolved imports remain visible conditions.

Permanent captures extend basic-arithmetic through TIMES-ZERO and
inequalities through `<-*-0`, from unchanged sources at clean fork `2f0dd071ca`.
`Tests.Ns1Arithmetic` independently pins all three translated statements and
their axiom trios; the wrapper's SYNP premise is retained. Removing its one
actual `< 0 X` IF marker in memory is rejected by the literal-chain consumer.
The pins and four context controls build in 3117 jobs
(`c2-product-sign-source-pins-build.log`); the static suite passes
(`c2-product-sign-static.log`). The CLI/coverage build passes 6216 jobs
(`c2-product-sign-final-cli-build-rerun.log`), including the unchanged CD2
coverage pin. Its first command named a nonexistent test module and failed;
that failed invocation is preserved. The final CD2 executable replay is
unconditional with all three discharge leaves in 15381 ms
(`c2-product-sign-final-cd2-replay.log`).

INTEGERP-MOD now retains only `rule:EQUAL-/-0`, down from two rule conditions
(`c2-product-sign-closed-integer-mod-replay.log`, 102784 ms for the focused
book run). This remains a conditional replayed statement, with no new native
mirror yet. The full gate still requires a rerun; BUG-042/043/044 remain open.


The full product-sign checkpoint at `e7829b5` passes:
`.gate-runs/e7829b5-20260906T135512Z.log` records **TRUE_EXIT=0**. The main build
passes 3234 jobs; the forced coverage assembly is 116/116 unconditional over
29 books and matches the unchanged golden. All 21 existing mirror products
consume replayed statements through the 59-seam check. BUG-042/043/044 close
at this checkpoint. The earlier red gates remain red. The broad product-sign
CLI run was stopped after twelve minutes without a final target result
(`c2-product-sign-final-replay.log`, exit 143); the targeted whole-proof and
source/axiom pins above are the positive product-sign receipts.

While this checkpoint was frozen, the actual EQUIV-1-IMPLIES-EQUIV-* proof
was composed through the existing clause spine, consuming its recorded
substitution and equal-self ending. It checks the whole source statement
and axiom trio; deleting the substitution makes equal-self reject the
literal's clause membership (`c2-congruence-existing-spine-frozen-control.log`).
Production dispatch considers only literal records after clausify and still
needs to route this ending to the existing walker. No new proof method is
needed. A multi-target reciprocal probe exceeded its command budget after
two targets; its completed frontiers remain evidence, and subsequent probes
will be separated rather than raising that budget.

A separate sparse ACL2 checkout, `.tmp/ns1/acl2-if-basis`, branch
`mdd/ns1-if-basis`, keeps diagnostic instrumentation isolated from the
checkpoint. Its clean commit `268a219360` adds root-IF type-set bases to
known-true hypothesis records. The fresh image build and origin/tag checks
pass; a source-through-EQUAL-/ capture has 3516 lines, 6/6 QED/declaration
pairs (source census 13), and clean provenance. The root mask is 256; the
NOT(ACL2-NUMBERP X) leaf is 256 with X's nonnumeric mask -128; the other
leaf is pruned with mask 0. The reader probe preserves those fields and
rejects malformed mask/leaf mutations (`c2-known-if-basis-reader-probe-rerun.log`).
The initial reader probe had a field-notation elaboration error and failed.
This reopens BUG-039's root-IF case; the production parser/consumer and fork
integration remain pending. Production `acl2/` is still clean at `2f0dd071ca`.
The three NS1 native products remain unproved.

The production dispatcher now routes recorded post-clausify substitution
and equal-self steps through the existing spine consumer. The whole
EQUIV-1-IMPLIES-EQUIV-* statement replays unconditionally in 335 ms with no
DP leaves (`c2-congruence-dispatch-replay.log`). The preceding
COMMUTATIVITY-2-OF-* row still fails; this is not a whole-prefix claim.
The CLI and independent source/axiom pin build in 6208 jobs
(`c2-congruence-dispatch-build.log`). The permanent negative control deletes
one actual substitution and is rejected at equal-self clause membership;
all five context controls build in 3117 jobs
(`c2-congruence-contexts-build.log`). Static checks pass
(`c2-congruence-dispatch-static.log`). This is an intermediate fast-gate
increment after the full checkpoint above.

RIGHT-CANCELLATION-FOR-* still reaches a vacuous residual without a matching
child. Inspection of `rewrite-clause-lst` identifies a producer boundary
error: `crunch-clause-segments` runs before BEGIN-BRANCH, so its substitution
records occur outside the branch they simplify. The consumer must not infer
their ownership from clause contents; the producer boundary needs repair.

### C2 multiplication cancellation (2026-09-06)

RIGHT-CANCELLATION-FOR-* now replays unconditionally from the unchanged
arithmetic-3/pass1/basic-arithmetic-helper source. The executable takes
6271 ms for the whole statement and closes all seven recorded tau leaves
(`.tmp/ns1/c2-branch-context-cancellation-replay.log`). The prefix is 3/4
unconditional: COMMUTATIVITY-2-OF-* still fails and is not claimed.
`Tests.Ns1Arithmetic.multiplicationCancellationReplayed` independently pins
the unrestricted translated formula, including FIX on nonnumbers, and its
accepted axiom trio. The source and context controls build in 3123 jobs
(`c2-cancellation-source-context-pins-build.log`).

The clean production fork is now `f486834ebf9f`, branch
`mdd/ns1-branch-context`. It includes the root-IF basis emission and moves
BEGIN-BRANCH before `crunch-clause-segments`, preserving actual execution
order. The fresh production image builds
(`c2-branch-context-production-image-build.log`), recapture finishes
(`c2-branch-context-recapture-all.log`), and provenance checks all 107
permanent logs at that fork (`c2-branch-context-production-provenance.log`).
The isolated source/image and diagnostic captures remain available.

The cancellation composer consumes the branch's recorded substitutions,
the actual primitive associativity/inverse rewrites with their hypothesis
children, and the equal-self ending followed by its recorded duplicate
removal. A negative control changes that actual duplicate to a term absent
from the transformed clause; its consuming check rejects it. The seven
verdict leaves use a shared field view of canonical numeric values, with
explicit NUMBERP premises on equality transport and zero completion for
nonnumbers. This route is confined to the existing bounded DP attempt;
no resource limit rises. Initial isolated normalization probes failed;
`c2-cancellation-complex-dp-rerun3.log` checks all seven leaves and their
axiom sets. The whole proof is the evidence above.

The actual EQUAL-/ root-IF hypothesis also checks, and deleting its pruned
leaf is rejected. The permanent control records this single node under its
actual branch, not the whole theorem. Its remaining proof crosses the
clausifier's PUSH/CALL boundary and recorded final true-clause scans, but
still fails at a nonconstant literal's type-set verdict
(`c2-primitive-inverse-equal-frontier.log`). BUG-032/039/045 remain open
pending whole-proof/regression validation. The isolated literal obligation
is recorded in `c2-literal-typeset-obligation.log`; it is not a new
hypothesis-relief DP allowance.

The affected executable builds in 6208 jobs. CONS-NEQ-DETAIL's recaptured
clausification proof remains unconditional in 759 ms
(`c2-branch-context-clausify-replay.log`). Static checks pass
(`c2-branch-context-static.log`). This is an intermediate **fast-gate**
increment; the full regression checkpoint is next. No NS1 native product
is claimed. The disk-space interruption left the worktree and receipts
intact; no additional cleanup was performed on resumption.

The full branch-context checkpoint at `3fb7763` passes:
`.gate-runs/3fb7763-20260906T161407Z.log` records **TRUE_EXIT=0**. The
main build passes 3240 jobs, tests 3204, and forced coverage 3148. Coverage
is 116/116 unconditional over 29 books, with the golden unchanged. The 21
existing native products retain their axiom and seam checks. BUG-045 closes;
BUG-032/039 remain open until the reciprocal paths finish. This checkpoint
does not complete C2 or any new native product.

While sources were frozen, the next EQUAL-/ literal type-set verdict was
checked under its actual nonnumber branch, transported to EvTrue, and
tested against a changed-verdict mutation
(`c2-literal-typeset-consumer-probe.log`, accepted axiom trio). Its production
consumer remains to be integrated. Inverse uniqueness still fails at
ACL2-NUMBERP(UNARY-/ X), TYPESET 126/TRUETS 127
(`c2-3fb7763-inverse-uniqueness-frontier.log`, 109 ms). Both actual POSITIVE
USE instances in the floor-bound dependency check against the complete
primitive axiom (`c2-positive-actual-instances-probe-rerun.log`); its whole
proof still reaches use:POSITIVE. These are temporary node/premise checks,
not completed dependency statements. Failed initial probes remain recorded.

### C2 reciprocal dependencies (2026-09-06)

The exact unrestricted statements for UNIQUENESS-OF-*-INVERSES-LEMMA,
EQUAL-/ and EQUAL-/-0 now pass independent source and axiom pins in
`Tests.Ns1Arithmetic` (`c2-reciprocal-zero-type-cell-build.log`, 3124 jobs).
The EQUAL-/ executable replay is unconditional, with all three recorded
DP leaves checked (`c2-reciprocal-equality-focused-replay.log`, prefix
5/6 unconditional; COMMUTATIVITY-2-OF-* still fails). EQUAL-/-0 is also
unconditional with its helper-book dependency
(`c2-reciprocal-zero-focused-replay.log`, 72983 ms for the focused prefix;
4/14 rows replayed, including one unrelated conditional row).

The proof follows the actual primitive reciprocal completion rule and its
OR hypothesis, the scoped IF windows (including empty swapped windows and
nested boundaries), Boolean equality normalization, and literal type-set
verdict. The latter is a recorded verdict-only leaf under the actual
nonnumber branch; hypothesis relief still uses its structural consumer.
Numeric type cells include the reciprocal's completed range and zero
multiplication. No DP allowance or resource budget changes. The permanent
context controls reject changed literal verdicts/polarity, changed window
tests, non-Boolean masks and deleted addressed IF leaves.

Production fork `ef2746dadef2d8160f978207f0eef822d886c1a2` records both
Boolean equality orientations, their consumed masks, supporting runes and
addressed IF leaves. Its image builds; all 107 permanent logs are recaptured
at the clean fork and pass provenance checks
(`c2-equal-boolean-production-image-build.log`,
`c2-equal-boolean-recapture-all.log`,
`c2-equal-boolean-production-provenance.log`). The tracked P8 artifact's
only changes are generated banner/provenance metadata. Initial failed
consumer probes remain recorded.

A focused sorting replay initially fails at the new Boolean equality step
on PERM (`c2-equal-boolean-convert-perm-with-deps.log`, 12/13 replayed,
11 unconditional). Its recursive tree cites PERM's Boolean type
prescription. The type-set consumer has been extended to instantiate that
exact cited corollary through the existing TP proof channel. The repaired
focused run passes 13/13 unconditional in 40701 ms
(`c2-equal-boolean-sorting-tp-replay.log`). This is a focused regression
check; the earlier failing run remains a regression receipt.
BUG-032/039/046/047 remain open until the full checkpoint.

The final affected build passes 6225 jobs, including all three reciprocal
source/axiom pins and the permanent context controls
(`c2-reciprocal-boolean-tp-build.log`). Static and provenance mutation gates
pass (`c2-reciprocal-boolean-tp-static.log`). This is an intermediate
**fast-gate** increment; the full checkpoint is next.

A fresh unchanged FLOOR-MOD capture through INTEGERP-MOD now composes the
whole statement conditionally on EQUAL-/,
FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT and NUMERATOR-NEGATIVE
(`c2-reciprocal-closed-integerp-mod-frontier.log`, 51391 ms). The first two
have checked source pins, but this raw probe lacks the prepared dependency
registry and exposes the existing inverse-lemma name collision: plus and
star both sanitize to the same name, causing a refused transfer. The third
comes from bind-free/numerator-and-denominator, distinct from the already
pinned pass1 book; its fresh capture and recursive tree are recorded in
`c2-bind-free-numerator-capture.log` and
`c2-bind-free-numerator-tree.log`. These are dependency frontiers, not new
native products. All three NS1 mirrors remain unproved.

The full gate for reciprocal checkpoint `7445845` fails:
`.gate-runs/7445845-20260906T175722Z.log` records **TRUE_EXIT=1**. The main
build finds a regression in ORDEREDP-MEMB: the new IF-window test filter
rejects an anchor. Its dependent ORDERED-PERMS statement retains that rule
condition, and the corresponding waypoint and coverage pin fail. The
unchanged golden is authoritative; this checkpoint does not preserve the
baseline yet. The previous `3fb7763` full receipt remains the last passing
checkpoint. BUG-046 remains open and its repair takes priority.

While the checkpoint was frozen, fresh pass1/mini-theories and
bind-free/numerator-and-denominator captures close
REWRITE-LINEAR-EQUALITIES-TO-IFF and NUMERATOR-NEGATIVE. Their exact source
formulas and accepted axiom trios check in
`c2-numerator-negative-frozen-pins.log`; the focused numerator prefix is
2/2 unconditional in 13995 ms (`c2-numerator-negative-mini-replay.log`). An
earlier broad run with the wrong dependency book was stopped (exit 143,
`c2-bind-free-numerator-replay.log`); it has no completed target receipt.

A temporary copy of the registry retaining exact cross-book name components
checks both inverse-uniqueness statements and the previously refused
FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT transfer. Its staged diagnostic
also reaches an unconditional INTEGERP-MOD with the accepted axiom trio
(`c2-integerp-mod-registry-staged-rerun2.log`), but the helper stage reports
command-budget errors: this is NOT a passing probe file or a permanent
source pin. Earlier syntax/initializer failures remain recorded. The next
naming patch is prepared in scratch files; production naming is unchanged.
No NS1 native product is proved.

The ORDEREDP-MEMB regression is repaired at the actual window: its running
IF test is `(EQUAL 'NIL (CAR A))`, while BEGIN-IF records the stripped test
`(CAR A)` and SWAPPED-P. The new anchor filter recognized only the IF-shaped
negation. The inline and combined consumers now use the already checked
EQUAL-NIL swap judgment too; the three existing swap-shape checks share one
helper. `Rewrites.lean` shrinks to 1481 lines. The diagnostic before the
repair is `c2-ordered-window-diagnostic-replay.log`.

The focused ordered-perms prefix is 6/6 unconditional in 52899 ms
(`c2-ordered-window-equal-nil-replay.log`). Reciprocal source/axiom pins
and context controls build in 6225 jobs
(`c2-ordered-window-equal-nil-build.log`). The two previously failing
waypoint/coverage modules and the new actual EQUAL-NIL window mutation
control build in 3130 jobs (`c2-ordered-window-regression-pins-build.log`);
coverage matches the unchanged 6/6 section. Static checks pass
(`c2-ordered-window-static.log`). This is an intermediate **fast-gate**
repair. The 7445845 full gate remains red and still needs a complete rerun.

The smaller per-dependency INTEGERP-MOD diagnostic now passes as a whole
Lean file (`c2-integerp-mod-dependency-stages.log`, exit 0). It replays six
actual helper statements, the mini-theories statement and NUMERATOR-NEGATIVE
at the consumer's world before INTEGERP-MOD; every stage is unconditional,
and INTEGERP-MOD has only the accepted axiom trio. A separate independent
source-formula pin is running. Production registry naming and permanent
capture/pin integration remain pending; this is still no native product.

The independent INTEGERP-MOD source pin now passes too
(`c2-integerp-mod-frozen-source-pin.log`, exit 0, accepted axiom trio).
It remains a diagnostic staged replay. Both production macro attempts —
standard and `inline_deps` — hit the default 200000 command budget
(`c2-integerp-mod-standard-import.log`, `c2-integerp-mod-inline-import.log`).
The importer needs decomposition; no limit was raised. Profiling is in
`c2-integerp-mod-inline-profile.log`.

The production naming change now preserves registry keys as structured Lean
name components, across CLI declarations, cross-book/termination caches,
transport lookups and their statement pins. The affected executable and
arithmetic pins build in 6224 jobs (`c2-registry-name-focused-build.log`).
Both actual escaped zero rules replay (`c2-registry-escaped-zero-replay.log`;
7/13 unconditional plus two conditional rows in the selected prefix,
47417 ms). A permanent control checks that the plus/star inverse-uniqueness
imports and their multiplication consumer have distinct declarations of
their exact source-statement types, with no premise binders and only
accepted axioms (`c2-registry-name-contexts-build.log`, 3125 jobs).
The changed sorting declaration pins and full regression still need checking.

The next FLOOR-bound dependency has a fresh unchanged capture through
<-OF-*-AND-*-CANCEL at ef2746dade (23170 lines, 22/22 QED/declarations;
`c2-positive-primitive-current-capture.log`). Its two actual POSITIVE USE
instances now consume the complete primitive axiom from axioms.lisp:4340:
addition includes the complex lexicographic order; multiplication retains
both rationality premises. Primitive wiring builds in 6214 jobs
(`c2-positive-primitive-wiring-build.log`). The whole proof then reaches
its two application clauses (`c2-positive-primitive-whole-cancel.log`).
The source uses CASES and USE together; prove.lisp applies CASES first and
USE to each case. Both recorded children are present. Sharing the existing
case-partition validator/composer with USE is in progress; the first build
fails on mutable-variable shadowing (`c2-positive-use-cases-build.log`).
No whole cancellation or new native mirror is claimed.

The USE+CASES composer builds after the shadowing fix
(`c2-positive-use-cases-build-rerun.log`, 6214 jobs). The actual children
then expose a RATIONALP sum/negation cell and later-literal rational
assumptions. The shared primitive type-set table and its clause-context
demands now cover those operands; RATIONALP's two-valued range is consumed
by the recorded Y recognizer. The NOT-FLG path also applies the existing
recorded IF-collapse checker before its constant negation fold, matching
rewrite-clause's dumb-negate-lit step (simplify.lisp:7753). Builds pass
through `c2-positive-negated-if-build.log` (6214 jobs), but the whole
cancellation proof remains open at the boundary verdict described below.

The first full profiler run was stopped after its instrumentation became
costly; it yielded no completed importer profile. Narrow diagnostic timing
(`c2-integerp-mod-harness-timing.log`) shows INTEGERP-MOD's own tree takes
about 31600 user heartbeat units, with the timeout during dependency
discharge. An experimental explicit source-development option stages eight
dependencies at the consumer's world. Each checks under the unchanged
200000 command limit, but the final import still exceeds it
(`c2-integerp-mod-source-stages.log`). Further timing identifies the cost:
EQUAL-DENOMINATOR-1, reciprocal sign and product sign dependencies were
still replayed inside that final command. Staging those existing proofs too
passes the whole import, its independent INTEGERP-MOD source pin and all
sixteen axiom checks (`c2-integerp-mod-all-cost-stages.log`, exit 0). The
option and these diagnostic captures are not yet integrated permanently.
No budget was raised.

BUG-048 records rewrite-atm's independent boundary proof replacing the
attempted rewrite while the instrumentation retains both in one chain.
A separate sparse fork checkout `.tmp/ns1/acl2-atm-boundary`, branch
`mdd/ns1-atm-boundary`, has diagnostic commit `567617bd10`. Its raw-only
retention follows the source's three actual outcomes: independent type-set
proof, retained IMPLIES expansion, or the original rewrite accepted by
try-clause. The initial image build failed on a missing closing parenthesis;
the corrected image and tag check pass
(`c2-atm-boundary-isolated-image-build-rerun.log`,
`c2-atm-boundary-isolated-tags.log`). An initial capture lacked its output
directory; the next lacked the production system-books path. With
ACL2_SYSTEM_BOOKS pointing at the unchanged production books, capture passes
22450 lines and 22/22 QED/declarations at the clean diagnostic commit
(`c2-atm-boundary-capture-system-books.log`). All six reconstructed boundary
instances now retain one IMPLIES expansion before their verdict
(`c2-positive-boundaries-isolated.log`). Replay still refuses the nontrivial
boundary (`c2-positive-isolated-whole-frontier.log`); its checked consumer
and production integration remain pending. The production fork remains
clean at ef2746dade. Current static checks pass
(`c2-registry-positive-static.log`); the affected regression build is running.

The affected registry regression build passes all four requested modules,
including Tests.SortingPins and Tests.SortingPinsEndgame
(`c2-registry-positive-regression-build.log`, 3138 jobs). This is an affected
build receipt, not a full-gate result. The isolated boundary fork adds a
freshness check so it retains only the verdict emitted by the current
TYPE-SET call: clean commit `56948b4df642`. Its image rebuild, tags and fresh
22450-line capture pass (`c2-atm-boundary-freshness-clean-image-build.log`,
`c2-atm-boundary-freshness-tags.log`, `c2-atm-boundary-fresh-capture.log`).
The production fork remains ef2746dade.

The production `driver_replayed% ... from sourceDev` interface now stages
source trees at the consumer world and refuses any retained conditions.
Definition and primitive world checks still run at every actual use; this
is reconstruction, not transport under an assumed world inclusion. Three
unchanged-source captures have permanent paths under `acl2_samples/ns1/`
and commands in `capture-ns1-logs`. The first permanent build passes
(`c2-mod-permanent-staging-build.log`, 3152 jobs): Tests.Ns1Mod has the
independent INTEGERP-MOD source pin and build-failing axiom checks on all
sixteen declarations. All commands use the default heartbeat limit. A
missing-dependency control is being added.

The original isolated boundary DP and composition probes timed out inside
the decision procedure (`c2-positive-boundary-dp-timed.log`,
`c2-positive-boundary-compose-rerun.log`). A diagnostic using Boolean
normalization and the already proved primitive POSITIVE laws checks the
exact fresh leaf with no clause assumptions
(`c2-positive-boundary-primitive-rerun4.log`, exit 0, accepted axiom trio).
Proof construction takes about 694 user heartbeat units, kernel checking
about 157 more. Earlier tactic probes failed or left goals and carry no
proof receipt. The small tactic is now wired inside the existing bounded
DP attempt; the boundary composer replays the retained prefix, checks its
endpoint, proves the isolated verdict, then applies NOT-FLG. Its affected
build and whole cancellation replay remain pending. There are still zero
new NS1 native products.

The boundary consumer's affected build passes in 3149 jobs
(`c2-atom-boundary-consumer-build.log`). All six actual prefix/verdict
compositions check, with accepted axiom closures, and the diagnostic
mutations of prefix, input, output and polarity are rejected. Both actual
POSITIVE instances reject changed substitutions and hypotheses; a missing
CASES child and a changed case partition are rejected too
(`c2-positive-boundary-use-controls-rerun2.log`). Two preceding control
files failed on Lean record-layout syntax. These remain diagnostic controls
until the isolated capture is integrated.

Whole cancellation advances to Subgoal 2.9's X2 := X1 substitution
(`c2-positive-boundary-whole-replay.log`); it is not a complete proof.
BUG-049 records the missing intermediate equation insertion in
process-equational-polys. Source inspection distinguishes that operation
from remove-trivial-equivalences, whose emitted substitution follows it.
The old quoted-RHS fallback is unchanged. The actual insertion, numeric
completion and possible forcing flags need recording before composition.

The permanent source-stage negative control passes: an actual
NUMERATOR-NEGATIVE import without its mini-theories dependency is refused.
Tests.Ns1Mod and Tests.Ns1Contexts both build with the new leaf checker
(`c2-mod-source-stage-controls-build.log`, 3127 jobs). An earlier direct
invocation raced the affected rebuild and failed on the temporarily absent
Runner.olean (`c2-mod-source-stage-control.log`); it carries no proof receipt.
The initial static round passes (`c2-staged-mod-boundary-static.log`);
tracking the new files/captures requires the final static rerun before an
intermediate fast-gate commit. Full regression and NS1's three products
remain open.

The final tracked-file static round passes
(`c2-staged-mod-boundary-tracked-static.log`): 110 provenance-stamped logs,
88 embedded-log references, and all ordinary static recipes. This
checkpoint is **fast-gate**, with the affected builds and focused actual
replay/control receipts above. The new source captures retain ACL2's raw
trailing whitespace; they were not edited to silence `git diff --check`.
Code/document whitespace checks are separate. Full claim-gate is next;
BUG-048's producer and diagnostic capture remain isolated, and BUG-049
is the current whole-cancellation frontier.

The full gate at `d452422` is red:
`.gate-runs/d452422-20260906T194643Z.log`, **TRUE_EXIT=1**. Basics/REV-APP,
PERM-CONS/PERM-SYMMETRIC/PERM-RM and the corresponding coverage, driver,
pattern and sorting pins reject the new boundary endpoint check. The
actual PERM-CONS literal is `(NOT (CONSP (CONS X1 X2)))`: the old log keeps
a recognizer rewrite to T before the boundary verdict on the original
CONSP atom (`c2-perm-boundary-regression-shapes.log`). The known BUG-048
producer replacement is needed on those captures too; weakening the new
check would retain the wrong proof path.

The production fork now has the two checked boundary fixes, cherry-picked
as `094ebcc7ee` and `aac5e1a45d`, with a fresh image
(`c2-boundary-production-image-build.log`). Full corpus recapture and a
new gate are pending. The isolated fork has separate diagnostic commit
`1589f73292`, recording the actual linear equation insertion's input/output,
inserted literal, numeric flags, selected polynomial pair, assumptions and
runes. The first image failed the raw-code registration check; registering
PROCESS-EQUATIONAL-POLYS fixes it. Its image, tag check and source capture
pass (`c2-linear-insertion-registered-image-build.log`,
`c2-linear-insertion-registered-tags.log`,
`c2-linear-insertion-dirty-capture.log`); the clean committed image rebuild
also passes (`c2-linear-insertion-clean-image-build.log`). The diagnostic
source capture was made before that commit and is stamped dirty; it is not
a production artifact. Its six records all have KNOWN-TRUE numeric flags,
no added assumptions and complementary two-term polynomial pairs. The
current reader rejects LINEAR-EQUATION, as it should
(`c2-linear-insertion-current-reader.log`). No linear insertion is replayed.

The three new MOD capture paths follow the repository's generated-artifact
convention: their files remain on disk and their capture commands are in
Justfile, but the accidentally force-added logs/sidecars are removed from
Git tracking in this fix round. Their bytes are unchanged by that index
correction. The earlier capture-integrity and source-pin receipts stand.

The production recapture finishes successfully
(`c2-boundary-production-recapture-all.log`), with 110 logs stamped at
clean aac5e1a45d. The times prefix now ends at <-OF-*-AND-*-CANCEL so its
actual boundary controls are permanent in Tests.Ns1Positive. The affected
build passes in 3159 jobs (`c2-boundary-production-focused-build.log`):
Basics and PermBook import again; sorting/perm matches its unchanged 8/8
golden; the six boundary compositions and their USE/CASES mutation controls
pass; INTEGERP-MOD and its missing-dependency control still pass. Static
checks pass (`c2-boundary-production-static.log`). This producer-integration
checkpoint is **fast-gate**, not a repaired full-baseline claim.

The clean isolated 1589f73292 image/capture also passes
(`c2-linear-insertion-clean-capture.log`, 22450 lines, 22/22 source events).
The full corpus boundary-shape triage reports 77 supported-tree boundary
instances, all the same negative/T/NIL class. It explicitly reports the
known unread/unreconstructed pattern books; it is a shape inventory, not
coverage (`c2-boundary-corpus-shape-triage.log`). A prior inventory looked
only at Git-tracked logs and returned no boundaries; most captures are
intentionally generated/ignored. The new linear-insertion reader is prepared
but not yet applied. Its next-step source notes are in
`.tmp/ns1/linear-insertion-next.md`; no new proof scope has been assumed.

The next isolated source increment, `aaaaaea5c4`, records `:PARENT-CLAUSE`
at the initial PROCESS-EQUATIONAL-POLYS call. Its PT indices address that
original clause even after recursive insertions change the current clause.
The ordinary SBCL startup attempt failed at the nono boundary on
`/etc/sbclrc`; the repository's existing `--no-sysinit` build succeeds and
refreshes the image (`c2-linear-parent-clean-image-build.log`). Capture
needs `ACL2_SYSTEM_BOOKS` pointing to the unchanged production books because
the isolated checkout is sparse. Its successful receipt is
`c2-linear-parent-clean-capture-system.log`, 22450 lines / 22 QED events.
Earlier attempts used the absent sparse book path or omitted that environment
setting and did not produce a promoted capture.

The reader retains all six actual LINEAR-EQUATION items in the reconstructed
tree (`c2-linear-parent-reconstructed-tree.log`). The first reader builds
exposed missing exhaustive cases in the literal/discharge/term collectors;
the repaired reader/Runner build passes in 3139 jobs
(`c2-linear-parent-reader-build-rerun.log`). Insertions are not classified as
verdict-only discharge leaves or globally available rewrite hypotheses.
The new record requires its fields and rejects malformed/duplicate fields.
The parser's first static gate found growth past ProofLog's grandfathered
limit; its shared field readers are extracted to ProofLogFields rather than
raising the limit. The final extraction rebuild is pending below.

The first consumer checks the actual direct unit polynomial pair against
its PT comparisons and rationality premises. A generic component-order
judgment proves the complementary-row consequence; deterministic additive
normalization checks the emitted row against its source comparison. This
does not widen the old branch-level DP fallback. The continued clause
consumes the recorded substitution and duplicate removal, then its exact
pushed child. The first extracted actual subtree checks with the visible
condition `rule:NOT-<-SAME` (`c2-linear-insertion-fragment-telescopes.log`).
Earlier diagnostics exposed metadata layout, Boolean-to-truth conversion,
and quoted-integer cast normalization errors; these were explicit replay
failures. Whole cancellation now reaches the Boolean type-set query for
`(< (* X1 Y) (* X2 Y))`, whose recorded mask is 384 and whose rune list is
empty (`c2-linear-insertion-controls.log`). It is still not replayed in full.
The first attempted all-six control run stopped at that whole-theorem
frontier; the first direct subtree harness lacked the stored-rule telescope.
Neither is a passing mutation-control receipt.

The unchanged less-than source through NOT-<-SAME has now been captured
(`c2-linear-less-than-capture.log`) for that concrete dependency. The
comparison's Boolean range is being added to the existing primitive
type-set registry. A fresh msort diagnostic also exposes four insertion
records using ACL2-COUNT type prescriptions and ACL2-COUNT-CAR-CDR-LINEAR
(`c2-linear-parent-msort-tree.log`). Those need checked consumers before
the isolated producer can replace production. This is not an all-linear
certificate support claim.

The existing arithmetic, INTEGERP-MOD and six atom-boundary tests build in
6232 jobs (`c2-linear-existing-focused-build.log`; INTEGERP-MOD module 250s).
That build predates the field-reader extraction and comparison-range change.
The subsequent ordered-perms command's rebuild hit a stale registry consumer
while the next edit was being applied; it did not run the book. A fresh
sequential rebuild and focused replay are required. The initial static gate
is red solely at the parser file-weight check
(`c2-linear-reader-static.log`); no repaired full-gate claim is made.

The field-reader extraction and primitive comparison Boolean range build
successfully (`c2-linear-parser-range-build.log`, 3143 jobs). Static checks
now pass (`c2-linear-reader-static-rerun.log`), including the unchanged
file-weight caps, import reachability and all 110 production provenance
stamps. The less-than capture has 12204 lines / four QED events, through
NOT-<-SAME. Supplying its actual tree closes that dependency in every
insertion subtree: Subgoals 2.9, 2.8, 2.6, 2.5, 2.3 and 2.2 all check
unconditionally with `{propext, Classical.choice, Quot.sound}`
(`c2-linear-insertion-closed-fragments.log`). That same run rejects nine
mutations: changed parent scope/output, missing polynomial pair, reversed
coefficients, missing numeric PTs, forcing flags/assumptions, missing child,
and missing duplicate-removal record. The tested roots are the unchanged
subtrees extracted from the actual capture, not fabricated positive nodes.
The whole-theorem rerun is still pending, and these fragments are not new
native products. The isolated capture is diagnostic; its producer is not
yet the production submodule.

The whole cancellation run reaches the existing 3M-heartbeat limit at
`isDefEq` (`c2-linear-product-with-less-than.log`). It remains open; no
budget was raised. A separate profile is locating the cost before choosing
the decomposition. The first profile harness had a MetaM/TermElabM logging
type error and did not run; the corrected harness is pending.

The focused ordered-perms regression first returned 5/6: the new adjacent
duplicate consumer chose clause order, but ACL2 emits `(NOT (ORDEREDP A))`
before `(NOT (TRUE-LISTP A))` after B := A. The consumer now selects the
adjacent pair named by the next recorded removal and consumes that record.
The rebuilt focused book returns **6/6 unconditional** in 56580 ms
(`c2-linear-ordered-perms-record-order.log`); the build receipt is
`c2-linear-recorded-dedup-order-build.log`. An earlier command used the
`replay` recipe with a corpus key instead of a file and failed before
replay; `replay-book sorting/ordered-perms` is the correct dependency-aware
command. These are fix-round receipts, not a full-baseline claim.

### C2 cancellation arithmetic cost (2026-09-06, in progress)

The full gate on `d12e966` is **RED**, with `TRUE_EXIT=1` in
`.gate-runs/d12e966-20260906T211317Z.log`. It found a missing
`ClauseItem.linearEquation` case in `Tests.TamperTests.mapItem`. Sorting's
coverage and endgame axiom pins subsequently built. The final
`Imported.Waypoints.SortsEquivalent` job was deliberately terminated after
1295 seconds so the already-failed fix round could proceed; its exit 143 is
an interruption, not a newly diagnosed proof failure. This is not a
complete regression receipt. The source stayed unchanged until the run
ended. The test helper now preserves the insertion item while mapping
ProofNodes, since that item contains no ProofNode.

The corrected phase profile located the cancellation timeout inside
reconstruction. Clause timing measured about 776644 user heartbeats in
Subgoal 2.4 and 1809081 in Subgoal 2.1; the recorded insertion subtrees
cost about 4–7k each. The profile reached Subgoal 1.7 before the existing
3M limit. The cause was the rational DP leaf normalization: sums and
negations were left unnormalized, and early Boolean expansion made
`split_ifs at *` enumerate comparison signs.

The candidate normalizes addition/negation through `numberParts`, retains
propositional truthiness until comparisons normalize, and simplifies their
`Ne`/conditional forms before splitting. The arithmetic solver and all
resource limits stay unchanged. The actual clause and its emitted rational
premises are unchanged. Initial experiments exposed an unknown lemma name
inside a guarded temporary tactic and a redundant final `simp_all`; both
were corrected before the passing runs.

All **12 actual emitted cancellation DP leaves** pass with the candidate
and the production normalization prefix under the existing 15000-heartbeat
direct-attempt limit (`c2-rational-product-all-leaves.log`), using about
1595–2623 tactic heartbeats each. That initial receipt used `Meta.check`,
which is the metaprogramming type checker, not the kernel. The explicit
`Meta.checkWithKernel` rerun also passes all 12 leaves and their accepted
axiom scans (`c2-rational-product-all-leaves-kernel.log`); it is the kernel
receipt. The earlier user-facing description of the initial check as a
kernel check was corrected during the run. The three measured hot-spot checks are also
recorded in `c2-rational-product-leaves-bounded-rerun.log` and
`c2-rational-product-leaves-driver-prefix-rerun.log`. These are actual leaf
proofs, not a whole cancellation or native-product claim. The affected
production build passes (`c2-rational-production-build.log`, 3157 jobs),
as do the explicit kernel regression pins
(`c2-rational-production-kernel-test-build.log`, 3129 jobs) and static
checks (`c2-rational-production-static.log`).

The first production whole-theorem run finishes with one visible condition,
`rule:COMMUTATIVITY-2-OF-*` (`c2-rational-product-whole.log`). Replaying that
actual dependency exposes its two `:USE` instances of
`ASSOCIATIVITY-OF-*`. This is the primitive axiom at axioms.lisp:4299,
already modeled by `Logic.times_assoc` for rewrite steps. PrimitiveUse now
checks the exact source schema under the recorded translated substitution
and uses that same model proof for the cited premise; the ordinary USE
application clause is still fully replayed. No new primitive law or DP
allowance was added.

Both the commutativity dependency and **the complete cancellation theorem
now replay unconditionally**, with the accepted axiom trio
(`c2-associativity-use-dependency.log` and
`c2-associativity-use-cancellation.log`). The latter uses the unchanged
isolated times capture at aaaaaea5c4 and the actual basic-arithmetic and
NOT-<-SAME dependency trees. This is a closed replayed statement from a
diagnostic capture, not a promoted producer or a native BVCHOP mirror.
The production commutativity source pin, its axiom receipt, the three
production DP kernel checks and mutations of both actual associativity USE
instances pass (`c2-associativity-use-permanent-test-rerun.log`, 3129 jobs).
The first negative test accidentally left an empty identity substitution
unchanged; the corrected mutation explicitly inserts X and both instances
reject it. The existing POSITIVE mutation checks share the same helper and
still pass. The rebuilt ordered-perms book returns **6/6 unconditional**
in 54236 ms (`c2-rational-ordered-perms-replay.log`). Static checks pass
(`c2-associativity-use-static.log`); no captures or production fork pointer
changed in this fix round. These are fast-gate receipts. The complete
regression rerun remains pending.

The broader insertion consumer still needs msort's type-set-bound and
rewritten-linear-rule classes. Its retained pre-literal rewrite nodes are
currently handled by the legacy setup-memo path in CoreSpine. A new
consumer must connect their actual proof chain to the inserted equation;
they must not be treated as if they were already replayed. The isolated
producer remains unpromoted.

### C2 regression recovery and quotient frontier, 2026-09-06 22:33 UTC

The source remained clean at **2953c78** throughout the full rerun:
`TMPDIR="$PWD/.tmp" just claim-gate`, artifact
`.gate-runs/2953c78-20260906T215722Z.log`, manually read **TRUE_EXIT=0**.
All 116 baseline theorem rows are unconditional, the coverage golden is
byte-identical, and the seam gate reports all 21 existing products with
accepted proof paths. This closes the pending full regression checks for
BUG-032/039/046/047/048 and the rational DP/test-traversal repairs. It does
not promote the isolated linear insertion producer or close a new mirror.

The current NIQ upper-bound tree first stops at its induction decrease:
the nonzero NFIX ruler and IFIX lower bound are inside the recorded false
`(IF a a c)` test. A temporary consumer extracts the two components using
the existing `cond_or_nil_inv` proof and proves the captured `=` alias's
value equality from its actual World definition. The actual decrease
passes an explicit kernel check. It then reaches a terminal IFF OR-collapse:
the combined record already identifies the collapse, but the consumer
previously required a following finishing child. Extending that existing
route to the combined record's result also passes an explicit kernel check
inside the actual theorem (`c2-quotient-ruling-or-kernel.log`). These are
fragment receipts; the whole NIQ upper-bound still fails at BUG-050.
No production Lean implementation was changed during the gate.

Isolated fork **f5cada538a**, branch `mdd/ns1-hyp-subst`, lives at
`.tmp/ns1/acl2-quoted-unify` (the directory was created for the earlier
quoted-match investigation; that matcher is still unchanged). It observes
`sublis-var`'s actual cons-term fold inputs, outputs and argument positions,
and snapshots that basis on the known-true hypothesis marker. Raw observer
macros expand to the original forms in the logic. The initial image build
failed the bootstrap's raw-macro declaration check; declaring those three
intentional raw/logic differences fixes it. `make LISP="sbcl --no-sysinit"`
then succeeds (`c2-substitution-fold-image-build-rerun.log`), as do fork tags
and diff checks. A raw diagnostic initially hit nono's `/etc/sbclrc` denial;
using the capture script's existing `--no-sysinit` resolves it. The two raw
observer examples preserve returned values and report the expected fold
positions (`c2-substitution-observer-probe-rerun.log`); they are diagnostics,
not positive proof artifacts.

After the full gate completed, the unchanged NIQ source through
NONNEGATIVE-INTEGER-QUOTIENT-LOWER-BOUND-LINEAR2 was captured with that clean
image, `CAPTURE_WORKER=1` and an isolated OUTDIR. The capture succeeds with
14/12 QED/DEFTHM events (`c2-substitution-fold-capture.log`); source hash is
7a5098c9c7f5f9e19bc65f36a4d26bfe5e53984bb2fefb9bafeb34aa367be391.
The actual missing hypothesis fold is now present at
`c2-substitution-fold-capture/nonnegative-integer-quotient.proof-log:20406`.
The old reader reconstructs the tree but does not yet retain these new
fields. Add strict parsing and recorded fold consumption before any
producer promotion. No hypothesis DP, new arithmetic lemma, budget change,
book edit, or native-spec change was made.

### C2 recorded induction rulers and hypothesis instantiation, 2026-09-06

The induction accessor now shares proof-producing false OR-component
extraction with the existing ATOM decrease path. Equality aliases are
checked against the captured World definition, with their values related
by body convergence and uniqueness. The terminal IFF OR-collapse uses the
existing recorded test-prefix replay and bridge; its endpoint is the combined
record's result when no finishing child follows. The emitted collapse LHS
is checked explicitly. No new arithmetic lemma or resource limit was added.

Production fork **1167a1ac98330ab04ed57fae18ed6726f8134b25** incorporates
the isolated f5cada538a substitution observer. Its image succeeds and passes
the explicit freshness check (`c2-substitution-production-image-build.log`).
`just recapture-all` succeeds (`c2-substitution-production-recapture-all.log`),
and all **110** sidecars carry that clean fork. Source books/hints and the
native specifications are unchanged. The tracked P8 fixture and sidecar
were regenerated normally; other captures remain ignored artifacts.

The reader retains a strict plain-instance/ordered-fold basis on the actual
hypothesis marker. Replay validates each fold's ground arguments, emitted
primitive guard, result and zero-based argument path, then composes those
checked computations to the exact relieved hypothesis. It consumes the
marker there and transports back to the original stored-rule instance.
Quoted truth at the marker is checked directly. This route adds no hypothesis
DP or inferred normalization. One initial compile failed because an early
`return` escaped the enclosing Array-valued computation; replacing it with
a value-producing branch fixes the error.

The temporary actual-tree test and permanent `Tests.Ns1Substitution` check
all **16** nonempty markers using `Meta.checkWithKernel` and the accepted
axiom scan. They reject deleted folds, changed results/positions and missing
primitive guards; the permanent test also rejects unpaired fields and a
non-integer path. Receipts are `c2-substitution-folds-actual-controls.log`
and **`c2-substitution-permanent-tests-build.log`** (3134 jobs, including
Ns1Positive, Ns1Contexts and TamperTests). Reader/driver builds pass
(`c2-ruling-substitution-reader-build.log`,
`c2-hyp-substitution-consumer-build-rerun.log`,
`c2-hyp-substitution-tree-build.log`). The reconstructed tree displays the
actual fold under its hypothesis (`c2-substitution-fold-reconstructed-tree.log`).

Focused regression preserves **LEN-ZIP2 1/1**, **LEN-ZIP3 1/1** and
**ordered-perms 6/6**, all unconditional, in 5276, 8202 and 60342 ms
respectively (`c2-ruling-zip2-replay-rerun.log`,
`c2-ruling-zip3-replay-rerun.log`, `c2-ruling-ordered-perms-replay.log`).
The first ZIP commands used a doubled recon-tests path; those command
failures are superseded by the correctly named book reruns. Static recipes
pass (`c2-substitution-production-static.log`).

The capture comparison is explicit about its limits. **108 parsed logs
preserve 14696 original events**, modulo the added hypothesis basis and
one newly cited recognizer tuple: p6-or-collapse-arith now cites
ACL2-NUMBERP through its actually recorded ground fold. All existing
recognizer entries are unchanged by unique function key; proof event order
is preserved. `cov-force-round` and `cov-or-hint` retain their existing
forcing/package-marker parser refusals; their events were not compared.
The initial comparison stopped on the first parser frontier; the next
stopped on the recognizer addition. The final comparison checks that every
added recognizer is named by an actual fold and reports the two uncompared
logs (`c2-substitution-production-event-comparison-final.log`). These
comparison projections are never used as replay inputs. The initial
user-facing description as an ordering change was corrected after inspecting
the complete snapshot: it is one added entry.

Whole NIQ upper-bound replay passes these nodes but still refuses the
known-true `(< '0 J)` hypothesis of <-OF-*-OF-/-ARG1-ARG2
(`c2-quotient-production-after-folds.log`). Its marker has no recorded
comparison/type-set basis; BUG-039 is reopened for that distinct class.
The quoted-constructor matcher remains unchanged. Next capture the actual
query route and consume its evidence, while preserving the no-hypothesis-DP
boundary. These are fast-gate receipts. A fresh full regression run remains
required for this increment; C2 and all three native products remain open.

### C2 increment — actual comparison tables (2026-09-06)

The fresh quotient tree identifies the missing known-true comparison route:
`type-set-<` selects its numeric table with left mask 1, right mask 6, and
result 256 for `(< '0 J)`. Both occurrences are under
`<-OF-*-OF-/-ARG1-ARG2` in NONNEGATIVE-INTEGER-QUOTIENT-UPPER-BOUND-LINEAR
(`c2-known-comparison-tree.log`:1870,1962). The root query observer records
the selected lookup, constant-bound, or table route without repeating its
computation. Unsupported routes remain explicit consumer frontiers.

The parser/tree retain `:COMPARISON-BASIS`. The table consumer checks the
reported result and numeric projection, proves membership in the recorded
right mask using the existing context/type-set walker, and applies the
existing zero/positive-rational primitive law. No arithmetic lemma, solver,
or budget was added. The following RATIONALP sum hypothesis already cited
the quotient's TP; forwarding its existing citations to the shared consumer
lets that step replay too. Repeated citation extraction was consolidated.

The isolated observer is **3d78183cc7**; production is
**fd27e59021cf7d0103a526dbda41553ad709eae3**. The initial isolated build
required the new raw observer functions to be declared in ACL2's bootstrap
program-function registry; the corrected image and tag check passed. The
production image also passed its success/freshness checks, and all **110**
permanent captures were regenerated with that fork stamp. The tracked P8
fixture/sidecar changed through the capture recipe.

Capture comparisons distinguish three checks:

- The selected isolated NIQ capture preserves all **462** original events
  modulo the comparison field (`c2-known-comparison-event-comparison.log`).
- All **110** isolated corpus recaptures succeed. **108** parseable logs
  preserve all **14,696** original events modulo that field; `cov-force-round`
  and `cov-or-hint` retain their exact forcing/package parser refusals and
  their events are not compared (`c2-known-comparison-corpus-comparison.log`).
  New basis records occur only in five NS1 captures, including unselected
  constant-bound routes in `basic`; sorting/reconstruction captures have none.
- All production capture text matches that isolated corpus except the two
  expected ACL2 banner lines containing the image build time and embedded
  Git hash (`c2-known-comparison-production-artifact-comparison.log`). An
  initial byte-equality assertion stopped at those banner differences;
  the final comparison excludes exactly those two lines in each log.
  Comparison projections never enter replay.

`Tests.Ns1Comparison` consumes the two actual upper-bound nodes under facts
drawn from their recorded clauses and branch paths. Both proofs pass
`Meta.checkWithKernel` and the accepted-axiom check. Changed verdicts and
numeric projections, removed routes/context/basis, and malformed parser
fields are rejected. The new test's first build had a record-layout syntax
error; it was corrected. The focused build command also initially named a
nonexistent `Tests.Ns1Mod16`; the real module is `Tests.Ns1Mod`.

Static recipes pass (`c2-known-comparison-production-static.log`). The
corrected focused build passes **6242 jobs**, including `Tests.Ns1Comparison`,
`Tests.Ns1Substitution`, `Tests.Ns1Positive`, `Tests.Ns1Contexts`,
`Tests.Ns1Mod`, `Tests.TamperTests`, and the replay executable
(`c2-known-comparison-production-regression-build-rerun.log`). The
INTEGERP-MOD module, including its staged dependency proofs and axiom
receipts, builds in 238 seconds. These are fast-gate receipts. The
focused `ordered-perms` replay passes **6/6 unconditional theorem rows** in
51,583 ms (`c2-known-comparison-ordered-perms-replay.log`); its informational
DP brackets retain their existing separate assumed rows. The last full
claim-gate remains `.gate-runs/2953c78-20260906T215722Z.log`, `TRUE_EXIT=0`.
No new full-gate or native-product completion is claimed here.

The production whole quotient probe crosses the two comparison nodes and
the cited-TP recognizer, then stops at **BUG-051**, Subgoal *1/3': the actual
context-contradiction leaf contains three negated FC conclusions after the
branch accumulator. Its adapter currently accepts only an empty FC suffix.
`simplify.lisp` constructs this obligation from the actual selected FC pairs;
the record must retain their selection and proofs before the extra literals
can be peeled. Receipt: `c2-quotient-comparison-production-whole.log`; its
trailing unknown-constant error is the unavailable whole-proof axiom query.
Ordinary FC-rule dependency proofs, remaining quotient/FLOOR dependencies,
the shared operation/decode kit, and all three native products remain open.

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
