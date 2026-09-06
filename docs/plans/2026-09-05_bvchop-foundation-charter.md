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

## Resume record

- Approved docs are committed on `main` at `b452b70`; implementation lives
  in `/home/dev/projects/ACL2Lean/.claude/worktrees/ns1-bvchop`, branch
  `mdd/ns1-bvchop`. C0 is committed at `31d8e42`; C1 is `276f4b8` and carries
  the full gate receipt above.
- C0's two review tasks are complete. The two C4 tasks remain authorized;
  no preflight questions are pending.
- Next: extend the linear premise consumer for the actual multi-hypothesis bound rule,
  close that dependency proof, and build the first native proof.
- C2–C4 and all three new mirror proofs remain open. NS1 is in progress;
  there is no merge or push approval for the implementation.
