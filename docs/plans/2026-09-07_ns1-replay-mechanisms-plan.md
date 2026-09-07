# NS1-R — reusable type-query and clause-edit replay

Dated 2026-09-07. **Execution activated; R0 checkpointed, R1 scope frozen; R2 in progress.**
Evidence and current next actions are in the
[execution record](../notes/2026-09-07_ns1-r-execution.md).
This is the next bounded slice within NS1, following the project check-in.
It changes the immediate execution sequence, while preserving the three
native propositions and completion requirements of the
[NS1 charter](2026-09-05_bvchop-foundation-charter.md). The
[master plan](2026-09-05_master-plan.md), [lexicon](../LEXICON.md), and
[working rules](../../CLAUDE.md) remain binding.

## Objective

Build reusable machinery for two recurring ACL2 proof mechanisms:

1. Recorded type queries, including recognizer queries whose arguments
   contain conditional expressions.
2. Recorded clause edits, including equality substitution with retention
   or deletion of the selected literal and the subsequent clause cleanup.

Establish their supported scope from actual ACL2 source branches and captured
proof trees before broadening the implementation. Consolidate the existing
consumers behind shared, kernel-checked judgments. Demonstrate the result
through six complete arithmetic dependency replays, reuse outside those
dependencies, and a measured replay of their consuming proof.

**This slice has its own completion condition.** It does not require a new
native mirror, and completing it does not close NS1 checkpoint C2. It must
deliver integrated reusable code and complete dependency proofs; a survey,
collection of successful leaf probes, or proposed abstraction is insufficient.

**Agent-declarable early exit:** stop incomplete with the exact artifact and
obligation if a mandatory acceptance proof requires a mechanism outside the
frozen scope, unavailable evidence, a new semantic or fidelity ruling, or an
excluded proof route. Do not recursively expand the slice to absorb that
obstruction. Continue independent work within the frozen scope before the
terminal report when that work remains useful. A successful slice and an
incomplete stop are distinct outcomes.

## Workspace and preservation

Continue in the existing worktree:

```text
/home/dev/projects/ACL2Lean/.claude/worktrees/ns1-bvchop
branch: mdd/ns1-bvchop
planning checkpoint: 7598d0a
```

The migration, checked dependencies, diagnostic ACL2 producer, and build
artifacts already live there. A new worktree from main would omit the work
this slice depends on. A second checkout from the NS1 branch would add build
and capture setup without providing a needed separation: this is a sequential
consolidation of that implementation, with no simultaneous implementation team.
Use local commits to delimit the slice; leave other worktrees untouched.

At planning time three implementation files are uncommitted:
`ACL2Lean/NumericComponents.lean`,
`ACL2Lean/Replay/Driver/ComplexViews.lean`, and
`ACL2Lean/Replay/Driver/Discharge.lean`. They contain the latest primitive
negation work. Preserve and inspect them at R0; record their diff and actual
receipts before making a separate intermediate checkpoint. Do not reset,
stash away, or silently include them in a later architectural change.

The production ACL2 submodule is at
`fd27e59021cf7d0103a526dbda41553ad709eae3`. The diagnostic producer in
`.tmp/ns1/acl2-ta-singleton` is a separate checkout; its recorded checkpoint
is `df7a28e38c`. Verify both identities and saved-image provenance at R0.
Existing diagnostic success does not establish production integration.

No merge, push, publication, goal activation, or additional subagent campaign
is part of writing this plan. Implementation can make verified local commits
under the existing gate tiers. The two NS1 C4 review tasks remain reserved
for that checkpoint; this slice does not spend or enlarge that allocation.

## Starting evidence and unresolved uncertainty

The numeric migration is complete. The last full claim gate is
`.gate-runs/a38c7f5-20260907T095722Z.log`, with `TRUE_EXIT=0`,
116 unconditional baseline rows and 21 existing native mirrors. Subsequent
increments have focused receipts, not a fresh full-gate claim.

The latest diagnostic staging replays 24 bootstrap/component declarations
plus seven minus/component-negation declarations unconditionally. The latter
receipt is `.tmp/ns1/c2-minus-negation-unconditional-stages.log`; the affected
build passed in `.tmp/ns1/c2-primitive-negation-affected-build.log`. These 31
declarations are a particular staged chain, not a census of all NS1 proofs.

The selected six theorems are in unchanged
[`kestrel/arithmetic-light/times.lisp`](../../acl2/books/kestrel/arithmetic-light/times.lisp):

| Required complete replay | Last observed obstruction |
| --- | --- |
| `<-OF-*-AND-0` | Known-true `BOOLEANP` query over a comparison |
| `<-OF-0-AND-*` | The same query family |
| `<-OF-*-AND-*-CANCEL` | Recorded literal deletion after linear substitution |
| `<-OF-*-AND-*-CANCEL-GEN` | Known-true `BOOLEANP` query; nested conditional arguments also occur |
| `<-OF-*-AND-*-CANCEL-ARG1-AND-ARG2` | Conditional on CANCEL-GEN and CANCEL |
| `<-OF-*-AND-*-CANCEL-ARG2-AND-ARG1` | Conditional on CANCEL-GEN and CANCEL |

Evidence: `.tmp/ns1/c2-strict-arithmetic-staged-dependencies.log` and
`.tmp/ns1/c2-strict-arithmetic-frontier-trees.log`. Refresh these observations
against the preserved starting state before treating them as current failures.
An older isolated cancellation capture replayed unconditionally; that does
not discharge the deletion now recorded by the current producer.

Two concrete composition gaps motivate the design:

- [`KnownTrue.lean`](../../ACL2Lean/Replay/Driver/NodeCore/KnownTrue.lean)
  invokes recognizer replay with an empty argument-leaf list.
  `HypRecognizerBasis` records the outer masks and recognizer tuple, whereas
  a separate `HypIfBasis` handles a root IF. Actual nested-IF recognizer
  queries have no corresponding branch evidence in that channel.
- [`LinearSubstitution.lean`](../../ACL2Lean/Replay/Driver/Waterfall/LinearSubstitution.lean)
  accepts retention and explicitly refuses `DELETE-LITERAL T`. ACL2's
  `remove-trivial-equivalences-rec` treats retention and deletion as branches
  of the same operation; subsequent folds and duplicate removal also belong
  to the resulting clause transition.

The downstream consumer is `<-OF-*-AND-*-SAME-HELPER`, used on the quotient
bound route. Its Subgoals 7' and 6' retain product/cancellation conditions;
9.12, 9.18' and 9.17 have unconditional subtree receipts. Those receipts
do not establish a complete helper. More distant FLOOR/MOD/BVCHOP proofs
have not been exhaustively classified against the current code.

## What replay must establish

Keep three obligations separate:

| Layer | Required evidence and proof |
| --- | --- |
| Recorded reasoning | Follow selected rewrites, rule instantiations, query routes, branch contexts and clause edits. Every consumed premise has a checked derivation. Preserve exact endpoints and required execution children. |
| Verdict-only leaves | At an actually emitted decision-procedure discharge, prove its exact obligation using the existing kernel-checked procedure allowance. This does not license solving a missing rewrite or hypothesis-query trace by automation. |
| Native correspondence | The eventual NS1 mirror connects the replayed statement to the agreed Lean proposition by generic correspondence and transport. This remains outside this slice's implementation. |

Neither a type mask, a recognizer tuple, a cited rune, nor a context snapshot
is an assumed Lean fact. Distinguish primitive semantic laws from ordinary
ACL2 theorems, including ordinary `defthm`s in bootstrap sources. The latter
still require replay. Proving a primitive Boolean membership law does not
authorize registering a handwritten proof of `BOOLEANP-COMPOUND-RECOGNIZER`.

## Scope and rules for controlling expansion

The initial family envelope is fixed here. R1 makes its source cases and
capture requirements precise; it may narrow unsupported cases explicitly
but cannot weaken the six mandatory replay targets.

**Type-query family:** the recorded Boolean/recognizer/comparison and
conditional-query compositions present in the six proofs, together with
already implemented primitive numeric, lookup and branch-membership routes
needed to compose them. Include their existing consumers in known-true
hypothesis relief, explicit recognizer rewriting, and the selected existing
FC or elimination query route used to demonstrate reuse.

**Clause-edit family:** recorded EQUAL substitutions selected from clause or
branch evidence, both retention and deletion, quote-opaque term replacement,
recorded executable folds, NIL removal, duplicate removal, and exact child
composition. Preserve supported occurrences and source-selected orientation;
do not assume arbitrary term replacement is valid at every position.

**Also included:** source-compatible instrumentation for these families,
reproducible capture/provenance integration for the mandatory proofs,
necessary dependency replay through existing or newly frozen mechanisms,
and measured performance repairs inside these mechanisms.

**Excluded:** a universal ACL2 type-inference engine; a replacement waterfall;
an unrestricted arithmetic solver; new numeric semantics; arbitrary user
equivalences as a new supported feature; GL, new SMT backends, arbitrary meta
rules/clause processors, forcing-round composition and guard-proof replay;
the remaining quotient/FLOOR/MOD proof campaign; native mirror construction;
unrelated cleanup or additional audit campaigns.

A large number of instances of a frozen case is implementation work. A new
kind of evidence, inference rule, transformation or context transition is a
scope finding. Record which it is before adding support. In particular,
do not use a growing list of theorem names, clause IDs, preferred captures,
fallback tactics or individually selected masks to define the family.

## R0 — preserve a reproducible starting point

1. Record branch, dirty diff, toolchain, producer/image identities, source
   hashes and capture paths. Check available disk before new captures; avoid
   duplicating ACL2 trees, build directories or saved images unnecessarily.
2. Verify the latest affected build and 31-declaration staging receipts;
   rerun only checks invalidated by a changed input or uncertain receipt.
   Check the actual declarations' types, condition inventories and axioms.
3. Make a separate verified intermediate checkpoint for the existing WIP
   under the fast-gate protocol, including the updated status record.
4. Establish runnable commands for the six-theorem probe and parent helper.
   Their baseline failures are expected observations, not a green result.

**Exit artifact:** a short baseline manifest and replay report. Do not begin
the architectural changes until the inherited state is identifiable and
recoverable. Do not run Lean probes while a core rebuild is invalidating
their imports.

## R1 — inventory the mechanisms before implementing them

Traverse reconstructed trees, not only the driver's first failing node.
Start with the six selected proofs, their actual required dependencies and
the consuming helper. For the higher BVCHOP route, record known dependency
edges and missing trees; an exhaustive crawl of included books is not part
of this slice.

Produce a compact inventory with one row per distinct source case:

| Required field | Purpose |
| --- | --- |
| Source file/function and branch | Defines the real mechanism and its variations |
| Capture identity, theorem and tree address | Makes the observation reproducible |
| Recorded input, output and selected evidence | Defines what the consumer can legitimately use |
| Context and recursive children | Exposes composition requirements hidden by summary masks |
| Existing module/consumer | Identifies reuse and conflicting implementations |
| Status | Supported, missing capture, missing composition, missing dependency, expensive, or unexamined |
| Required scope and witness | Links implementation to a mandatory proof or a concrete reuse case |

Inspect ACL2's `type-set-rec`, `type-set-recognizer`, `known-whether-nil`,
the IF branch collectors, `find-trivial-equivalence`,
`subst-equiv-and-maybe-delete-lit`, `remove-trivial-equivalences-rec`, and
the associated clause rebuilding calls as needed by those rows. Record
whether evidence observes the executed call or comes from a diagnostic
re-query; do not describe the latter as the former. Capture changes must
preserve proof search, source statements, definitions and hints.

Inventory the existing `TypeSetQuery`, `NodeCore/TypeSetWalk`, `KnownTrue`,
recognizer, linear-substitution, residual-postpass and duplicate consumers.
Distinguish shared semantic lemmas from duplicated orchestration. Do not
start a rewrite simply because a module is large.

**Exit artifacts:** dependency graph with explicit unexplored edges; source
case matrix; proposed module contracts and migration map; bounded list of
work packages and measurement commands. Freeze this supported scope before
implementation. If a mandatory target already needs an excluded mechanism,
report that obstruction before building the new modules.

## R2 — focused probes from real ACL2 runs

Use actual occurrences as primary witnesses. Where they leave an observed
source branch untested, author small ACL2 books and run the real capture and
reconstruction pipeline. Derive variations from the source branch inventory.
Handwritten proof logs, trees or positive proof artifacts are prohibited.

Probe the relevant dimensions without manufacturing a Cartesian test explosion:

| Family | Source-grounded variations to cover |
| --- | --- |
| Query composition | Direct comparison; recognizer applied to comparison; recognizer over nested IF; IF containing recognizers; nesting and repeated terms |
| Query context | Primitive range versus selected lookup; branch-local premises; both result polarities where exercised; recorded pruned branch; cited ordinary theorem evidence |
| Query bookkeeping | Child order and term identity; mask/tuple agreement; supported propagated recognizer information; missing versus explicitly empty evidence |
| Clause substitution | Variable and existing supported compound lhs; either selected equality orientation; retained and deleted literal; earlier/later positions; quote boundaries |
| Clause continuation | Subsequent executable fold; NIL/duplicate removal; multiple edits; changed literal positions; exact residual and selected child |

Not every row is a promise to implement every possible ACL2 case. Label
out-of-scope source branches explicitly. A missing record needed by a
mandatory in-scope case must be fixed in the producer before consumer work
depends on it.

Use focused negative controls on real captures: delete a required child or
selection, change a mask or position, or supply a mismatched endpoint. They
must fail at the relevant consuming boundary. Tests must check meaningful
claims; avoid a large mutation-count target or tests that merely reproduce
the implementation.

Reserve at least one distinct source-backed reuse witness per family, chosen
after the case contract is frozen and before implementation is tailored to
it. Each must exercise meaningful composition, not just renamed variables.
Record a reuse failure honestly; do not silently swap witnesses.

**Exit artifact:** a finite probe matrix with actual capture commands,
provenance, observations, expected refusal boundaries and selected reuse
witnesses. A supported case needs an end-to-end consumer witness as well as
any useful isolated probe.

## R3 — implement shared certifying fragments

### A. Recorded type-query replay

Extend the existing machinery around
[`TypeSetQuery.lean`](../../ACL2Lean/Replay/Driver/TypeSetQuery.lean) and
[`TypeSetWalk.lean`](../../ACL2Lean/Replay/Driver/NodeCore/TypeSetWalk.lean).
Use explicit fragment records for selected routes, child queries and context
references. Parse them strictly. Raw source metadata may remain alongside
the typed view for provenance, but consumers must share one interpretation.

The judgment is conceptually: under a checked context and arbitrary world
and environment, evaluating the recorded term yields a value in the recorded
type set. Its concrete Lean formulation must respect the existing fuel and
value-conversion judgments. The certificate supplies decisions; kernel
proofs establish membership. A mask is never enough on its own.

Implement compositional cases for the frozen fragment. Preserve branch-local
assumptions, recorded child evaluations and cited dependencies. Route both
known-true recognizer queries and existing explicit recognizer/conditional
queries through the shared mechanism. Exercise an existing FC or elimination
consumer through the same judgment, using its real context adapter.

Primitive laws belong in the semantic lemma family. Ordinary rule facts
arrive through the replayed registry with source/world identity and checked
instantiation. Unsupported evidence fails explicitly. Do not add a hypothesis
DP fallback or infer missing IF branch evidence from the term's shape.

### B. Recorded clause-edit replay

Extract the common transition logic from
[`LinearSubstitution.lean`](../../ACL2Lean/Replay/Driver/Waterfall/LinearSubstitution.lean),
[`ResidualPostpass.lean`](../../ACL2Lean/Replay/Driver/Waterfall/ResidualPostpass.lean)
and the existing duplicate-removal path, as demonstrated by R1/R2.

The central contract is a checked implication from the recorded resulting
clause to the original clause, under explicit checked context. Literal
deletion need not preserve equivalence, so an equality-only interface is
insufficient. Keep stronger existing equality/equivalence judgments where
valid and compose them into this implication judgment.

The selected equality remains available inside the proof justifying a
substitution even when ACL2 deletes its clause literal. Check input clause,
position, orientation, relation, permitted replacement positions and exact
result. Replay folds and cleanup in their recorded order. Reset or transport
context facts explicitly across clause boundaries; do not leak an old fact
because two terms happen to print alike.

Integrate both linear-insertion continuation and a real residual-postpass
consumer. Replace their duplicated supported transition logic. Legacy
capture adapters may remain only where the older record contains adequate
evidence; missing evidence must not select an inferred fallback.

### Shared architectural requirements

- Follow L1: fragment-local records and soundness lemmas behind judgment
  interfaces, with no universal closed derivation datatype.
- Follow L2: relation interfaces remain value-level parameters, not an enum
  that closes the architecture to future equivalences. This slice's supported
  substitution case is EQUAL; that does not require implementing others.
- Follow L3: generic lemmas use arbitrary worlds and environments. No book
  constant, theorem name or clause ID selects production behavior.
- Record dependency proofs and declared context assumptions explicitly.
  Kernel acceptance alone does not prove source attribution or replay fidelity.
- Keep new lemma families in their own modules under the repository size norm.
  Retire overlapping supported code in the same slice; do not leave two
  competing interpretations behind an order-sensitive fallback list.
- Profile expensive composition before optimizing. Avoid eagerly constructing
  unrelated context derivations; reuse checked premises with correct context
  identity. Preserve existing resource limits and measure construction separately
  from checking where the tooling permits. No general performance campaign.

Build and replay a real owning theorem at each integration increment. An
isolated soundness lemma is not a reason to postpone wiring the consumer.

## R4 — complete the dependencies and test reuse

1. Replay all six selected arithmetic statements unconditionally through the
   ordinary driver and checked dependency registry. Require exact statement
   and source/world pairing, an empty replay-condition inventory, and axioms
   contained in `{propext, Classical.choice, Quot.sound}`. A successful command
   with a failed or conditional selected row must fail the acceptance check.
2. Preserve the 31 staged prerequisite declarations. Integrate the required
   staging and capture recipe into maintained repository locations. The new
   tests must work without manually compiled `NS1Probe` modules, custom
   scratch-only `LEAN_PATH`, or an undocumented saved ACL2 image.
3. Pass the reserved reuse witnesses through ordinary consumers without
   theorem-specific driver edits. Each family's positive witness must be a
   complete replayed theorem, not only a hand-assembled fragment. If a witness
   exposes a previously unmodeled in-family composition, repair the shared
   case and repeat the original targets. An out-of-family witness records a
   failed reuse test and an incomplete slice, not a replacement selection.
4. Run the whole consuming `<-OF-*-AND-*-SAME-HELPER` with the checked registry
   and unchanged resource limits. Record exact remaining conditions or the
   first unsupported node, plus the inventory of later sites obtained by tree
   inspection. Preserve the existing unconditional subtree receipts.

**The whole helper is a downstream measurement, not a seventh unconditional
acceptance theorem.** If it is blocked by a mechanism outside this slice,
record that boundary and stop expanding downstream. The slice can still
complete when all its mandatory machinery, six proofs, reuse and integration
checks pass. If the helper exposes a failure in a case claimed supported by
this slice, that is a defect to resolve before completion. Apply the same
distinction to timeouts: locate the expensive site and report an external
family obstruction; fix a scalability defect in the delivered fragment.

Do not continue automatically into the quotient, FLOOR/MOD or native transport
campaign after this report. That is the next NS1 planning decision.

## R5 — integration, validation and final assessment

Promote the instrumentation and captures actually required by this slice into
the production path, using the existing tagging/provenance/versioning rules.
Validate affected older consumers, especially the known linear-insertion
interaction with sorting/msort. A diagnostic producer plus successful local
probes is not a completed integration. If promotion exposes an unavoidable
new mechanism outside the frozen scope, report the slice incomplete.

Use focused builds and owning-book replays during implementation. Extend
existing tests and checks instead of adding a separate gate framework. At
slice exit require a fresh full `just claim-gate` with `TRUE_EXIT=0`, retaining
116 unconditional baseline rows and all 21 existing mirrors and their axiom
and seam checks. Explain any legitimate golden movement through the existing
protocol. No new native proposition is claimed, so this slice does not claim
the independent validation reserved for the three NS1 mirrors.

Required final deliverables:

- Source-case matrix, supported-fragment contract and dependency graph with
  explicit unknown edges and exclusions.
- Shared production consumers, generic checked lemmas, maintained captures
  and reproducible tests, with replaced code identified.
- Six unconditional dependency receipts, prerequisite preservation and
  complete reuse-witness receipts.
- Downstream helper result and an updated account of what remains before
  the first mirror; distinguish observed blockers from unexplored proofs.
- Before/after capture, replay and build timings at the measured granularity,
  relevant proof/artifact size and memory observations where available.
- Full regression receipt, source/fork/toolchain identities, unresolved bugs
  and a concise handoff suitable for deciding the next slice.

Keep the evidence in a linked dated execution note rather than appending
every debugging attempt to this plan. Update the live TODO, pattern map and
BUGS index as their state changes. Report completed whole proofs, supported
source cases and removed duplication; commit counts and leaf-test counts
are not progress substitutes.

## Completion and incomplete-stop checklist

**Complete only if all are true:** the two shared fragments are integrated;
all six selected proofs and the reserved reuse proofs are unconditional;
required captures and dependencies are reproducible through maintained
paths; the downstream measurement is recorded; baseline preservation and
the full claim gate pass; the supported scope and remaining NS1 work are
documented. All new proof paths are free of `sorryAx`, `native_decide` and
unapproved axioms. No theorem-specific mathematical shortcut is used.

**Otherwise report incomplete** when a mandatory requirement cannot be met
within the frozen envelope. Include the source and tree address, precise
missing record or judgment, the unmet acceptance items, why the existing
mechanisms cannot cover it, and the smallest additional scope or evidence
needed. Preserve verified local work. Do not weaken a target, broaden the
DP allowance, inflate limits, change ACL2 hints, or silently switch captures
to avoid the recorded operation.

R0–R2 establish finite artifacts and a frozen implementation scope. R3–R5
execute that scope. They are internal checkpoints, not recurring permission
requests. No time or token estimate is asserted before the inventory; record
measured costs at the checkpoints and revise the remaining-work assessment.

## Goal text

The following can be used as the next goal objective without resuming the
larger mirror campaign implicitly:

> Execute NS1-R in the existing `mdd/ns1-bvchop` worktree, following
> `docs/plans/2026-09-07_ns1-replay-mechanisms-plan.md`. Preserve and checkpoint
> the inherited verified WIP. Inventory actual source cases and proof trees,
> run focused real-ACL2 probes, and freeze a bounded supported scope before
> consolidating recorded type-query replay and clause-edit replay into shared,
> world-parametric, kernel-checked fragments. Deliver unconditional replay of
> the six named product/cancellation dependencies, preserve their 31 staged
> prerequisites, pass complete reuse proofs selected after the scope is frozen,
> integrate required captures and production consumers, and record a measured
> whole-helper replay with exact remaining NS1 blockers. Finish with a fresh
> full claim gate preserving the 116 unconditional baseline rows and 21 existing
> mirrors, plus the supported-scope and reproducibility records. Stop incomplete
> with the exact obstruction if a mandatory requirement needs a mechanism
> outside the frozen scope, unavailable evidence, or a new semantic/trust/fidelity
> ruling; do not widen this slice by chasing subsequent quotient or mirror
> frontiers. Do not merge, push, publish, change native specifications, introduce
> theorem-specific shortcuts, or launch additional subagent tasks. Completion
> of NS1-R does not complete NS1 or require a new native mirror.
