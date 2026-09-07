# NS1-R supported scope and probe contract

Dated 2026-09-07. **Implementation scope frozen at R1.** This is a bounded
implementation contract, not a claim that the listed cases already replay.
The [execution record](2026-09-07_ns1-r-execution.md) holds observations and
receipts; the [slice plan](../plans/2026-09-07_ns1-replay-mechanisms-plan.md)
defines mandatory acceptance. No production replay code was changed before
this freeze. R2 must expose the missing records before their consumers land.

## Evidence and dependency boundary

The inventory traverses complete reconstructed trees for the six required
product/cancellation statements, their consuming helper, four additional
equality dependencies, both Boolean-book proofs, and the selected bootstrap
recognizer theorem. Addresses below use the theorem, clause ID, processor,
and item path from `scripts/replay-mechanism-inventory.lean`; full paths and
provenance are in the corresponding JSONL receipts. These are actual tree
occurrences, not generated positive test nodes.

The six targets have 88 clause nodes and 607 rewrite-detail nodes. Their
fourteen known-true Boolean recognizer queries include five conditional
arguments. The source capture omits their recursive argument evidence.
CANCEL has six selected deletions; CANCEL-GEN has three deletions and five
retentions. The additional ordinary dependency graph and observed failures
are recorded in the execution note. The preserved 31 declarations are the
already checked component/negation staging chain; they are not an exhaustive
count of the proof closure.

`BOOLEANP-COMPOUND-RECOGNIZER` is an ordinary bootstrap `defthm`. Its original
initialization tree now replays unconditionally at the quotient consumer
world, with explicit `{propext, Classical.choice, Quot.sound}` receipts.
It must enter through that replay. POSITIVE and the existing primitive
arithmetic USE schemas remain checked model laws for actual ACL2 axioms.

Higher NS1 edges remain measurement boundaries: BVCHOP bound needs MOD
totality/type and arithmetic dependencies; the selected MOD route needs
FLOOR/nonnegative integer quotient; the quotient bound consumes the strict
product helper. The existing captures expose portions of those proofs, but
their complete closure is not established here. No new capture census of
all included books or automatic continuation into those proofs is authorized
by this freeze.

## Source cases and permitted work

Source locations refer to the preserved diagnostic producer `df7a28e38c`.
Later observational instrumentation may move line numbers. Each row defines
a mechanism; theorem names identify witnesses and never select behavior.

| Case | Source and actual occurrence | Input / output and required evidence | Existing owner; disposition |
| --- | --- | --- | --- |
| Q1: primitive range and selected lookup | `type-set-rec`, `type-set-b.lisp:8150–8210`; explicit numeric queries in the staged component proofs | Recorded term, result, candidate lookup, selected route, executed children and ttrees; a selected entry is checked against the actual context and independently proved | `TypeSetQuery`, `TypeSetWalk`, `TsFacts`; consolidate existing supported cells and range/lookup adapters |
| Q2: recognizer application | `type-set-recognizer:3226`, consumed tuple at `type-set-rec:8393`; sign targets and CANCEL-GEN's known-true nodes | Argument membership followed by the recorded tuple's true/false intersections; preserve strongness, polarity, rune and propagated tuple | `KnownTrue`, `Recognizer`, `TypeSetWalk`; recursive evidence missing in known-true capture; replay ordinary recognizer source before applying its tuple |
| Q3: conditional query | IF arm of `type-set-rec:8433`; five Boolean recognizer arguments in the six trees | Observe `assume-true-false-rec` outcome, decision queries, true/false contexts, executed branch queries and mask union/intersection. A branch premise is local to its branch. A pruned branch requires checked decision/contradiction evidence | Current recursive-query observer lacks branch scope labels; old root-IF collector is a diagnostic re-query. Add observation of executed calls and share one consumer judgment |
| Q4: Boolean premise at a rewrite join | `if1/boolean`; EQUAL-OF-BOOLEANS-CHEAP, Goal', simplify, item 2/1/0/node 0 | `(IF Y 'T 'NIL) → Y` under the recorded false clause literal `(NOT (BOOLEANP Y))`; the context adapter must derive membership from its checked premise | `Ctx.boolDisj?`, `Node`, `TypeSetWalk`; missing shared context conversion, not permission to infer a type from a name |
| Q5: existing FC/ELIM query adapter | `relieve-hyps` FC records and `type-restriction-segment`; existing component/helper query captures | Actual context/source selection and successful reliefs feed the same membership judgment; context snapshots supply no assumptions | `ForwardChain/Context`, `ElimRestrictions`, `LinearNumeric`, `LinearEquation`; preserve supported routes and exercise at least one actual FC or ELIM consumer |
| E1: selected EQUAL substitution | `find-trivial-equivalence1:6398`, `remove-trivial-equivalences-rec:6737`; CANCEL Subgoal 2.9/2.8 simplify item 2; CANCEL-GEN retained/deleted selections | Exact input clause, zero-based selected position/literal, equality orientation, replacement and deletion choice. Selected literal supplies equality inside a proof by contradiction, including when deleted | `LinearSubstitution`, `ResidualPostpass`; consolidate into child-clause-to-parent-clause implication |
| E2: literal construction and folds | `subst-equiv-and-maybe-delete-lit:6679`, `subst-equiv-expr` and scons construction; inverse-product Goal' residual continuation | Record which literal/term is being built, local substitutions and executable folds in execution order, then exact resulting literal. A fold may affect a temporary term later discarded | Both existing postpasses globally replace and reject no-effect folds; add construction evidence, never accept an unmatched step as a successful no-op |
| E3: cleanup and successive edits | `add-literal-and-pt` called while rebuilding clause tails; CANCEL-GEN Goal''; EQUAL-DENOMINATOR-1 existing residual route | Recorded NIL/duplicate removal, preserving ACL2's surviving occurrence and exact next input; compose multiple edits and the actual continuation child | `SubstitutionDuplicates`, both postpasses; extract common supported transition logic and retain exact endpoint checks |
| I1: recorded IF rewrite-window composition | `fncall/non-recursive` followed by `if-finish/combined`; EQUAL-OF-*-AND-*-CANCEL-ARG2-ARG2, Goal', simplify item 1/node 0/node 1 | The RHS window records FIX X's expansion. The OR-copy bridge must consume that exact selected prefix in its correct relative path, with source and final endpoints checked | `NodeCore/Rewrites`; repair routing of existing recorded rewrite evidence. No new rewrite rule, inferred expansion or arbitrary prefix acceptance |
| I2: existing verdict leaf normalization | EQUAL-OF-*-AND-*-CANCEL's emitted leaf after zero substitution; full obligation in `r1-dependencies-replay.log` | Primitive zero multiplication and Boolean completion inside the exact emitted DP obligation; decomposition must use existing numeric semantics and the same decision-procedure allowance | `Discharge`, primitive numeric views; bounded integration prerequisite. No handwritten cancellation theorem, new arithmetic solver or limit increase |

Q3 includes the source's four decision outcomes (both branches, true only,
false only, contradictory context) **only with replayable decision evidence**.
An unobserved or unsupported route is refused. Capturing a Boolean flag alone
does not add a proof rule. Lookup/computation intersections use recorded
operands and checked membership/subset proofs; a new backchaining or forcing
derivation is outside scope. The same applies to a new ordinary recognizer
whose source proof requires an excluded mechanism.

E1 supports EQUAL and quote-opaque replacement through positions justified
by the existing equality congruence machinery. It does not claim arbitrary
equivalence-hittable replacement, substitution under unsupported lambda
binding, or user congruences as a new feature. Source-selected compound lhs
cases already supported remain supported. A source hit that cannot be
represented by the existing relation/conversion interface is an explicit
frontier, not a license to replace every printed occurrence.

I1 and I2 are named integration obligations, not additional open-ended
families. If inspecting either reveals an unrecorded inference or a new
semantic/arithmetic rule, report the six-proof acceptance obstruction and
stop incomplete. Their inclusion does not authorize repairing subsequent
quotient or native-transport failures.

## Judgment and module contracts

The query judgment is membership of the evaluated term in the recorded type
set, under an arbitrary world, environment and checked context. Keep the
evaluation/conversion proof alongside membership; do not substitute an
unconnected primitive value expression. A strict fragment-local capture
view records route, children, scoped branch transitions, lookup selection,
tuple and citations. The proof builder follows that view, using local
semantic composition lemmas. It neither searches for another route nor
reconstructs a missing branch record from syntax.

Primitive range, subset, union and Boolean conversions live in a query lemma
family. Ordinary recognizer/TP rules arrive via the existing checked registry,
with their source/world pairing and instantiation. Context adapters select
checked facts and transport them to the judgment. Known-true and explicit
recognizer/IF consumers share this interface; the existing FC/ELIM adapter
must pass through it as well. Retire overlapping supported interpretation
code in the same slice. An adequate legacy capture can have a strict adapter;
inadequate old evidence must fail rather than select inference.

The clause judgment is `EvTrue w env child → EvTrue w env parent`, possibly
under explicit checked context. A fragment-local edit record holds selected
input/position/orientation, per-literal construction records, cleanup and
result. An EQUAL conversion can transport a literal; deletion uses clause
implication. The selected equality remains available only within the
justifying local proof. A continuation sees reset or explicitly transported
facts, never stale positional facts from the old clause.

Build a common edit interpreter and soundness/composition lemmas, then route
linear insertion and residual postpass through it. Keep rewrite relation
interfaces abstract at value level (L2); EQUAL is this fragment's supported
instance. Every lemma is world-parametric (L3). These are two local fragments
behind judgments, not one universal derivation datatype (L1).

## Finite implementation packages

1. **Executed query capture and strict schema.** Extend the existing observer
   to known-true calls and scoped IF branches without changing search, source
   statements or hints. Compare old/new theorem and structural projections.
   Preserve raw captures, manifests and image identities.
2. **Shared query judgment and consumers.** Implement Q1–Q4, replay the named
   bootstrap dependency, and connect Q5. Use one actual owning proof at each
   integration increment; include required negative controls at consumption.
3. **Recorded edit construction and common continuation.** Capture E1–E3's
   actual construction scope; implement the implication contract and replace
   duplicated postpass orchestration. Exercise deletion and residual folds.
4. **Dependency integration.** Resolve I1/I2 only under the bounds above,
   close the six whole proofs plus their inspected ordinary dependencies,
   preserve the 31 prerequisites and run the reserved reuse proofs.
5. **Production and exit.** Promote required captures/producers, maintain
   staging without scratch imports, check sorting/msort interaction, measure
   the whole strict helper, and run a fresh full claim gate preserving the
   116 unconditional baseline rows and 21 mirrors.

These packages are finite by source cases, not an estimate in days. No package
passes because isolated leaves check. In-family failures require repair;
new mechanisms require the plan's incomplete-stop report. The whole helper
remains a downstream measurement, not a seventh unconditional target.

## R2 probe selection and refusal checks

Witnesses are selected **after the freeze above and before consumer
implementation**:

| Role | Reserved actual whole theorem | Why it is a different composition |
| --- | --- | --- |
| Query reuse | `EQUAL-/` from arithmetic-3 basic-arithmetic-helper, existing `acl2_samples/ns1/basic-arithmetic-helper.proof-log` and its unchanged source | Root conditional hypothesis relief composed with reciprocal/type context and ordinary dependencies, rather than Boolean recognition of a product comparison |
| Edit reuse | `EQUAL-DENOMINATOR-1` from arithmetic-3 numerator-and-denominator, existing `acl2_samples/ns1/numerator-and-denominator.proof-log` and its unchanged source | Residual clause rebuilding and folds in a numerator/denominator proof, rather than a linear-insertion product cancellation continuation |

Keep these selections if they fail; do not replace them with easier witnesses.
Recapturing the unchanged source to obtain newly required evidence is allowed,
with an explicit comparison and provenance record. Existing unconditional
tests identify the baseline, but fresh complete replay through the migrated
consumer is required for acceptance. The mandatory sign/CANCEL-GEN queries
and CANCEL deletion cover the new paths; reuse does not replace those tests.

Use source-backed small books only for observed source axes absent from
these captures: nested/repeated IF queries, both polarities and branch pruning;
earlier/later selection, both orientations, retained/deleted literals and
successive cleanup. Reconstruct every real capture before deciding what it
witnesses. If ACL2 chooses another route, report that observation and adjust
the source probe from the source case, without changing mandatory book hints.

Negative controls mutate copies of real captures at the consuming boundary:
missing query child/decision, wrong mask/tuple/context selection, wrong
substitution position/orientation or endpoint, and removed construction/fold.
They must fail where that record is consumed. No synthetic positive records
or arbitrary mutation-count target.

Measurement commands follow the R0/R1 recipes in the execution note. Capture
time, replay construction/checking time where available, artifact sizes and
default-budget failures separately. The final owning tests must fail on any
conditional or failed selected row; the observational R1 scripts are not
acceptance gates.
