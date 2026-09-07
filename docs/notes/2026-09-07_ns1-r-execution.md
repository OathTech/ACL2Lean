# NS1-R execution record

Dated 2026-09-07. Implements the
[focused plan](../plans/2026-09-07_ns1-replay-mechanisms-plan.md).
**In progress: R0 checkpointed at `435a26f`; R1 scope frozen; R2 probes next.**
The [supported scope](2026-09-07_ns1-r-supported-scope.md) records the cases,
module contracts, integration bounds and subsequently selected reuse witnesses.
Neither production replay fragment has been changed by this slice.

## Baseline and preservation

The goal was activated with the objective in the user's attached text.
The preceding interrupted activation made no implementation progress;
process inspection found no surviving ACL2Lean build or capture to resume.
Work continues in `mdd/ns1-bvchop`. The planning documents are checkpointed
at `7369381`, following implementation HEAD `7598d0a`.

The inherited diff is limited to `NumericComponents.lean`,
`Replay/Driver/ComplexViews.lean`, and `Replay/Driver/Discharge.lean`.
It adds primitive component/negation normalization inside actual emitted
verdict leaves. It does not add an ordinary theorem to the core registry.
The source inspection and a copy of this exact patch precede new replay
implementation; its separate fast-gate checkpoint is `435a26f`.

[The R0 manifest](2026-09-07_ns1-r-baseline.json) records 22 source/capture/image identities,
the inherited patch hash, Lean 4.33.0, production ACL2
`fd27e59021cf7d0103a526dbda41553ad709eae3`, and diagnostic ACL2
`df7a28e38c5122d987fc0bc3c19a0db3895105b6`. The diagnostic checkout is clean.
All 55 source hashes in the selected bootstrap capture's diagnostic manifest
match that checkout. Its saved image matches the earlier successful build
record and the times capture's image timestamp. The captured image core is
241,948,208 bytes, SHA-256
`5c28de5c83d5b42d4f225cf698fd17f13df7dfbe502678c4ca5b64841a168f2f`.
These are engineering provenance checks, not a kernel guarantee of attribution.
Available disk at entry: 1.1 TiB; no cleanup was needed.

Fresh R0 commands, from the NS1 worktree:

```sh
lake env bash -c 'export LEAN_PATH="$PWD/.tmp/ns1:$LEAN_PATH"; exec lean -o .tmp/ns1/NS1Probe/Components.olean .tmp/ns1/NS1Probe/Components.lean'
lake env bash -c 'export LEAN_PATH="$PWD/.tmp/ns1:$LEAN_PATH"; exec lean -o .tmp/ns1/NS1Probe/Negations.olean .tmp/ns1/NS1Probe/Negations.lean'
lake env bash -c 'export LEAN_PATH="$PWD/.tmp/ns1:$LEAN_PATH"; exec lean .tmp/ns1/probe-strict-arithmetic-dependencies.lean'
```

The first two commands exit zero, replaying **24 + 7 declarations
unconditionally**. Component staging enforces the accepted axiom set; all
seven negation axiom receipts were also inspected and accepted. Sources and
captures are unchanged. Receipts: `r0-components.log` and `r0-negations.log`
under `.tmp/ns1-r/`. IMAGPART-OF-- takes 3747 ms and REALPART-OF-- 3555 ms
in the reported replay interval, excluding module loading.

The third command reproduces four failed targets and two conditional
corollaries in `r0-six-dependencies.log`. It is an observational probe whose
process can succeed despite failed rows; it is **not** the final acceptance
test. Its first failures remain the Boolean hypothesis queries and recorded
literal deletion. The final six-theorem test must enforce unconditionality.

R0's fresh static recipes pass in `r0-static.log`; the affected build passes
3167 jobs in `r0-affected-build.log` (existing build artifacts reused where
valid), and focused equality-reasoning replay checks 3/3 unconditionally with
two checked DP leaves in `r0-equality-replay.log`. All receipts are under
`.tmp/ns1-r/`.

The last full gate remains
`.gate-runs/a38c7f5-20260907T095722Z.log` (`TRUE_EXIT=0`), preserving 116
unconditional rows and 21 mirrors. R0 is not a new full-gate claim.

## R1: inspection beyond the first failure

[`scripts/replay-mechanism-inventory.lean`](../../scripts/replay-mechanism-inventory.lean)
traverses all constructors in reconstructed clause/item/node trees and emits
JSONL with theorem, structural address, processor input, branch segments,
rune/USE evidence and query/edit records. It does not attempt replay, turn
recorded contexts into assumed facts, or classify an occurrence as supported.
An initial formatting error in the script was corrected before the successful
run; the first run is not an inventory receipt.

```sh
lake env lean --run scripts/replay-mechanism-inventory.lean \
  .tmp/ns1/c2-clausify-reductions-times-capture/times.proof-log \
  .tmp/ns1-r/r1-times-trees.jsonl \
  '<-OF-*-AND-0' '<-OF-0-AND-*' '<-OF-*-AND-*-CANCEL' \
  '<-OF-*-AND-*-CANCEL-GEN' '<-OF-*-AND-*-CANCEL-ARG1-AND-ARG2' \
  '<-OF-*-AND-*-CANCEL-ARG2-AND-ARG1' '<-OF-*-AND-*-SAME-HELPER'
```

The first successful version emitted 6180 records, 9,601,887 bytes
(`r1-inventory-rerun.log`). A subsequent version retains full provenance for
every node, including rewrite paths needed to inspect IF joins; its successful
receipt is `.tmp/ns1-r/r1-inventory-full-provenance.log`. The six targets contain 88 clause nodes
and 607 rewrite-detail nodes; the downstream helper contains 94 clauses and
3095 rewrite-detail nodes. Counts describe this capture, not acceptance quotas.

| Target | Clauses | Rewrite-detail nodes | Known-true recognizer queries | Queries with IF argument | Substitutions: delete / retain |
| --- | ---: | ---: | ---: | ---: | ---: |
| `<-OF-*-AND-0` | 13 | 29 | 2 | 1 | 0 / 0 |
| `<-OF-0-AND-*` | 12 | 30 | 2 | 1 | 0 / 0 |
| `<-OF-*-AND-*-CANCEL` | 29 | 298 | 0 | 0 | 6 / 0 |
| `<-OF-*-AND-*-CANCEL-GEN` | 28 | 196 | 10 | 3 | 3 / 5 |
| `<-OF-*-AND-*-CANCEL-ARG1-AND-ARG2` | 3 | 27 | 0 | 0 | 0 / 0 |
| `<-OF-*-AND-*-CANCEL-ARG2-AND-ARG1` | 3 | 27 | 0 | 0 | 0 / 0 |

All fourteen known-true recognizer records are BOOLEANP with argument/true
masks 384/384 and false mask -385; all carry zero argument leaves. Thus the
nested-conditional gap is visible without first repairing the direct case.

The six trees use only apply-top-hints, preprocess and simplify processors
in this capture. That is not a proof that every nested rewrite/DP obligation
is supported. In particular, CANCEL-GEN has two uses of the ordinary theorem
`EQUAL-OF-*-AND-*-CANCEL-ARG2-ARG2`, at Subgoal 9.2' and Subgoal 5'. That
dependency was hidden behind its first Boolean failure. The separate
`EQUAL-OF-BOOLEANS-CHEAP` book proof is also required. Their complete proof
closure must be inspected before the family scope is frozen.

## Source cases under investigation

Source locations below refer to diagnostic ACL2 `df7a28e38c`, not necessarily
the production checkout's line numbers.

| Source branch | Observation | Design consequence / remaining work |
| --- | --- | --- |
| `type-set-b.lisp:3226`, `type-set-recognizer` | Computes Boolean result by intersections with the enabled tuple's true/false masks and retains its rune | Separate checked argument membership, tuple justification and mask conversion; do not assume a tuple establishes its own theorem |
| `type-set-b.lisp:8120`, `type-set-rec` query observer | Already records executed recursive calls and selected lookup/comparison/recognizer metadata when dynamically enabled | Reuse this observer for hypothesis consumers where possible; first inspect its IF and context coverage |
| `type-set-b.lisp:8393`, recognizer argument | Captures the actual consumed argument mask and tuple | Outer summaries alone do not provide the argument's branch derivations |
| `type-set-b.lisp:12819`, `known-whether-nil` | Publishes root recognizer/comparison summaries; root IF uses a separate collector | Inspect and consolidate the two evidence routes before changing the consumer |
| `type-set-b.lisp:12021`, `tp-collect-if-leaves1` | Diagnostic re-query of branches using `assume-true-false-rec` and `type-set` | It is not an observation of the original query's executed children; retain that distinction in the capture design |
| `simplify.lisp:6679`, `subst-equiv-and-maybe-delete-lit` | Skips the selected literal while substituting elsewhere; deletes or retains it; rebuilds through add-literal | Shared clause transition needs implication and exact ordered cleanup, not only equality transport |
| `simplify.lisp:6737`, `remove-trivial-equivalences-rec` | Repeats selected edits; records selected input, position, equality and deletion flag | Inventory all successive edits and child endpoints; do not select a different capture to avoid deletion |

The source's actual IF query branch is `type-set-b.lisp:8433`: it calls
`assume-true-false-rec`, then either uses the true branch, uses the false
branch, unions both returned masks, or reports an empty type for contradictory
context. `type-set-finish` can then intersect with prior lookup information.
These cases must be distinguished in the evidence; positional child terms
alone do not describe the branch contexts or the pruned branch's justification.

## Additional dependency probes and downstream baseline

The unchanged `equal-of-booleans.lisp` was captured afresh with the preserved
diagnostic image: 2/2 QEDs, 600 lines, full source. Capture and sidecar are in
`.tmp/ns1-r/equal-booleans-capture/`; receipt is `r1-equal-booleans-capture.log`.
This diagnostic used the existing capture worker mode because it writes a
new scratch file that no compiled include-string consumer references; it does
not recapture or change an existing embedded input. Production promotion must
still invalidate affected consumers under the normal protocol.

The tree inventory now also covers both Boolean-book proofs and four ordinary
equality-cancellation dependencies from the existing times capture. Their
full-provenance outputs are `r1-equal-booleans-trees.jsonl` and
`r1-equality-dependency-trees.jsonl`, with matching `*-full-provenance.log`
command receipts under `.tmp/ns1-r/`.

The actual dependency graph contains these additional edges:

```mermaid
flowchart TD
  signs[Two product-sign targets] --> bools[EQUAL-OF-BOOLEANS-CHEAP]
  gen[CANCEL-GEN target] --> bools
  gen --> cancel[CANCEL target]
  gen --> eqright[EQUAL-OF-*-AND-*-CANCEL-ARG2-ARG2]
  cor[Two mixed-argument targets] --> gen
  cor --> cancel
  eqright --> eqbase[EQUAL-OF-*-AND-*-CANCEL]
  eqright --> both["*-BOTH-SIDES"]
  eqbase --> both
  eqright --> inverse["*-OF-/-SAME-ARG2"]
  eqbase --> inverse
```

This is the newly inspected ordinary-rule subgraph, not the complete list of
primitive, type, totality or bootstrap obligations. The Boolean recognizer's
named bootstrap theorem is itself an ordinary `defthm` at `axioms.lisp:2269`;
its original initialization proof was captured and replayed separately (receipt below). POSITIVE,
used by CANCEL, is an actual primitive axiom at `axioms.lisp:4340` with an
existing checked model schema.

`.tmp/ns1-r/probe-dependencies.lean` uses the existing staged driver against
the five additional ordinary dependency trees. Its completed observational
run is `r1-dependencies-replay.log`:

| Dependency | Actual result | Scope assessment still required |
| --- | --- | --- |
| `*-BOTH-SIDES` | Unconditional, accepted axioms; 790 ms | Existing machinery suffices |
| `*-OF-/-SAME-ARG2` | Residual executable fold changes no surviving literal at Goal' | Shared edit machinery must account for recorded temporary construction/folds; do not simply accept every ineffective step |
| `EQUAL-OF-*-AND-*-CANCEL` | Recorded DP leaf fails after zero substitution; 42,516 ms | Inspect primitive completion and the exact leaf before assuming the new query/edit modules will solve it |
| `EQUAL-OF-*-AND-*-CANCEL-ARG2-ARG2` | IF OR-copy reconstruction ends at FIX while the recorded test has FIX's expanded body | Trace the recorded rewrite paths and classify this existing composition defect before freezing scope |
| `EQUAL-OF-BOOLEANS-CHEAP` | IF Boolean collapse cannot obtain Y's two-valuedness | The actual branch contains `(NOT (BOOLEANP Y))` as a false literal; shared checked-context membership must expose that premise |

The no-effect folds are repeated recorded `(UNARY-/ '0) → '0` calls and
`(BINARY-* '0 '0) → '0`, within the original substitution continuation.
The IF-copy mismatch has an actual `FIX X` expansion preceding the combined
node; the current bridge excludes window-tagged prefix nodes when selecting
the test proof. This is an identified consumer boundary, not yet a verified
repair or authorization to ignore the endpoint check.

The baseline whole helper also ran with all 31 checked stage declarations:

```sh
lake env bash -c 'export LEAN_PATH="$PWD/.tmp/ns1:$LEAN_PATH"; exec lean .tmp/ns1-r/probe-helper.lean'
```

`r0-helper-replay.log` reports a failure after **178,789 ms** at Subgoal 2':
literal item 6 is quoted T, while the next clause literal is
`(< (BINARY-* X1 Y) (BINARY-* X2 Y))`. It did not hit the earlier heartbeat
timeout in this run. This is an actual remaining composition boundary; no
complete helper or conditional whole-helper proof is claimed.

The original initialization capture for BOOLEANP-COMPOUND-RECOGNIZER completed
with `initialize-acl2 nil`, unchanged original theorem arguments/hints, a clean
producer, and an explicit completed observation window. Raw stdout and its
Latin-1-to-UTF-8 transcription are retained separately under
`.tmp/ns1-r/bootstrap-boolean-capture/`, with 55 source hashes and driver/script
identities in `diagnostic.json`. Decompressed UTF-8 SHA-256:
`ec7d3cdc46b27852f4d36d2dce17bff8d26fd2a8191bcbcfd7395747a6732045`.
The inventory reconstructs one clause. The CLI checks 1/1 unconditionally
(429 ms reported theorem replay), without a DP leaf. A second probe at the
quotient consumer world enforces an empty condition inventory and accepted
axioms, then runs `#print axioms R1Bootstrap.booleanRecognizer`. Both succeed:

```sh
lake env lean .tmp/ns1-r/probe-bootstrap-boolean.lean
```

Receipt: `r1-bootstrap-boolean-consumer-world.log`. This is a complete ordinary
bootstrap replay, not a handwritten registration of its corollary.

R1 now freezes the source-case and integration envelope in the supported-scope
note. No inspected mandatory dependency has yet demonstrated a need for an
excluded mechanism. That assessment is bounded: the IF window mismatch may
only be repaired by correctly routing its already recorded rewrite, and the
zero-product verdict may only use existing primitive semantics inside that
emitted leaf. An unrecorded inference or new arithmetic mechanism would be
an incomplete-stop finding. No new semantic lemma or replay dispatch case has
been added under NS1-R yet. The next package is R2's executed-query capture
and real-source probes; the missing recursive/branch evidence remains open.

The R1 inventory/scope checkpoint passes a fresh fast gate: static recipes in
`r1-static.log`, affected build (3167 jobs) in `r1-affected-build.log`, and
3/3 unconditional equality-reasoning replay in `r1-equality-replay.log`.
The inventory script compiled and traversed the source trees as recorded
above. This checkpoint changes the inspection tool and records; it makes no
new production replay or full-gate claim.
