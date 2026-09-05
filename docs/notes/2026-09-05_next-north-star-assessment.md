# After sorting: making ACL2Lean useful beyond its demonstration corpus

Assessment dated 2026-09-05. Baseline: ACL2Lean `06ccb8e` (`v0.1.0`),
instrumented ACL2 `e8d78e513d6867d04002f0df644da1723cc96e89`, Lean 4.33.0.
This is a recommendation for a successor arc, **not a replacement governing
plan or a claim that a new book replays**. The [master plan](../plans/2026-08-12_master-plan.md),
[lexicon](../LEXICON.md), and [working rules](../../CLAUDE.md) still govern.

## Recommendation

Combine the two approaches: **choose a useful book family, then broaden the
machinery only where its actual proofs and mirror definitions require it**.
Keep sorting as a regression corpus, and add an unfamiliar book as the test
that the improvement generalizes. An unrestricted cleanup of the existing
machinery would lack a product test; committing immediately to all of x86isa
would put too many unmeasured prerequisites before the next useful result.

My recommended next target is **a small, explicitly selected Kestrel bitvector
library**, starting with `kestrel/bv/bvchop.lisp`, then `bvplus.lisp`, with
`bvcat.lisp` as the next test of reuse. The intended users are Lean developers
reasoning about machine words and software: they should obtain reusable word
operations and their laws from ACL2, through a documented import workflow.
The value is the repeatable import capability and access to a larger library;
a handful of arithmetic identities alone would not establish usefulness.

Use **`x86-popcount-32-correct` in `projects/x86isa/proofs/popcount/popcount.lisp`**
as the longer-term target. It is a concrete program-correctness theorem with a
clear result and explicit machine setup. “Replay the x86 model” needs this
kind of boundary: importing definitions, replaying library lemmas, and proving
a machine-code program correct are different milestones.

The first commitment should be a bounded feasibility arc, not a promise to
finish either library. A fresh `bvchop` capture succeeded during this
investigation, but parsing it immediately exposed an existing semantic gap:
an included arithmetic theorem contains a complex number. Resolve that scope
before committing to the full bitvector arc. If its prerequisite cost proves
disproportionate, the fallback is `misc/records.lisp`, with typed finite-record
read/write laws as its product. M1 is a reasonable intermediate machine-model
exercise if program semantics becomes the priority, but is not essential to
the bitvector-to-x86 route.

## What the release demonstrates, and what I measured

The committed [coverage golden](../../Tests/driver-coverage.golden) records
116/116 theorem rows replayed unconditionally. The product files contain 21
`mirror_transport%` declarations: six Basics and fifteen Sorting products.
These are different inventories. The golden also contains termination rows
and informational DP probes; neither should inflate the theorem count.
The sorting products are instance mirrors, not proofs of every polymorphic
schema in the spec file. See the [technical overview](../OVERVIEW.md).

I built the focused executable with `lake build acl2lean-replay` successfully
and used it to inspect actual reconstructed trees and run the probes below.
The existing-pattern probes use the checkout's captured logs; only `bvchop`
and the attempted `records` capture were freshly run through ACL2 here.
I did **not** rerun the full claim gate, the full coverage sweep, mirror axiom
receipts, or independent product validation. The release-wide counts above
are inspected artifacts, not a fresh certification of the release.

| Probe | Observed result | What it establishes |
| --- | --- | --- |
| `simple` | 1/1 unconditional; reconstructed tree inspected | The focused development loop works in this checkout. |
| `recon-tests/07-mutual-recursion` | 2/2 unconditional; `termination:MY-EVENP` also replayed | “Mutual recursion is unsupported” is too broad. These ground applications and this admission replay; that does not establish arbitrary mutual induction or generated mutual mirrors. |
| `pattern-tests/cov-force-round` | Parser rejects `FORCING ROUND (round 1)` | Forcing-round support is still a live gap. |
| `pattern-tests/cov-verify-guards` | Parser rejects a `VERIFY-GUARDS` proof for `GSUM` | Guard obligations can block ingestion before the theorem of interest. |
| `pattern-tests/cov-mv-let` | Reconstruction succeeds; replay 0/1 | First replay failure is an unexpected residual `LAMBDA-BODY` boundary in preprocessing. The older “MV-NTH DP lift” diagnosis is not the first frontier now. |
| `pattern-tests/cov-meta-rule` | Reconstruction succeeds; 5/16 conditional, 0 unconditional | Failures include evaluator/`RETURN-LAST` lifting, recognizer handling, and a `UNICITY-OF-0` shape. This is not evidence that general metafunction replay works. |
| `pattern-tests/cov-clause-processor` | Reconstruction succeeds; 6/16 replayed, only 1 unconditional | The unconditional `USE-ID-CP` tree closes through `CAR-CONS` preprocessing after an unchanged hint step. It does not demonstrate a substantive clause-processor transformation. |
| Fresh `kestrel/bv/bvchop.lisp` | Capture accepted: 116 QED / 116 `:SOURCE :LOCAL` theorem events; 436,037 lines, 20,856,860 bytes. Dump fails at `unrecognized reader macro: #C`. | A successful ACL2 capture is not a successful parse, reconstruction, replay, or mirror. Included theorem statements without proof trees are not counted in those 116. |
| Fresh `misc/records.lisp` | Capture refused; zero theorem proofs captured | `total-order` includes `xdoc/top`, whose `XDOC` package is unknown in this image. A normal ACL2 run confirms the missing package setup and uncertified-book warning. This is an environment/certification blocker, not measured replay difficulty. |

The `bvchop` log contains `#C(0 1)` in the included theorem
`EQUAL-OF-+-OF-*-OF-I` and its stored rule, at lines 947 and 949 in this capture.
It reaches the existing [BUG-009](../BUGS.md#bug-009--no-complex-rational-class-numberslexorder)
before any bitvector proof tree is available. Integer-only target statements
do not imply an integer-only dependency environment. No log was edited or
filtered to get past this failure.

Two practical measurement cautions emerged. The focused CLI can exit zero
while printing failed or conditional rows; a tool-facing success result must
inspect theorem status, not just process status. Its reported replay time
also excludes module loading. In the final simple run, the reported replay
portion was 1,042 ms; this is a single warm measurement, not an end-to-end
latency promise.

## Bottom-up assessment of the machinery

There is a reusable architecture worth extending: world-parametric judgments,
record-directed clause-tree replay, explicit frontiers, a shared measure
classification, generated execution/simulation kits, and a kernel-checked
transport path into Lean mirrors. The highest-return work is closing gaps
between these layers, not replacing the architecture.

| Area and current evidence | Consequence beyond sorting | Recommended change, driven by a real consumer |
| --- | --- | --- |
| **Primitive support is different at each layer.** [`EvalOpt.callBuiltin`](../../ACL2Lean/EvalOpt.lean) has 54 named match arms, while [`ExecGen.builtinTwins`](../../ACL2Lean/Imported/ExecGen.lean) has seven entries: `CONSP`, `EQUAL`, `CAR`, `CDR`, `CONS`, `LEXORDER`, `BINARY-+`. DP lifting has another registry in [`DpLift`](../../ACL2Lean/Replay/DpLift.lean). | An evaluator-supported arithmetic function need not have a generated execution correspondence or a mirror route. A green replay can leave substantial hand work. | Make each added operation a complete family: semantics and differential cases, replay/lift lemmas, execution correspondence, and native refinement where demanded. Share registration metadata for these existing consumers, while keeping their distinct proof obligations. Do not make every ACL2 library function a trusted-core primitive. |
| **Execution correspondence has a small arity ceiling.** `ExecGen.mkConvDefn` handles only 1–3 arguments. `MeasureTable` is shared, but its header records that ExecGen still transcribes the positional measure declaration. | `bvcat` already has four arguments; x86 instruction functions routinely have more. Existing measure support in replay does not automatically reach execution generation. | Derive argument environments and measure positions from emitted declarations. Replace the arity ladder with a list-indexed application/correspondence lemma when the first four-argument target reaches it. Extend measure routes from recorded admissions, not a growing list of example names. |
| **Some replay route selection still names sorting helpers.** [`destructorChainOk`](../../ACL2Lean/Replay/Driver/NodeCore/Ctx.lean) explicitly recognizes `EVENS` and `ODDS` alongside `CAR`/`CDR`; it is documented as an expiry-held heuristic. | Renaming or changing a helper can change the route selected even when its proof shape is analogous. This is a concrete specialization, not merely a module named “Sorting.” | At the next affected tree, consume a recorded route/decrease justification and retire the special case. Do not add the new book's helper name to this predicate. Keep the change constrained to the route it serves. |
| **The transfer kit's data shapes remain list-oriented.** [`SimGen.SimVarKind`](../../ACL2Lean/Imported/SimGen.lean) offers raw values, lists, and literals. [`IsoGen.ArgReading`](../../ACL2Lean/MirrorProofs/IsoGen.lean) offers lists, embedded elements, and fixed arguments; square classes cover agreement and list/scalar/element results. SimGen explicitly rejects mutual blocks. | Records, tuples/multiple results, numeric recursion, and indexed word types need more than another sorting square. Replay support alone will not supply these products. | Add the representation and operation square needed by the first target: integer/word refinements for bitvectors, products and record fields for state. Build mutual generator support only when a selected mirror needs it. Preserve the same-algorithm/refinement discipline. |
| **Decode assembly remains handwritten.** A lexical census finds 65 top-level `theorem …of_replayed…` declarations under [`Imported`](../../ACL2Lean/Imported), including generic helpers, not 65 distinct products. [`Waypoints/Isort`](../../ACL2Lean/Imported/Waypoints/Isort.lean) illustrates per-theorem assembly. [`LiftingRel`](../../ACL2Lean/Imported/LiftingRel.lean) already supplies comparison and conjunction combinators. | The final few lines of `mirror_transport%` hide the setup cost. New theorem formulas, environments, and representation hypotheses still require manual assembly. | Generate source/body/formula bindings and decode assembly from explicit representation declarations plus the replayed statement. Cover implication, equality, predicates, comparisons, and conjunction as they occur. Count all required user code, not just the final declaration. |
| **Cross-book proofs work, but orchestration is tied to the demonstration harness.** [`Runner`](../../ACL2Lean/Replay/Runner.lean) already transports eligible imported constants across checked world extensions, with re-replay as fallback. [`Coverage/Harness.covDeps`](../../Tests/Coverage/Harness.lean) supplies a hand-maintained book DAG and a functional-instantiation pre-pass. The [focused CLI](../../ReplayMain.lean) does not run that full pre-pass. | A new caller must discover dependency logs and reconstruct harness setup. CLI and coverage success are not interchangeable for functional-instantiation capstones. | Promote the existing per-book preparation pipeline into the reusable importer. Capture dependency identities and package/certification context; cache checked modules by their actual inputs. Reuse the existing world-transport lemmas rather than propose them as new work. |
| **Execution-kit registration has global name scope.** `ExecGen.findKit` keys on an ACL2 name string; `registerKit` rejects duplicate names and explicitly asks for registry scoping before generating same-named kits from another book. | Independent developments cannot freely register their own same-named functions in one Lean environment. Package support alone will not solve book/world collisions. | Scope generated kits by full symbol identity and definition/world identity, with checked reuse when definitions agree. Exercise this through two independent imported developments, not by weakening the duplicate-registration check. |
| **Semantic breadth and proof records remain independent limits.** Package identity bugs BUG-013/015/017, complex numbers BUG-009, forcing rounds, guard obligations, and nested lambda paths are concrete examples. `MOD`, `FLOOR`, `LOGAND`, and `ASH` have no direct builtin dispatch, though captured definitions may provide logical routes. | “Add bitvector tactics” cannot solve a reader failure, an incorrect package identity, missing logical definitions, or an unrecorded transformation. | Classify every new failure by pipeline stage. Preserve ACL2's logical definitions where possible; extend the semantic core only deliberately. Add emission at the source where proof data is missing. Never treat a missing primitive-table entry alone as proof that a function cannot be interpreted through its definition. |

The old overspecialization audit is a useful search guide, not a current work
list. For example, the measure table and several transport rungs have landed
since that audit. The fresh mutual-recursion and clause-processor probes above
likewise refute blanket descriptions of those layers as parse/replay failures.
The [backlog](../../TODO.md) needs a targeted reconciliation before estimating
an arc: it still includes the already-tagged release and historical sorting
milestones. Do not spend the successor arc polishing that entire journal.

One fidelity constraint matters particularly for arithmetic broadening:
[`GzRules`](../../ACL2Lean/Replay/GzRules.lean) distinguishes boot-skipped facts
from ordinary book theorems whose proofs have not been captured. Capture and
replay the latter as their books enter the dependency closure, retiring those
entries. Extending the hand-proved rune registry for each new arithmetic book
would defeat the intended scaling model.

## Candidate targets

The judgments below combine inspected source with the probes above. Relative
costs are engineering judgments, not measured implementation estimates.

| Candidate | Useful result and pressure on the machinery | Assessment |
| --- | --- | --- |
| Order-generic sorting | A sorter over arbitrary total orders; stronger constrained-function and refinement support | Worth retaining from the governing plan, but weak evidence of breadth beyond the existing corpus. A secondary target. |
| [`misc/records.lisp`](../../acl2/books/misc/records.lisp) | Typed record lookup/update laws: same-key read after write, other-key preservation, shadowing, commuting independent writes | Best lower-cost fallback. Reuses ordering/list reasoning while requiring pair/record refinement and real package/dependency setup. It does not by itself establish array, memory, or stobj support. `records-bsd.lisp` is only an include wrapper in this checkout. |
| [`models/jvm/m1/sum.lisp`](../../acl2/books/models/jvm/m1/sum.lisp), then another M1 program | A typed machine state reaches a halted state with the specified arithmetic result; numeric countdown, state access, clock induction, dependency reuse | Good intermediate machine example. M1 uses unbounded integers and parsed instructions, with no heap: its [README](../../acl2/books/models/jvm/m1/README) explicitly distinguishes it from the JVM. Useful as a probe, but another pedagogical demo is insufficient as the final product. Not captured here. |
| [`kestrel/bv/bvchop.lisp`](../../acl2/books/kestrel/bv/bvchop.lisp), `bvplus`, `bvcat` | Word truncation, modular addition, concatenation; integer arithmetic, width parameters, four-argument functions, representation transport | **Recommended next family.** Directly relevant to software proofs and to x86 prerequisites. Fresh capture makes the first blocker known. Arithmetic dependency breadth makes it materially harder than “just some bit operations.” |
| [`centaur/bitops/ihsext-basics.lisp`](../../acl2/books/centaur/bitops/ihsext-basics.lisp) | Bit operations used directly by x86isa | A strategically relevant follow-on/validation corpus. Its source already brings `BITOPS`, generated events, and `arithmetic/top-with-meta`; less attractive as the first bounded import. Kestrel support will not automatically replay these distinct proofs. |
| x86isa application-level popcount correctness | A theorem about actual instruction bytes, registers, and execution | Strong long-term product; several substantial prerequisites remain. Choose one theorem and its dependency closure, not the top-level directory. |
| Full x86isa, including system-level execution | Broad ISA and system-software verification | Premature as the next completion criterion. The pinned directory alone contains 188 `.lisp` files and 159,389 lines, excluding dependencies elsewhere. These are source-inventory counts, not the closure needed by popcount. |

A useful secondary test is a **held-out book chosen after the shared mechanism
is implemented**, with its source and theory unchanged. This protects against
the observed failure mode of a new registry whose entries exactly match the
new passing corpus. Deliberately authored pattern books remain appropriate
for isolating a real upstream shape, provided ACL2 produces the actual logs.

## The proposed bitvector milestone

Start with the following exported theorem targets. Their names and statements
are present in the pinned upstream sources; none is claimed replayed here.

| Book | Initial targets | Intended native reading |
| --- | --- | --- |
| `bvchop.lisp` | `bvchop-upper-bound`, `bvchop-of-bvchop-same`, `bvchop-identity` | Truncation stays within its width, is idempotent, and preserves an already bounded value. |
| [`bvplus.lisp`](../../acl2/books/kestrel/bv/bvplus.lisp) | `bvplus-associative`, `bvplus-commutative` | Algebra of the imported modular-addition operation. |
| [`bvcat.lisp`](../../acl2/books/kestrel/bv/bvcat.lisp) | `bvchop-of-bvcat-same`, then `slice-of-bvcat` | Width preservation and extraction from concatenated words. The second theorem is a stretch beyond the first six. |

The milestone is the selected theorem set **and every proof obligation it
depends on**, not a claim that all of `kestrel/bv` has been imported. Capture
the unmodified books and their real dependencies. Report other rows as
unsupported where appropriate, while keeping malformed input fatal and
keeping all conditions of an accepted product discharged.

Draft the Lean-facing definitions before implementing their transport. Start
with a native width parameter and integers/naturals where that is the closest
reading of the book; use `BitVec w` or a bounded-value refinement where it
faithfully describes the operation. Width zero, negative integer inputs,
signed versus unsigned readings, and ACL2's `ifix`/`nfix` behavior need explicit
correspondence. Restricting a mirror to a typed input domain is acceptable
when stated openly; it must not masquerade as the full untyped ACL2 statement.
The underlying replayed statement still follows the book's actual formula.

For book functions, follow the own-definition naming rule. Merely restating
a standard Lean addition law and closing it from Lean's library would not be
an import. The representations and generated squares must connect the chosen
native operation to the book's operation, and the theorem proof must consume
the replay. A downstream user can then connect that operation to standard
Lean interfaces through ordinary reasoning.

The central acceptance experiment is this: after the first book establishes
the necessary operation/representation families, import another book without
adding theorem-specific Lean proofs or editing replay internals. The user
supplies the desired native definitions/statements and correspondence
declarations. Generated statements, environments, execution correspondences,
decodes, and catalog bookkeeping are tool work. If the held-out book exposes
a missing family, record it and repeat the experiment on a further book after
the extension; do not relabel the failed experiment as “nearly free.”

## Working backward from x86

The longer-term target should first be **application-level execution of a
specific program**. The official [application-view documentation](https://acl2.org/doc/index-seo.php?path=5216%2F58419%2F8094%2F12158%2F5794&xkey=X86ISA____APP-VIEW)
explains that this view abstracts OS services such as paging. It reduces the
target's scope, but does not remove state, bit operations, decoding, or proof
dependencies. The following requirements are inferred from the pinned source;
I did not capture or replay an x86isa book in this investigation.

1. **Reproduce the ACL2 proof environment.** The popcount book begins in
   `X86ISA`, uses `:dir :proof-utils`, includes GL, and requests trust tags.
   Its [`cert.acl2`](../../acl2/books/projects/x86isa/proofs/popcount/cert.acl2)
   registers that include directory and loads a portcullis book. The current
   capture command is an `ld` into a fixed image; the source closure scanner
   handles relative and `:system` includes, not a general certification world.
   Support package imports, portcullises, include-directory mappings, and
   expanded-event identities. A certificate helps reproduce ACL2's world;
   it supplies no Lean proof of the theorems loaded from it.
2. **Handle the logical state model.** The checked-in
   [`machine/state.lisp`](../../acl2/books/projects/x86isa/machine/state.lisp)
   uses `rstobj2::defrstobj` and a nested `bigmem` memory object. This is more
   specific than older accounts of a single flat x86 stobj. The current
   [state documentation](https://acl2.org/doc/index-seo.php?path=5216%2F58419%2F8094%2F12158%2F882&xkey=X86ISA____X86ISA-STATE)
   confirms the nested record structure. Model the logical access/update
   functions and prove their correspondence to a native state representation.
   ACL2's [stobj documentation](https://acl2.org/doc/index-seo.php?xkey=ACL2____STOBJ)
   distinguishes functional logical semantics from destructive execution;
   reproducing host mutation is not a prerequisite for replay. Abstract
   interfaces and their correctness constraints still require proofs.
3. **Cover integer and bit-level semantics through every layer.** Masks,
   shifts, sign extension, word widths, flags, address arithmetic, and memory
   byte access need logical semantics, proof recipes, and native refinements.
   Reuse the bitvector arc, then validate against the actual Centaur/IHS
   dependencies. Do not assume Kestrel's operation names or proofs coincide.
4. **Replay expanded function bodies and their admissions.** Multiple values,
   nested lambdas, generated accessors, `mbe`/logical bodies, numeric measures,
   and larger arities all occur on this route. Macros do not necessarily need
   a second macroexpander in Lean: capture their expanded logical events with
   source provenance. Capture alone does not prove those events.
5. **Close the proof mechanisms actually used.** Both the explicit
   `x86-popcount-32-correct` theorem and intermediate lemmas in
   [`popcount-general.lisp`](../../acl2/books/projects/x86isa/proofs/popcount/popcount-general.lisp)
   use GL. Even the apparently different
   [`fact-wormhole-abstraction.lisp`](../../acl2/books/projects/x86isa/proofs/factorial/fact-wormhole-abstraction.lisp)
   uses a local `def-gl-thm` helper. Choosing factorial does not demonstrate
   that the GL dependency disappears. Establish how GL's symbolic
   transformations and final obligations become replayable evidence before
   estimating either target.
6. **Respect the existing decision-procedure boundary.** A SAT/SMT success
   bit, a trust tag, or an ACL2 certificate is not proof. A future GL route
   needs checked transformation evidence and kernel-checked leaf proofs (or
   checked certificates with proved translation). The existing verdict-only
   DP-leaf exception does not automatically authorize treating an entire GL
   derivation as an opaque leaf. Any proposed extension is a design decision
   for review. A native word solver can help discharge permitted leaves; it
   cannot replace the recorded machine-code proof.
7. **Make the product statement substantial.** The native theorem should
   describe execution of the pinned instruction bytes from a specified native
   state, reaching the halt address with the result register equal to the
   input's population count. Preserve the setup and termination conclusions
   of the book's theorem. A proof of a standalone popcount arithmetic identity
   does not establish machine-code correctness. The state and interpreter
   correspondence may itself be a major part of the work.
8. **Demonstrate reuse and scale.** Only after one such theorem, import a
   second program using the same instructions/state refinements. Measure
   changed-program latency and dependency reuse. System view, paging, OS
   execution, floating-point coverage, and the full ISA are later expansions
   with their own product statements.

The logical soundness claim remains the established one: the kernel checks
the user's native proposition end to end. Matching it to the named ACL2
theorem and retracing that theorem's proof remain attribution/fidelity
obligations supported by records and review, not additional kernel guarantees.

## A staged plan with explicit stopping conditions

These are proposed work packages, not authorized implementation or calendar
estimates. Each extension must be wired into the actual target theorem as it
is built. Preserve L1–L3: fragment-local proof mechanisms, abstract relations,
and world-parametric lemmas.

| Stage | Deliverable and acceptance evidence | Early exit / decision point |
| --- | --- | --- |
| **0. Feasibility and target contract** | Pin the six initial bitvector targets, intended Lean statements, dependency/certification environment, and first frontier per layer. Recapture dependencies as needed to expose their actual proofs. Produce a concrete scope for BUG-009, including its `RATIONALP`, count/induction, and type-mask consequences. Bound this investigation to a few development sessions. | Stop and report if complex-number support or a proof-backend ruling dominates the first product. Select the records fallback or explicitly approve that larger prerequisite arc. Never delete the complex theorem from the log to obtain a passing parse. |
| **1. One unfamiliar mirror end to end** | Close the first selected `bvchop` theorem and all its dependencies, with a native mirror, replay seam, statement/source review, and clean axiom receipt. Add only the primitive, decode, and refinement families that this proof consumes. | Stop if missing proof data cannot be captured within the agreed scope, or a design boundary/prerequisite exceeds Stage 0. Report the actual node and remaining conditions. Do not substitute a hand proof of the target. |
| **2. Reusable bitvector import** | Reach the six-target milestone through the shared importer; test a further held-out book. Eliminate required per-theorem handwritten decode/exec glue, measure total user effort, and demonstrate dependency reuse after an edit. | If every new theorem needs a special case, stop broadening the result set and identify the repeated missing abstraction from those real examples. The release criterion remains unmet. |
| **3. A usable tool release** | Fresh-project setup and documented import path; a separate Lean consumer imports the resulting module and derives a small application fact. A supported import either creates checked declarations or reports a structured frontier/condition. The library core builds without requiring every example log. | Stop claiming product readiness if users need to edit the coverage harness, guess portcullis state, or diagnose failures from a zero-exit console transcript. |
| **4. x86 feasibility, then one program** | First measure capture and the GL/state boundary on the pinned popcount closure. Prove a reusable state-access/refinement slice and a real GL-consuming slice before committing to the whole program. Then produce the native program theorem. | Stop if a broader trust/fidelity policy, unavailable capture environment, or an unmeasured proof backend is required. Record a revised target; do not keep adding unrelated machinery to avoid the decision. |

For implementation milestones, use the existing focused checks during work
and the full `just claim-gate` at the required claim/arc-exit points. New
mirrors should join the existing axiom, seam, purity, and independent-validation
workflow. This assessment does not introduce a new audit or gate system.

Track two separate costs: **one-time machinery work per reusable family** and
**user work per subsequent import**. Report source/closure size, capture and
parse time, reconstruction time, replay/elaboration time, kernel-check time,
peak memory, serialized proof/module size, and warm rebuild behavior where
the tooling can actually measure them. Do not label the aggregate runner
timer “kernel time.” Profile before optimization; retain existing term sharing,
world transport, and module DAG work. Raising heartbeat limits is not a
scaling strategy.

Do not prioritize a general Lean-to-ACL2 tactic frontend, a full source-side
`gen-world` replacement, a monolithic proof checker, or all remaining pattern
rows before these product tests. The supported book-import workflow can
become useful first. Conversely, do not postpone basic packaging and honest
diagnostics until after x86: those determine whether anyone can use the
capabilities already earned.

## Reproduction and evidence limits

The probe outputs are retained locally under `.tmp/north-star-assessment/`
(gitignored); this note records the material results so it stands without
those files. The new `bvchop` source SHA-256 is
`19f0ebcdb29acab657919dcd4c2a5db46feaef096e70f8363f7bcddb400b1a79`.
Its capture sidecar records the pinned fork, source, include hashes, and log
hash. Existing corpus logs, source books, proof terms, and goldens were unchanged.

Representative commands, from the repository root:

```sh
lake build acl2lean-replay
lake env .lake/build/bin/acl2lean-replay --dump acl2_samples/simple.proof-log
lake env .lake/build/bin/acl2lean-replay acl2_samples/recon-tests/07-mutual-recursion.proof-log
lake env .lake/build/bin/acl2lean-replay acl2_samples/pattern-tests/cov-mv-let.proof-log
lake env .lake/build/bin/acl2lean-replay --dump acl2_samples/pattern-tests/cov-force-round.proof-log

mkdir -p .tmp/north-star-assessment
CAPTURE_WORKER=1 OUTDIR="$PWD/.tmp/north-star-assessment" \
  timeout 60 scripts/capture-proof-log.sh acl2/books/kestrel/bv/bvchop.lisp
lake env .lake/build/bin/acl2lean-replay --dump .tmp/north-star-assessment/bvchop.proof-log
```

`CAPTURE_WORKER=1` suppresses invalidation of the existing coverage artifacts
for these isolated captures into unused scratch paths; it does not bypass
capture completeness or provenance checks. Use the normal capture workflow
when replacing any library/test input. The 60-second timeout is a bound for
this exploratory capture, not a performance requirement.

The measurements do not establish bitvector replay coverage, the first
post-parser `bvchop` failure, x86 dependency-closure size, or the time to
implement any proposed extension. Those are Stage 0/4 questions. Online ACL2
documentation was consulted for the application view and state semantics;
implementation-specific observations above use the pinned local source, since
the upstream documentation can move independently of this checkout.
