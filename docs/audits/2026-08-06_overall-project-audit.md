# ACL2Lean overall project audit — 2026-08-06

## Executive verdict

ACL2Lean is on a credible technical path, and its strongest engineering feature is
that replay results are ordinary Lean proof terms checked by the kernel and filtered
for unexpected axioms. I found no kernel proof of a false native theorem in the
current tree. The current build and local conformance gate pass, the encapsulate
witness bug now fails closed, and the previously dangerous `ASSUMED:dp-fact` path is
structurally excluded from registered replay mirrors.

That is not yet enough to support the README's strongest claims. There are three
distinct properties which the project sometimes conflates:

1. **Lean logical soundness:** the declared Lean theorem follows from Lean's trusted
   basis and its listed axioms.
2. **ACL2 statement authenticity:** the Lean evaluator proposition denotes the same
   theorem, functions, scope, and value universe as the named ACL2 event.
3. **Replay fidelity:** the proof uses the recorded ACL2 reasoning rather than a
   stronger Lean-side derivation or an unrelated reachable replay seam.

The current gates are strongest on (1), incomplete on (2), and intentionally partial
on (3). Native decoding does not make stages 2–6 irrelevant: if those stages silently
substitute a different but true proposition, the native theorem can still typecheck.
That exact class has already occurred with encapsulate witnesses. The README statement
that a pipeline bug “can never certify a false native theorem” is therefore too strong.

The main threats to scaling are provenance which does not bind logs to source books,
a producer that warns rather than fails on incomplete ACL2 runs, the absence of a
mechanical source/log/statement identity chain, broad conditional replay coverage,
and a Mirror definition which currently permits ACL2 value types and even one theorem
containing the evaluator itself.

## Ground truth re-established

Audited `main` at `c85d2be`, ACL2 submodule `24e6dbc1382b`.

- `lake build`: success, 6,328 jobs.
- `just ci`: success. Shell checks, bug index, no-shadow check, instrumentation tags,
  dark-file check, proof-log presence/provenance, pattern map, build, tests, tamper tests,
  and the golden driver sweep all passed.
- Golden driver result: **86/116** theorem rows replayed: **31 unconditional, 55
  conditional**. Standalone DP probes: **60 proved, 11 assumed, 0 failed of 71**.
- No live `sorry`, `admit`, user `axiom`, or `native_decide` was found in project Lean
  declarations. Meta-programs do use `unsafe evalExpr`; this is acceptable for proof
  generation because generated terms are kernel checked, but makes the build tooling
  part of authenticity/fidelity control.
- Native catalog declarations are gated to the standard trio
  `propext`, `Classical.choice`, and `Quot.sound`.
- The working tree was clean before this report; this report is the only audit edit.
- `just diff-test`: success, **497 match, 143 unsupported, 10 known-bug, 15
  refuse, 0 FAIL**. GitHub CI, rather than local `just ci`, is the configured
  automatic differential gate.

## Findings

### P0 — Source-to-log provenance is not closed

**Impact:** an edited ACL2 book can be paired locally with an old proof log while
`just ci` and `just claim-gate` remain green. The resulting theorem is a proof about
the old logged development, not demonstrably about the current source.

The `.proof-log.meta` sidecar records the ACL2 fork commit, image mtime, and capture
time. `check-log-provenance.sh` verifies the fork commit against the submodule and the
banner against the sidecar. It records neither the source path nor a digest of the
source and its transitive `include-book` closure. Proof logs are gitignored and Lean
embeds them with `include_str`; therefore the source file and the proof artifact are
not cryptographically or structurally paired in a local gate.

Remote CI recaptures tracked books, which substantially contains this for pushed
changes, but the documented local completion/claim gate does not. It also does not
solve identification of the exact included-book closure or external certification
artifacts.

**Action:** add a manifest event or sidecar fields for canonical source path, SHA-256
of the loaded source, and hashes/identities of every transitively loaded book. Make
`check-log-provenance` recompute and compare them. Prefer an ACL2-emitted event after
successful `ld`, since a shell-side hash alone cannot identify what ACL2 actually
loaded. Include the manifest digest in generated Lean declarations and in the native
catalog entry.

### P0 — Incomplete proof-log capture exits successfully

**Impact:** failed or truncated ACL2 runs can be accepted as producer output. Known
coverage goldens often catch this downstream, but the capture boundary itself is not
fail-closed, and new or partially covered books need not be protected.

`capture-proof-log.sh` correctly detects hard errors, missing QED records, and a
shortfall versus textual source `defthm` count, but each branch prints `WARNING` and
continues. It then writes a valid-looking provenance sidecar and exits zero. The script
comments call downstream `buildDevelopment` load-bearing, but that only detects a
started theorem without QED. It cannot know about later events absent from a truncated
log without an independent expected manifest.

**Action:** make every detected incomplete condition fatal, remove the output and
sidecar (or write to a temporary file and atomically rename only on success), and emit
an explicit `BEGIN/END` capture record with source identity and successful `ld` status.
Reject missing end records in `ProofLog.parse`/`buildDevelopment`. Replace the regex
source theorem count with an ACL2-produced event manifest.

### P0 — The README overstates the native bridge's soundness envelope

**Impact:** reviewers may stop auditing statement authenticity after a native bridge,
exactly where statement substitution can cross into user-facing claims.

README lines 62–69 say that after native decoding “a bug anywhere makes the composed
proof fail to typecheck” and can never certify a false native theorem. This is not
generally true. If instrumentation, parsing, scoping, world construction, or theorem
selection substitutes a different *true* ACL2-level proposition which is sufficient
for a false intended native claim under a faulty bridge, the kernel checks only the
composed Lean term. It does not know the intended ACL2 source. BUG-019 was a concrete
statement-substitution incident: local witnesses entered the world and made mirrors
about a particular witness rather than the constrained function. It is now contained,
but it refutes the general trust argument.

**Action:** rewrite the trust model around the three properties above. State that the
kernel guarantees the Lean declaration as elaborated; authenticity and replay fidelity
are separately enforced invariants. Native Mirrors reduce the evaluator-facing API
surface, but do not render the producer/translator untrusted until source-to-statement
identity and bridge correspondence are themselves mechanically established.

### P1 — There is no independent source-to-statement equality gate

The live Mirror pipeline says “the ONLY input is the log” and derives both the `World`
and theorem formula from that log. This contradicts README stage 5, which describes the
same ACL2 source being independently translated. A corrupted or buggy `:DEFTHM
:TFORMULA`, `:DEFUN :BODY`, scope marker, or included-theorem event can therefore feed
both replay and decoding without an independent comparison to source translation.

The hand-written native bridges often use `by decide` world facts and hand-selected
formula constants. These are useful pins, but they are per-entry and do not establish
that the log equals the current ACL2 source.

**Action:** create a checked import manifest from the source translator and compare it
against log-derived declarations before replay: event order, names/packages, formals,
translated bodies, theorem formulas, rule classes, scope, locality, include provenance,
and admission metadata. Refuse unsupported source events. Make every native catalog
entry carry the source event ID/digest and exact replay declaration ID.

### P1 — “Native Mirror” does not consistently mean ACL2-free Lean theorem

The highest project goal is a Lean-idiomatic theorem containing no ACL2 notions. The
catalog's criterion is weaker:

- Most native theorems quantify over `SExpr` or `List SExpr`. This is useful value-level
  interoperability, but it is not generally a theorem over ordinary user types.
- `true_listp_flatten_native_driver` is explicitly exempted from the criterion gate and
  contains `Env`, `evalOpt`, `treeWorldD`, an ACL2 term, and `enc` in its statement.
  It is an evaluator theorem, not a native Mirror under the stated highest goal.
- The criterion permits self-contained functions over `SExpr` which reproduce ACL2
  concepts. That can be a legitimate intermediate layer, but should not be the terminal
  ACL2-free product tier.

**Action:** split status into at least `Replay`, `DecodedSExpr`, and `NativeLean`.
`NativeLean` must ban `ACL2.*`, `SExpr`, `Env`, `World`, evaluator terms, and generated
exec functions from the public statement, unless the theorem is explicitly about an
ACL2 datatype. Remove the flatten exception from native counts and mark it decoded-only
until a genuine simulation/native definition exists. Prioritize polymorphic lifting
(`List α`, equality/order relations supplied natively) so sorting results become useful
beyond `SExpr`.

### P1 — The seam gate proves reachability, not theorem-specific dependence

The catalog checks that a native theorem's proof transitively reaches the named
`driver_replayed%` constant through constants in `ACL2.Imported.Mirrors`. This catches
complete detachment and is valuable. The source itself documents the remaining hole:
an in-book helper or rule discharger can make an unrelated replay seam reachable, so a
mis-paired catalog entry can pass. It also cannot detect ornamental consumption where
the native claim is actually proved by stronger Lean lemmas and the replay fact is used
only in a disposable side branch.

This is primarily an import-authenticity failure, not Lean inconsistency, but it is
central to the project's definition of success (“kernel proof that does not mirror
ACL2's reasoning does not count”).

**Action:** generate a theorem-specific sealed bridge interface. Its only non-structural
input should be the exact replay result; simulation lemmas may concern one function,
and decode lemmas may only eliminate representation/evaluator structure. Record a
machine-readable dependency certificate and reject cross-function semantic lemmas in
the bridge cone. Add mutation tests which replace the selected replay theorem with a
different same-book theorem or an easy tautology and require the native bridge to fail.

### P1 — Conditional replay dominates the green scoreboard

Only 31 of 86 green theorem rows are unconditional; 55 carry conditions such as
`total:`, `tp:`, `rule:`, `linear:`, and `use:`. Conditional proofs can be entirely
sound, but the headline “REPLAYED” count hides how much ACL2 content remains in Lean
hypotheses and how much is later discharged by hand-written or generated infrastructure.

The `ASSUMED:dp-fact` incident demonstrates the worst failure mode: a false condition
makes a conditional theorem vacuous. The present `tryReplay` and `driver_replayed%`
guards correctly refuse such mirrors, and `cov-encapsulate` is honestly red. However,
the system still keys ordinary conditions by strings in several registries and relies
on complicated discharge ordering and cross-book offers.

**Action:** make the primary scoreboard four-dimensional: reconstructed; replayed with
no conditions; replayed with mechanically sourced conditions; native ACL2-free Mirror.
Do not call a conditional row imported. Replace condition strings with a typed
structure containing class, source event ID, exact proposition, scope/world digest,
and proof/discharger identity. Keep the “assumed can never register” invariant as a
build test over every registration API.

### P1 — Cross-book dependency offers are not tied to the include graph

The coverage harness accumulates all earlier corpus trees/rules. Its own comments note
that corpus order is not the include graph: consumers miss some true dependencies and
receive unrelated offers. Offers are hypotheses and recomputation checks make current
behavior mostly fail-closed, but this architecture will scale poorly and weakens the
meaning of provenance.

**Action:** land the planned include-book edge emission before expanding corpus breadth.
Build an explicit DAG keyed by canonical book identity and certificate/source digest;
offer only transitive included dependencies. Reject duplicate theorem/rune names with
different identities rather than selecting by order or name.

### P1 — The decision-procedure carve-out needs a formal policy and smaller TCB surface

The DP path is sensible when Lean proves the exact emitted leaf obligation. The current
report shows 11 standalone probes as assumed, and prior audits found false independently
quantified opaque obligations. Although composed registration is now guarded, the
existence of `assumeFact := true` in a coverage probe makes output easy to misread and
maintains two semantics for “discharge.” Open policy questions also remain for
ground-hypothesis closure and branch-level verdicts.

**Action:** separate the assumed probe from the replay scoreboard entirely. Require a
typed leaf-origin enum and a ratified allowlist. The DP input proposition must be
constructed from the exact clause, exact environment, and exact applications—not fresh
independent opaque values—and checked for free-variable provenance. Add negative tests
for aliasing/functionality loss, altered clauses, omitted premises, wrong origin, and
branch-vs-leaf misuse. No new DP class should land before the policy decision is recorded.

### P2 — Parse/reconstruction failures are silently converted to `.done` in constants

Many embedded development definitions use
`((parse ...).toOption.bind build...).getD .done`. Downstream theorem lookup normally
makes a total parse failure compile-fatal for active Mirrors, and coverage uses explicit
error handling, so I did not find a current false green caused by this. Nevertheless it
is poor fail-closed construction: errors lose their diagnostics and definition-only or
future consumers can observe an empty development.

**Action:** provide one elaborator/command for `include_proof_log%` which reports parse
and reconstruction errors at compile time and returns a non-optional `Development`.
Forbid `.getD .done` in production import modules with a static check.

### P2 — The public status documentation is stale and internally inconsistent

`Imported/NativeMirrors.lean` calls its header the live scoreboard but lists only the
earlier 18 entries while the actual catalog now contains many sorting mirrors. README
stage 5 describes source translation although production Mirrors are log-derived. The
README says replay does “no inference” while prior/current implementation includes
explicit inferred or hand-classified closure paths and a ratified DP exception; the
current TODO itself records a complement close inferred from absence and an unresolved
ground-hyp carve-out. README limitations also understate current encapsulate/include
work while overgeneralizing its readiness.

**Action:** generate the public scoreboard from `liftCatalog`; replace absolute prose
with checked counters and explicit tiers. Add a documentation gate that checks named
frontiers/bugs and claims against machine-readable status. Reserve “faithful replay” for
rows passing a fidelity tier, not every kernel-checked conditional proof.

### P2 — Axiom policy is good but should be declared as part of the product contract

The project says “Lean kernel as the sole trust anchor,” while native proofs depend on
`propext`, `Classical.choice`, and `Quot.sound`, plus Lean/mathlib definitions and the
correctness of the elaboration/build artifact chain. These are standard and not a
soundness defect, but the wording is imprecise. The catalog's manually enumerated axiom
gate can also drift unless it is derived exclusively from catalog entries.

**Action:** state the exact logical trust base and derive the axiom scan from every
`.native` catalog record (not a second manual list). Fail if the two sets differ. Publish
the axiom set and source/log/world digests beside each generated Mirror.

### P2 — Interpreter fidelity remains a bounded, explicitly incomplete claim

The project responsibly records unsupported/refused/known-bug cases, including complex
rationals, package imports, escaping, package dispatch, and reader macros. These gaps
are safe only if affected inputs are refused before they can enter imported statements,
worlds, rewriting rules, substitutions, quoted constants, and native bridges. A
differential evaluator test alone does not prove all those ingestion paths share the
same refusal boundary.

**Action:** centralize canonicalization and supported-fragment validation on every
parsed `SExpr` entering a `Development`. Add a theorem-import preflight which walks the
entire world/tree/rule payload and rejects values/features outside the certified tier.
For each open semantic bug add an adversarial import test, not only an evaluator row.

### P3 — Scale and maintainability risks

- The qsort sweep alone takes several minutes and the full coverage run is expensive;
  this discourages frequent adversarial iteration.
- Large hand-written Mirror proofs and per-function dischargers create transcription
  and ornamental-proof risk even with the seam gate.
- String names, sanitizer-based declaration names, corpus-order registries, and
  hand-maintained lists are recurrent collision/drift classes.
- Prior audits are unusually thorough, but important findings have sometimes existed
  only in prose or uncommitted session artifacts. Audits are evidence, not gates.

**Action:** cache replay by content-addressed `(source, log, fork, semantics, driver)`
digest; generate typed IDs and catalog declarations; minimize hand bridge code through
generic representations/simulations; turn every confirmed soundness-class incident into
a small committed negative test before closing it.

## What is working well

- Kernel-checked proof production and explicit axiom filtering are the correct base.
- The current ASSUMED-condition choke points address a real vacuity bug.
- Encapsulate witnesses are excluded from the certified world and the adversarial book
  is pinned red.
- Golden coverage, reconstruction-integrity failure, black-box-leaf rejection, tamper
  tests, no-shadow checks, and instrumentation tag checks are valuable regression nets.
- The project openly records semantic bugs and named frontiers instead of using `sorry`.
- The native catalog's coverage, seam, vocabulary, and axiom gates are strong foundations
  once their definitions are tightened.

## Recommended execution order

1. **Stop claim drift now:** correct the README trust model and split replay/decoded/
   native status. Do not count the flatten evaluator theorem as native.
2. **Close artifact authenticity:** fatal capture, atomic outputs, completion marker,
   source/include hashes, and an explicit include DAG.
3. **Build the independent statement gate:** source translation versus log-derived
   events/world/formulas/scopes, with a content-addressed theorem identity.
4. **Harden conditions and DP:** typed conditions, exact application identity, no
   assumed probes in replay counts, ratified origin policy, adversarial vacuity tests.
5. **Strengthen the Mirror seam:** theorem-specific generated bridge interfaces and
   mutation tests for mis-pairing/ornamental use.
6. **Industrialize true native lifting:** polymorphic `Rep`/simulation kits and public
   theorems over `List α`, native relations, and Mathlib structures.
7. **Then expand feature breadth:** R7 functional instantiation, nonstandard measures,
   remaining bsort/equisort frontiers, and larger books only after provenance and
   statement identity are enforced.

## Release criteria suggested for the first trustworthy milestone

A theorem may be advertised as a soundly replayed native Mirror only when:

1. its ACL2 source and transitive include closure are content-addressed;
2. ACL2 emits an explicit successful, complete capture record;
3. source translation and log-derived event/statement/world manifests agree;
4. every replay node is recorded or belongs to a ratified, typed DP leaf class;
5. the replay has no assumed or unresolved conditions;
6. the native statement contains no evaluator, ACL2 world/term, or ACL2-only value type
   unless that datatype is explicitly the theorem's subject;
7. the bridge is mechanically paired with the exact replay theorem and uses only
   approved simulation/decode lemmas;
8. the proof's axiom set is within the published policy; and
9. source/log/rule/scope tampering and seam substitution tests all fail closed.

Until then, the project should describe its current result accurately as a strong
research prototype with kernel-checked replay proofs over a partially validated ACL2
semantic model and a growing set of decoded Lean consequences—not yet a generally
sound ACL2-to-native-Lean importer.
