# Top-level claims audit — 2026-08-19

## Scope and verdict

This audit reviews the repository's public, top-level claims, principally
`README.md`, against the live Lean declarations, the ACL2 sorting books, the
proof-log/provenance gates, the mirror assembly, and the repository's own
canonical trust model.

The central logical-soundness claim is supported: the fifteen sorting products
are real Lean theorems, their statements contain no ACL2 notions, and each has
the advertised axiom receipt
`[propext, Classical.choice, Quot.sound]`. A bug in the ACL2 pipeline cannot make
one of those elaborated Lean propositions false.

The front page nevertheless overstates a different claim: that the kernel also
certifies that each result is the intended ACL2 theorem proved by ACL2's actual
recorded proof. The repository's own trust analysis correctly separates theorem
truth, statement authenticity, and replay fidelity; `README.md` collapses them.
It also presents concrete instance theorems as though they were polymorphic,
gives insufficient fresh-clone build instructions, and conflicts with binding
status documents.

## Audit target and ground truth

Audited superproject `main` at `1752ac6`, with ACL2 submodule
`e8d78e513d6867d04002f0df644da1723cc96e89`. The worktree was clean before this
report was added.

Mechanically re-established during this audit:

- `ACL2Lean/Mirrors/Sorting.lean` contains fifteen target `Prop` definitions.
- `ACL2Lean/MirrorProofs/Sorting.lean` contains fifteen
  `mirror_transport%` product theorems and fifteen guarded axiom receipts.
- Fourteen products are at `Int`; `permWitness_complete_optint` is at
  `Option Int`.
- `lake env lean ACL2Lean/MirrorProofs/Sorting.lean` exited 0, validating all
  in-file guarded receipts.
- `lake env lean ACL2Lean/MirrorProofs/SeamGate.lean` exited 0 and reported 21
  mirror products (fifteen sorting plus six basics), each transitively consuming
  a replayed statement. The printed seam names matched the products' subjects.
- `just check-mirrors-pure`, `just check-proof-logs`,
  `just check-log-provenance`, and `just test-provenance-gates` all passed.
- Provenance covered 91 logs, all stamped at the pinned ACL2 submodule commit;
  all four negative provenance fixtures failed closed and the control passed.
- `just test` exited 0 and completed 3,251 jobs.
- The latest full claim-gate artifact for the code at the README commit,
  `.gate-runs/8d934b9-20260819T060913Z.log`, records successful builds,
  `REPLAYED 116/116 (116 unconditional + 0 conditional)`, a golden/current
  match, and `TRUE_EXIT=0`. The current HEAD differs from that commit only in
  `docs/`.

The ACL2 source statements behind the fifteen products were also checked in
`acl2/books/sorting/{isort,msort,qsort,bsort,ordered-perms,perm,
convert-perm-to-how-many,sorts-equivalent}.lisp`. The named mirror subjects have
real book correspondents with the documented formulas, subject to the typed
rendering decisions recorded in the mirror specification.

## Findings

### P0 — The README conflates logical soundness, statement authenticity, and replay fidelity

`README.md:7-11` says the tool replays ACL2's actual proof step by step until
Lean's kernel checks every step, and that a bug anywhere in the import pipeline
makes the result fail to compile. This is too strong as a universal claim.

What the kernel certifies is the truth of the Lean declaration as elaborated.
The repository's more precise trust model says two further properties are not
kernel-certified:

1. **Statement authenticity:** the proposition really corresponds to the named
   ACL2 theorem. `docs/OVERVIEW.md:132-142` says a pipeline bug can produce a
   kernel-accepted proof of a different but true statement. Source hashes and
   hand statement pins are regression evidence, not a kernel proof of identity.
2. **Replay fidelity:** the proof follows ACL2's recorded reasoning rather than
   a stronger Lean-side route. `docs/OVERVIEW.md:143-153` treats this as a
   separately enforced invariant and records explicit deviations.

The live mirror seam gate strengthens today's evidence, but its own threat model
is explicit (`ACL2Lean/MirrorProofs/SeamGate.lean:33-42`): it catches detachment,
not mis-pairing; a product can consume another book's seam and still pass; and
nothing in the gate makes “proved via replay” kernel-certified. The generator's
fixed proof shape plus the waypoint and mirror seam gates make current
provenance strongly evidenced engineering, not mathematics.

There are also declared fidelity exceptions below the mirror layer:

- decision-procedure leaves are closed by a kernel-checked Lean decision
  procedure because ACL2 records only a verdict;
- expiry-held mechanisms are marked `DRIFT MARKER`; and
- `destructorChainOk` is explicitly a calibrated heuristic that predicts which
  replay route can discharge rather than reading a recorded route choice
  (`ACL2Lean/Replay/Driver/NodeCore/Ctx.lean:575-586`).

None of these can manufacture a false Lean theorem. They do, however, refute an
unqualified reading of “ACL2's actual proof, every step, certified by the
kernel.”

**Required correction:** retain the strong claim about mirror truth, but state
the three properties separately. Say that authenticity and replay fidelity are
supported by provenance, statement pins, generated templates, seam gates, and
review, with the documented exceptions.

### P1 — The README presents concrete instance products as polymorphic theorems

`README.md:18-22` displays representative results over `List α`, then
`README.md:27-30` says the theorems are applied at one seven-line
`TotalOrder Int` instance.

The live product declarations are not order-generic:

- fourteen sorting products instantiate their spec `Prop` at `Int`, e.g.
  `isort_ordered_int : ACL2Lean.Sorting.isort_ordered Int` at
  `ACL2Lean/MirrorProofs/Sorting.lean:105`;
- the fifteenth is
  `permWitness_complete_optint : ACL2Lean.Sorting.permWitness_complete
  (Option Int)` at `ACL2Lean/MirrorProofs/Sorting.lean:524-528`, and is
  deliberately order-free;
- `docs/plans/2026-08-12_master-plan.md:12-33` distinguishes these near-term
  instance mirrors from the still-later order-generic capstone.

The polymorphic `Prop` schemas in `ACL2Lean/Mirrors/Sorting.lean` are useful and
real, but a schema's existence is not a proof for every `α`.

There is a smaller singular/plural error in `README.md:24-25`: not every product
comes from one corresponding `defthm`. `permuted_equivalence_int` assembles the
reflexive, symmetric, and transitive conjuncts from three replayed ACL2 theorems,
as documented at `ACL2Lean/MirrorProofs/Sorting.lean:287-317`.

**Required correction:** render the examples at `Int`, explicitly call them
instance products, disclose the one `Option Int` product, and use “corresponding
ACL2 theorem or theorem bundle.”

### P1 — The documented fresh-clone build sequence cannot build the default targets

`README.md:49-52` correctly warns that generated proof logs are absent from a
fresh clone and directs the reader to `docs/OVERVIEW.md`. The linked instructions
then capture only `simple.lisp` and `recon-tests/*.lisp`
(`docs/OVERVIEW.md:175-187`) and say `just capture-all-logs` is not required just
to build (`:189-190`).

That is inconsistent with the build graph:

- `lakefile.toml:3` makes the executable and `Tests` the default targets;
- `Main.lean:1` imports the root `ACL2Lean` library;
- `ACL2Lean.lean:5-15` imports the sorting mirror proofs and seam gate; and
- sorting waypoint modules embed sorting logs at compile time, e.g.
  `ACL2Lean/Imported/Waypoints/Msort.lean:11-16` includes
  `acl2_samples/sorting/msort.proof-log`.

Pattern waypoint modules likewise embed pattern logs not generated by the
documented reduced command. The overview's own later reproduction inventory
correctly says that 91 `.proof-log` plus `.proof-log.meta` files are needed and
names `just recapture-all` (`docs/OVERVIEW.md:192-201`).

**Required correction:** make `just recapture-all` the fresh-clone instruction,
or introduce and document a smaller build target whose import cone really needs
only the stated logs.

### P1 — Binding status documents contradict the live product claim

The README's count is live and correct, but the documents identified by
`AGENTS.md` as binding/canonical disagree with it:

- `CLAUDE.md:133-158` says “Today it reaches only the WAYPOINT layer” and calls
  the product layer a north star still being built toward.
- The governing master plan says the sorting specification has thirteen Props
  (`docs/plans/2026-08-12_master-plan.md:3-8`) and still describes an unfinished
  order-generic capstone.
- `TODO.md:3-5` and the live declarations say fifteen sorting Props, fifteen
  proved products, and 21 products overall.

The stale `CLAUDE.md` text is especially damaging because its trust note is
binding and directly contradicts the front page's central result.

There is a second conservative stale statement in `docs/OVERVIEW.md:105-121`:
its quoted 2026-08-16 audit says the mirror-level seam gate is absent and refers
to nine live artifacts. The gate now exists and mechanically finds 21 products.
The quote can remain as a historical quotation only if the current disposition
is stated immediately after it.

**Required correction:** update the binding status paragraphs and counts, while
preserving historical plans/audits as dated records with explicit disposition
notes.

### P2 — “No sorry ... anywhere” is broader than the evidence

The important claim is true in the checked library: no compiled mirror or replay
declaration contains `sorry`, `admit`, a user `axiom`, or `native_decide`; the
mirror axiom receipts contain only the standard trio.

But `README.md:36-41` says “no `sorry`, no `native_decide`, anywhere.” The
advertised `gen-world` command deliberately emits Lean theorem stubs ending in
`:= sorry` (`ACL2Lean/WorldGen.lean:162-173`). It is a string template rather
than a hole in the built library, but “anywhere” includes a supported command's
output under its ordinary reading.

The same paragraph says two lemmas in the specification are proved natively.
There are six native helper/termination theorem declarations in
`ACL2Lean/Mirrors/Sorting.lean`: `length_evens_le`,
`length_filterRel_le`, `howManySmaller_cons`, `howManySmaller_bnext`,
`howManyBadPairs_bnext_le`, and `howManyBadPairs_bnext_lt`. Exactly two of those
are also named ACL2 book theorems; that is the narrower fact the specification
carefully discloses at `ACL2Lean/Mirrors/Sorting.lean:31-56`.

**Required correction:** say “no holes or `native_decide` in the checked library
or mirror proof closures,” and “two natively proved helpers duplicate named ACL2
book theorems.”

### P2 — Minor front-page pipeline-count error

`README.md:56-57` describes `docs/OVERVIEW.md` as the “seven-stage pipeline.”
The linked overview numbers nine stages: source, instrumentation, parsing,
reconstruction, statement derivation, interpreter, replay, waypoint, and mirror.
The older seven-stage decomposition treats waypoint and mirror as downstream
layers, but the link description should match the document it names.

### P2 — A green test run currently contains a deterministic Lean panic

`just test` exited 0 and ended `Build completed successfully (3251 jobs)`, but it
also printed a deterministic panic from
`Lean.LibrarySuggestions.SymbolFrequency` while processing the
`BSsortsEquivalent` build. The latest full gate artifact contains the same panic
and still ends `TRUE_EXIT=0`.

The panic occurs after the relevant proof work and did not invalidate an olean or
an axiom receipt, so this audit does not treat it as evidence against theorem
truth. It is nevertheless inconsistent with the repository's “warnings are
unacceptable” working rule and makes an unqualified “green” build claim noisy.

**Required follow-up:** classify and either eliminate the panic or document why
that specific Lean post-processing failure is non-semantic and acceptable. Do
not use it to weaken proof or replay failures.

## Claims supported by the evidence

The following top-level claims survived review:

1. **Fifteen sorting target propositions exist and all fifteen have product
   proofs.** The count is exact: fifteen `mirror_transport%` declarations and
   fifteen matching guarded receipts in `MirrorProofs/Sorting.lean`.
2. **The mirror statements are ACL2-free.** The sorting specification has zero
   imports and `just check-mirrors-pure` passes.
3. **Every sorting product's axiom footprint is exactly the advertised trio.**
   All fifteen guarded `#print axioms` receipts elaborate.
4. **Every current product consumes replay.** The live mirror seam gate reports
   all 21 products with a replayed-statement witness; the fifteen sorting
   witnesses have the expected subjects.
5. **The named sorting statements have ACL2 book correspondents.** Direct source
   inspection confirmed the formulas for the fifteen product subjects, including
   the three `*-IS-ISORT` functional-instance capstones.
6. **The latest full coverage claim is reproducible from the present local
   artifacts.** The claim-gate log records 116/116 unconditional theorem rows,
   and the current proof-log and provenance gates pass over all 91 logs.
7. **Pipeline bugs cannot make a false mirror proposition kernel-check.** The
   mirror proposition is stated entirely in Lean's own vocabulary and the kernel
   checks the proof term. The qualification is that the kernel does not certify
   ACL2 attribution or replay provenance.

## Could not verify

- The 91 proof logs were not regenerated from a freshly built ACL2 image during
  this audit. Their hashes/provenance and negative tamper gates were checked.
- The full long-running `just claim-gate` was not rerun. The audit used the latest
  artifact for the code at the README commit plus current focused builds and
  checks; subsequent changes are documentation-only.
- The interpreter was not differentially re-tested against ACL2 during this
  audit. Open fidelity bugs remain documented in `docs/BUGS.md`; they bound the
  tool's general ACL2 masquerade, not the kernel truth of the fifteen mirror
  products.
- The seam gate establishes reachability of a replay seam, not theorem-specific
  semantic dependence. The expected mapping was inspected for the fifteen live
  products, but there is intentionally no unforgeable kernel-level provenance
  certificate.

## Recommended disposition

The front page should keep the successful result prominent, but adopt the
repository's already-written two-sentence trust story in current form:

> Every mirror theorem is a self-contained Lean statement over zero-import
> definitions, kernel-checked with the standard classical/quotient trio; no bug
> in the ACL2 pipeline can make that Lean statement false. Its attribution to a
> particular ACL2 theorem and proof is strongly evidenced by source provenance,
> statement pins, generated transport templates, replay/seam gates, and review,
> but that provenance is not itself certified by Lean's kernel.

Then state the concrete scope: fourteen sorting products at `Int`, one at
`Option Int`, research-prototype breadth outside the demonstrated corpus, and
the exact fresh-clone reproduction command.
