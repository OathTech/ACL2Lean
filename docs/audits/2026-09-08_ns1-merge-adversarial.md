# NS1 merge-candidate adversarial audit — 2026-09-08

**Recommendation at the reviewed commit: request changes.** One verified
blocking fidelity defect has two newly added dispatch sites: ordinary ACL2
theorems are supplied by handwritten Lean model laws. The defect affects
maintained replayed statements and survives the existing axiom checks.

**Parent disposition after repair:** F1 is resolved and the full claim gate
passes. The branch is an incremental merge candidate with the existing
NS1/NS1-R incompleteness still explicit. The original review is retained below;
the final validation and limits are recorded in the parent section. No merge
or push was performed.

This is the single review requested before the parent performs fixes and
pauses before merging. No additional agents were used. Production code was
read only by this reviewer; diagnostic files were written under
`.tmp/ns1-r/audit-20260908/`. Parent fixes made after the findings were sent
are outside the original commit verdict below and need their own receipts.

## Reviewed identity and actual scope

- ACL2Lean branch: `mdd/ns1-bvchop`.
- Reviewed HEAD: `32b31c9be7f07c13138700c76801d73b7e5263df`.
- Main/base: `b452b700b6ec1b926fec348bcf9abf4949f33a9c`.
- Full candidate: 69 commits, 225 changed files, 26,882 additions and 5,509
  deletions. This review mapped the whole diff and commit sequence; it was
  not restricted to the final commit.
- Production ACL2: `fd27e59021cf7d0103a526dbda41553ad709eae3`, verified clean
  at initial inspection; diagnostic ACL2:
  `30503a673a7cf8c6fd6fae6547743f0e9541bb7e`.

The binding `CLAUDE.md`, canonical lexicon and overview, governing master
plan, NS1 charter, NS1-R plan, frozen supported scope, live bug index and
final execution record were consulted. The slice explicitly stops
incomplete. The absence of three BVCHOP mirrors, unfinished higher
quotient proofs, and unpromoted diagnostic producer do **not by themselves**
establish defects in an honestly scoped incremental merge.

## F1 — P1: two ordinary source theorems are bypassed as primitive laws

**New committed regression.** Both handlers below are additions relative to
the stated base. This is a fidelity/attribution defect, not a demonstrated
false Lean proposition or extra-axiom defect.

| Dispatch in reviewed HEAD | Actual ACL2 source | Bypassed proof content |
| --- | --- | --- |
| `ACL2Lean/Replay/Driver/NodeCore/Node.lean:299`; `PrimitiveInverse.lean:35`–`50` | `acl2/axioms.lisp:25453`, `(defthm default-unary-/ ...)` | `replayPrimitiveReciprocalDefault` uses `Logic.reciprocal_default` after relieving the application hypothesis. It does not replay the theorem establishing that rewrite rule. |
| `ACL2Lean/Replay/Driver/NodeCore/Node.lean:341`–`351` | `acl2/axioms.lisp:8300`, `(defthm distributivity-of-minus-over-+ ...)` | The dispatcher supplies `Logic.neg_plus` directly. `NumericNegation.lean:35` describes it as a ground-zero primitive equation, although ACL2 proves the named rule as an ordinary theorem. |

The classification is **verbatim primary-source evidence**. In particular,
`COMPLETION-OF-UNARY-/` at `axioms.lisp:25445` is a separate `defaxiom`;
its neighboring `DEFAULT-UNARY-/` is a `defthm`. The source also explicitly
describes the three addition lemmas around `axioms.lisp:8274`–`8303` as
proved `defthm` forms. Being located in `axioms.lisp` does not make every
declaration an axiom.

The governing plan requires ordinary dependencies to enter by replay;
NS1-R repeats that ordinary bootstrap `defthm`s remain on that side of the
boundary. This is distinct from proving that the semantic model satisfies
a real ACL2 axiom, and from the existing, documented D5 registry exception.
Neither new handler is an existing D5 registration. The older
`COMMUTATIVITY-2-OF-+` special handler is pre-existing and is not counted as
a new finding here.

### Real tree and live proof evidence

1. Fresh reconstructed `EQUAL-/` tree:
   `.tmp/ns1-r/r4-decision-reuse-trees.jsonl:171`, from
   `.tmp/ns1-r/r4-decision-reuse-capture/basic-arithmetic-helper.proof-log`.
   Address: `Goal/child:0/Goal'/simplify-clause/item:6/item:0/node:0`.
   The actual node is `DEFAULT-UNARY-/`, `(UNARY-/ X) -> '0`, with one
   recorded hypothesis child. Replaying that application child does not
   replay the ordinary theorem furnishing the rule.
2. Independently reconstructed production tree:
   `.tmp/ns1-r/audit-20260908/negation-trees.jsonl:4`, from
   `acl2_samples/ns1/basic.proof-log`, theorem `|(- (+ x y))|`.
   Address: `Goal/preprocess-clause/item:0`. It uses
   `DISTRIBUTIVITY-OF-MINUS-OVER-+` to rewrite
   `(UNARY-- (BINARY-+ X Y))` to
   `(BINARY-+ (UNARY-- X) (UNARY-- Y))`, with zero children.
3. `ordinary-negation-live.lean` reads and reconstructs that genuine log,
   then calls `tryReplay` with no cross-book tree or pre-replayed source
   theorem supplied. Observed result: `REPLAYED ✓`, `conditions=(some [])`;
   a fresh declaration `Audit20260908.ordinaryNegation` is registered and
   `#print axioms` reports the classical trio.
4. `ordinary-shortcuts.lean` inspects the transitive proof constants of
   maintained declarations. Observed:
   `ACL2.Tests.Ns1Arithmetic.reciprocalEqualityReplayed` contains
   `ACL2.Logic.reciprocal_default`, and
   `ACL2.Tests.Ns1Mod.integerModReplayed` contains both
   `ACL2.Logic.reciprocal_default` and `ACL2.Logic.neg_plus`.
   Both axiom receipts contain only `propext`, `Classical.choice`,
   `Quot.sound`. This command inspects already built declarations; the
   preceding item is the separate fresh construction check.

Exact commands, run from the reviewed worktree:

```sh
lake env lean --run scripts/replay-mechanism-inventory.lean \
  acl2_samples/ns1/basic.proof-log \
  .tmp/ns1-r/audit-20260908/negation-trees.jsonl '(- (+ x y))'
lake env lean .tmp/ns1-r/audit-20260908/ordinary-negation-live.lean
lake env lean .tmp/ns1-r/audit-20260908/ordinary-shortcuts.lean
```

All three corrected commands exited 0. The first attempt to inventory a
same-named theorem in `basic-arithmetic.proof-log` exited 1 with `theorem
absent`; it was not a proof failure and is not presented as positive evidence.

Input/receipt SHA-256 anchors:

| File | SHA-256 |
| --- | --- |
| `acl2_samples/ns1/basic.proof-log` | `4f25493186dce4f4106f8836d723e83371b7dcbd1ba18058119dc254fb3a2911` |
| `acl2_samples/ns1/basic-arithmetic-helper.proof-log` | `d8601ec880db2760d95e9120b33e5fb3a418987c54e59d8af9f0b641fc5e2bde` |
| `ordinary-negation-live.log` | `99279aff6f5b1d9b7e0f8b79a3c1b860cbbb99f4ba5d334b1b77d7167773fe1a` |
| `ordinary-shortcuts.log` | `23c30b6e9dda2c873170efabc04f3603a10fea4c68cb7eb34661a5268bab7cd0` |

**Impact.** Maintained “unconditional replay” claims include a route that
does not reproduce the named ordinary ACL2 dependency. Clean kernel/axiom
results cannot detect this: the substituted mathematical laws are true.
The charter's description of the reciprocal route as primitive is also
incorrect. No conclusion that the 21 existing pure Lean mirror propositions
are false follows from this finding.

**Minimal principled fix.** Remove these special ordinary-theorem dispatch
arms. Capture the original bootstrap proofs without modifying their forms,
hints, proof flags or event chronology, then feed their checked source trees
through the ordinary stored-rule/dependency machinery. Where that route is
not yet supported, retain an explicit condition/frontier. Preserve model
laws where appropriate for actual axioms and exact emitted DP obligations;
do not register these ordinary rules as new handwritten prelude exceptions.
Verify the actual consuming proofs and a missing-dependency refusal, then
run the required merge-candidate gate.

## Uncommitted capture/staging work: separate from the commit verdict

At audit start the dirty files were `Justfile`, theorem census/provenance
scripts and invalidation support; `Tests/Ns1Mechanisms/` and the two
bootstrap capture files were untracked. The recovery manifest in
`.tmp/ns1-r/r6-incomplete-handoff/manifest.json` matches that distinction.
The staged tests expressly say they are not integrated, and `Tests.lean`
does not import them. Their diagnostic successes are not maintained default
test coverage of the new producer.

The existing **BUG-060** chronology failure is real and independently
visible in the actual artifact:
`.tmp/ns1-r/r6-bootstrap-serialized/rationalp-minus.proof-log:14` introduces
`RATIONALP-UNARY--`, while line 53 includes that same rule in
`GROUND-ZERO-RULES`. The original WIP driver takes its snapshots after full
initialization. A late-world snapshot cannot be advertised as the
pre-window rule environment. This was already documented as an open WIP
promotion blocker; it is not a newly discovered regression in committed
HEAD's ordinary capture path.

During the parent fix round, an initial attempt to repair this by assigning
only the state global `current-acl2-world` was rejected on review. ACL2's
`fgetprop` (`axioms.lisp:11084`–`11140`) assumes that global names the
installed symbol-property cache; rebinding it to a historical list without
installing that world's cache makes snapshot `getpropc` calls return final
properties. The parent independently confirmed a self-rule in that initial
capture and rejected it. A historical snapshot must read the historical
alist while preserving the installed-world/cache invariant. This observation
concerns the corrective WIP, not the original merge-candidate diff.

The next WIP version scopes only the `w` accessor during snapshot printing,
leaving the installed world/cache paired. Source inspection supports that
boundary. The actual `snapshot-v2/reciprocal-default.proof-log` has no
ground-zero self-rule; its ordinary post-QED `:RULES` entry remains. Its
proof is a single `PREPROCESS/TYPE-SET-FC` fake-rune step without a recorded
structured query. This reviewer did not replay that revised capture; the
parent must establish that its source proof is faithfully supported before
claiming F1 resolved.

## Other assessed surfaces and limits of the evidence

- **Numeric semantics:** reviewed canonical complex construction, rational
  completion versus realpart, arithmetic and reciprocal/exponent completion,
  numeric `<` versus alphorder, recognizers, and value-level ACL2-COUNT.
  Checked the relevant production ACL2 source definitions and primitive
  axiom classifications. No additional concrete numeric counterexample was
  established in this review. This is not an exhaustive differential proof.
- **Recorded queries:** read the strict query schema, DWP handling, selected
  lookups, conditional decision/branch splitting, ordinary recognizer rule
  channel, constant definitional TP adapter, and known-true/explicit/FC
  consumers. The reviewed paths generally check child term/order and masks,
  and derive facts from checked context rather than assuming snapshots.
  New-record failures generally fail before legacy adapters. Unsupported
  intersections, ordinary backchaining and contradictory IF decisions are
  explicitly refused; those refusals are not counted as bugs.
- **Clause edits and context:** reviewed selected equality justification,
  positional recursive construction, exact fold matching, cleanup,
  child-clause implication and continuation reset, plus linear-row and FC
  context adapters. Inspected actual reconstructed tree inventories and
  their source mechanisms. Did not establish another accepted incorrect
  transformation. The ordinary linear-row construction gap exposed by fresh
  msort is explicitly outside the frozen supported fragment.
- **Relation/world boundary:** the new local judgments remain parameterized
  by world/environment; the EQUAL edit fragment does not establish arbitrary
  user-congruence support. Inspected source-stage reconstruction and
  ordinary recognizer/TP proof pairing. No concrete new world-crossing
  unsoundness was established.
- **Pins and claims:** the golden retains 116 unconditional theorem rows;
  its changed lines add five informational DP probes, not new theorem rows.
  The parametric pin additions are no-shadow premises for registered
  primitive heads. No native WordOps proof is claimed. None of these checks
  rescues F1's ordinary-rule attribution.
- **Producer changes:** inspected the production submodule diff map and
  high-risk source/scope, substitution-fold and snapshot changes. The
  diagnostic producer remains separate. This was not a line-by-line audit
  of every emitter change across both producer histories.

The full worktree receipt
`.gate-runs/c72e4a9-20260908T050003Z.log` actually ends in `TRUE_EXIT=0`,
116 unconditional baseline rows and 21 existing mirrors. It includes dirty
capture/provenance code and therefore is not by itself a clean-checkout
receipt for exactly committed HEAD. The parent independently extracted the
**committed** provenance/census scripts and ran them against all 110 actual
production logs and the committed negative controls; both passed. Those
parent checks support current-corpus provenance, not a fresh recapture or
cold build. No gate-hardening requirement is inferred.

Checks run by this reviewer: the fresh ordinary-negation proof and axiom
receipt; transitive maintained-proof/axiom inspection; complete tree
reconstruction for the actual negation theorem, `INTEGERP-MOD`, and
`|(* -1 x)|`; source/diff/provenance-manifest and receipt inspection; file
hashes. Existing negative-probe source was reviewed, but its whole suite was
not rerun by this reviewer. No new synthetic positive artifacts were made.

Not run by this reviewer: a duplicate full claim gate, clean-checkout
recapture/cold build, independent comparator/nanoda validation, all six
NS1-R whole-proof probes, or exhaustive semantic fuzzing. Core builds and
fixes were coordinated with the parent to avoid racing shared imports.
The full diff was much larger than can be exhaustively validated by one
broad review; an absence of further verified findings is not a proof of
absence. Original HEAD should not merge with F1 intact. The revised
candidate requires the parent’s concrete fix and validation receipts, then
the requested pause for merge sign-off.


## Parent fix round (2026-09-08; validation complete)

The original recommendation above remains the reviewer's verdict on
`32b31c9`. The parent independently confirmed both ACL2 `defthm` declarations
and dispatch sites, removed those two handlers and their unused handwritten
laws, and captured the original proofs with production ACL2 `fd27e590`.
Both real trees consist of a recorded whole-clause verdict: reciprocal
default uses `preprocess/type-set-fc`, and negation distributivity uses
`preprocess/tau-contradiction`. The existing verdict-leaf normalizers now
preserve conditional reciprocal premises and normalize negated sums through
canonical numeric components. There is no new decision-procedure allowance,
ordinary theorem handler, primitive registration, or resource-limit raise.

`Tests/Ns1Bootstrap` builds with both source statement pins, axiom receipts,
absence of self-rules before proof, and presence of post-proof stored rules.
`Tests/Ns1Arithmetic` and `Tests/Ns1Contexts` also build after passing the
bootstrap source tree alongside its checked consumer-world registry entry.
The ordinary rule decoder still checks the source tree against the stored
rule; a checked declaration alone does not waive that comparison.
The full MOD module also builds (298 seconds in the final gate run),
including both missing-dependency controls and the transitive source-reference
checks. Its source statement and axiom pins remain unchanged.

The bootstrap observer records the first actual proof window during original
full initialization; later passes execute unchanged. Its historical snapshot
uses the `w` accessor without changing the installed current-world/cache pair.
The failed first repair and its self-rule refusal remain preserved. A second
capture exposed a receipt parser bug when Lisp pretty printing wrapped
`:WINDOW-ENDED T`; the check now accepts ordinary whitespace. Production
captures pass provenance and the missing-receipt negative control. The
RATIONALP-UNARY-- diagnostic now has no self-rule, but its original verdict
remains unproved (`ASSUMED:dp-fact`); fixing chronology does not close NS1-R.

Integration inspection also found that the candidate bootstrap command
invalidated coverage but missed `include_str` consumers. The ordinary capture
script's existing invalidation code is now shared with bootstrap capture;
bootstrap invalidates embedded consumers before starting. The final recapture
completed with this shared invalidation path; the claim gate rebuilt those
consumers from the new captures. The unintegrated NS1-R Justfile recipe,
invalidation extension and four candidate test sources were parked under
`.tmp/ns1-r/audit-20260908/parked-wip/` during the gate. They remain outside
this commit and are restored to the worktree before the requested pause.

Earlier failures are retained in `.tmp/ns1-r/audit-20260908/`: rejected
historical-cache capture; wrapped initializer-result rejection; incomplete
verdict normalization; a missing source-tree offer in the first consumer
build; and a negative-control API mistake (condition metadata is returned
only when `tryReplay` is asked to create a named declaration). The corrected
negative controls passed in isolation and in the complete MOD module.
Diagnostic sketches are not counted as replay receipts.


### Final validation and disposition

`just claim-gate` completed with **TRUE_EXIT=0**. The exact receipt is
`.gate-runs/32b31c9-20260908T074800Z.log` (the filename names the pre-fix
HEAD; the gate ran on the staged repair). All executable edits and final
production recaptures preceded this run; only completion documentation
changed afterward.

- Default build: 3302 jobs; tests: 3263 jobs; coverage target: 3202 jobs.
- Baseline: **116/116 unconditional, 0 conditional, 29 books**; the
  generated coverage report matches the unchanged golden byte for byte.
- Existing products: **21 mirrors** pass the replay seam gate and existing
  axiom, purity and name checks. No new native mirror is claimed.
- The new bootstrap scope/source/axiom tests, maintained reciprocal and MOD
  imports, missing-dependency controls and source-reference checks all pass.
- Provenance: **112 production captures** at `fd27e590`, including both
  freshly generated bootstrap windows. Existing controls and the new
  missing-bootstrap-receipt control pass.
- The independent differential suite run during this audit reports
  **559 match, 138 unsupported, 7 known-bug, 32 refuse, 0 FAIL** in
  `.tmp/ns1-r/audit-20260908/differential.log`. The subsequent fix changes
  proof construction and capture, not numeric interpreter behavior.

Final recapture and chronology receipts are
`.tmp/ns1-r/audit-20260908/final-bootstrap-recapture.log` and
`final-chronology-control.log`. The latter still reports the separate
unproved RATIONALP-UNARY-- verdict; it does not offer a self-rule.

The parent independently verified and repaired the sole blocking finding.
The revised candidate satisfies the repository's local merge gate. This
was one broad adversarial review plus parent verification; it is not an
exhaustive semantic proof, a cold clone/build, or a promotion of producer
`30503a673a7c`. The ordinary linear-row construction, remaining bootstrap
staging and three BVCHOP mirrors stay open in the existing plans. Work pauses
after the local fix commit; main remains unchanged pending explicit sign-off.

Full-gate receipt SHA-256: `62956b0c360a7a6d082226a3cd0c82d032d215d009edd6a831c36ca2d1b4fa9a`.
