# NS1 C0 — canonical complex rationals and migration design

Dated 2026-09-05. Execution branch `mdd/ns1-bvchop`, based on approved docs
commit `b452b70`; ACL2 fork `e8d78e513d6867d04002f0df644da1723cc96e89`;
Lean 4.33.0. Governing contract: [NS1 charter](../plans/2026-09-05_bvchop-foundation-charter.md).

**Status: reviewed design adopted for C1.** The value model has not changed.
Both authorized C0 reviews are complete; the primary verification and design
decisions below address their findings. The fresh baseline gate passed with
`TRUE_EXIT=0` in `.gate-runs/b452b70-20260905T221458Z.log`: 116/116
unconditional theorem rows, byte-identical golden, existing product checks
passed. Coverage consumers were invalidated before this run.

## Driving artifact and native result

The worktree has its own ACL2 checkout and freshly built saved image. Its
system-book directory is the worktree's `acl2/books/`, verified in the banner.
The initial Lake cache and captured regression corpus were copied from the
assessed checkout; they are independent files, not shared writable artifacts.
`scripts/invalidate-coverage.sh` was run before the baseline gate.

Fresh capture, without changing the book or hints:

```sh
TMPDIR="$PWD/.tmp" just build-acl2
CAPTURE_WORKER=1 OUTDIR="$PWD/.tmp/ns1" TMPDIR="$PWD/.tmp" \
  timeout 120 scripts/capture-proof-log.sh acl2/books/kestrel/bv/bvchop.lisp
lake env .lake/build/bin/acl2lean-replay --dump .tmp/ns1/bvchop.proof-log
```

The capture completed with 436,039 lines and 116/116 QED/local-theorem
events. Source SHA256:
`19f0ebcdb29acab657919dcd4c2a5db46feaef096e70f8363f7bcddb400b1a79`.
Log SHA256:
`ea9a334b829250b68f2af7872731e3567793f766bbdd79a851249e84de287902`.
The dump exits 1 with `Parse error: unrecognized reader macro: #C`.
Capture log, full sidecar and dump output are under `.tmp/ns1/`. The selected
proof trees cannot yet be inspected; this is an ingestion prerequisite,
not a claim about their downstream replay mechanisms.

The native contracts remain `wordClipBound`, `wordClipIdempotent`, and
`wordClipIdentity` from the charter, with `wordClip w x = x % (2 : Int)^w`.
They are now declarations in
[`Mirrors/WordOps.lean`](../../ACL2Lean/Mirrors/WordOps.lean), without proofs.
`lake build ACL2Lean.Mirrors.WordOps Tests.MirrorNameCheck` passed; all 59
spec names passed the existing collision check (`.tmp/ns1/c0-spec-build.log`).
They use only native Lean definitions and integer/natural types. Every final
proof must consume its corresponding ACL2 theorem through replay. The numeric
model, capture, reconstruction, and proof generators are outside these
products' mathematical trust base once their full bridges are checked.
That does not certify attribution, replay fidelity, or unexercised semantics.

## Representation decision

Preserve `Number.int` and `Number.rational` and their existing BUG-012
canonicity invariant. Add one constructor:

```lean
| complex (real imag : Rat) (imagNonzero : imag.num ≠ 0)
```

Use Lean core's `Rat`, explicitly imported from `Init.Data.Rat.Basic`, for
the two components. Its type stores a positive denominator and reduced
numerator/denominator; see the pinned toolchain's `Rat` declaration. These
are rational components, so nested complex values are unrepresentable.
The nonzero-imaginary proof prevents a second representation of a rational.
Equality compares component data; invariant proofs are irrelevant.

A smart constructor `fromParts` takes two canonical rationals. When
`imag.num = 0`, it returns the real component using the existing integer or
proper-rational constructor. Otherwise it returns `Number.complex` with the
nonzero proof. Conversion from `Rat` inspects the denominator: 1 gives an
integer; otherwise positivity and reducedness prove the existing `canonRat`.
This keeps BUG-012's unique representation guarantees without requiring a
new invariant on environments or theorem statements.

A scratch prototype of this datatype, `fromRat`, and `fromParts` typechecks
in `.tmp/ns1/canonical-complex-prototype.lean`. Its normalization checks
include `(2/4, 0/3)` collapsing to `1/2` and `(0,1)` remaining nonzero.
Both smart constructors report only `[propext, Quot.sound]`. This validates
the proposed type/construction interface, not the migration or a book proof.

Using core `Rat` avoids maintaining a second rational normalization library.
Replacing all of `Number` with a different top-level representation would
unnecessarily change existing literal/proof interfaces. Raw unconstrained
pairs, an opaque complex token, and recursive complex components do not meet
the representation contract.

## Semantics from the pinned ACL2 source

Primary sources are `acl2/axioms.lisp` and `acl2/interface-raw.lisp`, not
ordinary ordered-field intuition. Relevant definitions and completion axioms:

| Operation | Required behavior | Source |
| --- | --- | --- |
| Arithmetic and reciprocal | Exact complex-rational arithmetic; nonnumeric arguments complete to zero; inverse of zero is zero | `axioms.lisp:25380` onward; `interface-raw.lisp:873` onward |
| `COMPLEX` | Each non-rational argument, including a complex argument, completes to rational zero; zero imaginary part collapses | `axioms.lisp:25537` |
| Parts and recognizers | Complex numbers satisfy ACL2-NUMBERP and COMPLEX-RATIONALP, not RATIONALP; nonnumbers have zero real/imaginary part | `axioms.lisp:4377` onward, `25717`, `25760`; `interface-raw.lisp:974` onward |
| Numeric `<` | After nonnumbers complete to zero, compare real parts, then imaginary parts | `axioms.lisp:25444`; `interface-raw.lisp:904` |
| `alphorder` / `lexorder` | All rationals precede all genuine complexes, then characters, strings, symbols; within complexes compare real part then imaginary part | `axioms.lisp:27036` |
| `ACL2-COUNT` | A complex value counts as 1 plus the counts of its real and imaginary components | `axioms.lisp:2355` |
| Constant term-order weight | Complex case visits imaginary part then real part with the source's accumulator/call increments and limits | `linear-a.lisp:1492` |

The two orders differ on mixed rational/complex inputs. They must not be
implemented by one undifferentiated comparison of numeric values.

Twenty-one labeled evaluations were run with the freshly built ACL2 image,
`ACL2_CUSTOMIZATION=NONE` and `(set-guard-checking nil)`. Inputs and transcript:
`.tmp/ns1/numeric-probes.lisp` and `.tmp/ns1/numeric-probes.out`. Selected
observed outputs, each checked directly in the transcript:

| ACL2 expression | Result |
| --- | --- |
| `(equal '#C(2/4 0/3) '1/2)` | `T` |
| `(complex '#C(1 2) '#C(3 4))` | `0` |
| `(complex 'foo 2)` | `#C(0 2)` |
| `(+ '#C(2/3 -4/5) '#C(1/3 4/5))` | `1` |
| `(* '#C(2 3) '#C(4 -5))` | `#C(23 2)` |
| `(/ '#C(2 3))` | `#C(2/13 -3/13)` |
| `(/ '#C(2 3) '#C(4 -5))` | `#C(-7/41 22/41)` |
| `(/ '#C(2 3) 0)` | `0` |
| `(numerator '#C(2/3 4/5))` / `(denominator '#C(2/3 4/5))` | `0` / `1` |
| `(< '#C(0 -1) 0)` | `T` |
| `(lexorder 100 '#C(-2 3))` | `T` |
| `(lexorder '#C(-2 3) 100)` | `NIL` |
| `(acl2-count '#C(2/3 -4/5))` | `15` |

The remaining probes cover case-insensitive `#c`, parts, fix/ifix/nfix,
recognizers, parity, powers (including zero/noninteger exponents and negative
powers), completion on symbols, and decrease to both complex components.
These are observed ACL2 outputs, not yet Lean differential successes.

## Coherent migration, in dependency order

1. **Syntax and literal construction.** Add the canonical constructor and
   component conversion helpers. Extend both value printers, expression
   reflection, translation output, and term-order weight. Parse `#C`/`#c`
   using the real reader shape: exactly two rational components in a proper
   list. Reject malformed/non-rational components instead of applying the
   *function* COMPLEX's completion at read time. Test the precise ACL2 reader
   acceptance boundary before landing this parser arm.
2. **Core operations.** Distinguish rational extraction/completion from
   real/imaginary decomposition of any numeric value. `toRat` may continue
   to mean rational-or-zero; it must not silently become realpart, and it is
   no longer injective on all numbers. Extend arithmetic, inverse, power,
   comparisons, parts, COMPLEX and recognizers with canonical outputs.
   Preserve the existing rational arithmetic path where useful for reduction
   and proof compatibility. Centralize the duplicate UNARY-/ and unary `-`
   dispatch formulas through their Logic definitions. Update builtinNames
   and required ground-zero agreement registration if COMPLEX is added.
3. **Ordering proofs.** Extend the atomic class ordering with the genuine
   complex class. Replace `LexorderOrder.number_eq_of_cross_eq`'s false
   all-number injectivity premise with rational-specific correspondence and
   componentwise equality for complexes. Reprove reflexivity, antisymmetry,
   transitivity and totality without importing a conflicting String order.
   The structural cons proofs should consume these general atomic facts.
4. **Type facts and primitive lemmas.** Make type-set index 6 inhabited.
   Replace `tsAcl2MaskOk` and its caller by the ordinary containment check.
   The true `< v 0` type bound must include complex values (112, not 48).
   Do not mechanically complement that new bound for the false branch:
   type-set index 6 contains complexes on both sides of zero. Review every
   numeric mask implication and its registry together, including arithmetic
   outputs, negation and complements. Separate RATIONALP/ACL2-NUMBERP twins
   in `EvalOpt`, `Replay/Lemmas/Derived`, and `Driver/NodeCore/Ctx`.
5. **Actual numeric descent.** Once COMPLEX-RATIONALP can return T, the
   totality and induction walkers' generic absurdity checks cease to apply
   to that branch. Replay its real cases. `consCount` is zero on all atoms
   and cannot justify recursion to realpart/imagpart. Keep its structural
   meaning; use a suitable count interpretation for these calls, with
   kernel-checked decreases licensed by the actual emitted obligations.
   The proposed interpretation is the ACL2-value count: magnitude for
   integers, numerator magnitude plus denominator for proper rationals,
   1 plus both component counts for complexes, string length, and structural
   sum for conses. Count convergence and recorded-admission consumers must
   agree with this interpretation where they use it. Extend the measure and
   decrease dispatch coherently; an extra REALPART name in the old
   consCount chain classifier would not establish the required decrease.
6. **Restore and exercise consumers.** Repair all affected generic proofs,
   current generated exec/waypoint/mirror users, and the differential corpus.
   Re-run the complete BVCHOP parser/reconstructor, inspect its real tree,
   and drive subsequent work from the selected theorem's next actual node.
   No source/log edits or hand proofs of ordinary book dependencies.

Initial source sweep (`rg -l 'toRat|\.rational|Number\.int|complexRationalp'
ACL2Lean Tests`) identifies 30 files; that is a navigation aid, not an
exhaustive impact certificate. In addition to the files above, inspect
`Imported/LiftingRel`, `Imported/ExecGen`, `MirrorProofs/OrderBridge`,
`Replay/Lemmas/{TpClosure,Discharge,Judgments,Totality,MeasureMu}`, and the
driver's `Discharge`, `NodeCore/Compose`, `TsFacts`, `Decrease`, `Totality`,
and `Waterfall/Induction`. Explicit constructor cases can be compiler-found;
wildcard cases and propositions made false by the enlarged domain need
source review. The pattern map's `cov-complex` and `cov-complex-defun`
records identify further reader/capture probes to reconcile with fresh runs.

## Checks and review questions

The new differential corpus will cover canonicalization, both orders,
all affected primitives, completion outside guards, mixed rational/complex
arithmetic, cancellation to a rational, negative powers and division by
zero. Reader rejection tests need per-form isolation. Promote existing
unsupported complex rows only after real Lean/ACL2 agreement. Pin newly
found fidelity bugs in the canonical index; BUG-009 closes only when its
full documented scope and dependent domain restrictions are repaired.

Add focused checks for index 6 and both signs of complex comparison, literal
reflection/printing, and the count/induction cases that used to be vacuous.
Use real captured books for replay checks; do not construct synthetic logs
or proof nodes. Generic core-logic proofs are permitted, including rational
component algebra. Book-specific results always enter through replay.

C0 reviewers independently inspect (a) canonical numeric semantics against
the ACL2 source and (b) consequences for type sets, measures, replay and
existing products. They should challenge the representation and executable
probe evidence, identify remaining false invariants, and test feasibility
of the changed count route. Findings must cite source locations and state
what was not verified. The primary agent verifies findings before applying
them. No new proof machinery policy or additional audit allocation is
authorized by this design note.

C1 requires a coherent model and restoration of all previous products;
getting past `#C` alone is insufficient. NS1's final acceptance remains the
three native proofs, complete supporting obligations, preserved baseline,
authorized final review, full claim gate, and independent product validation.

## Primary verifications during C0 review

- **Reader completion:** independently reproduced the reviewer's finding
  that `(quote 1/0)` prints `0` in the unchanged Lean CLI while ACL2 emits
  READER-ERROR / DIVISION-BY-ZERO. Recorded as BUG-028 in the canonical bug
  index. The parser's zero-denominator acceptance must be repaired before
  reusing that path for complex components. Arithmetic division-by-zero
  completion remains a separate, valid behavior.
- **Both comparison directions:** confirmed `inTs_zero_lt_true` at
  `TsAlgebra.lean:550` and `tsFactOf` at `TsFacts.lean:96` currently return
  mask 14; the enlarged domain needs 78. The false `< v 0` branch can still
  include all complex values, so its existing -49 mask is not replaced by
  the complement of 112. `tsTestNilOf` and its disjointness lemma also need
  the 112 true-mask update.
- **Count bootstrap:** confirmed `mkRecTermInfo` at `Decrease.lean:541`
  requires already available totality and a nonnegative-integer TP for the
  interpreted count. That route cannot supply ACL2-COUNT's own missing
  totality. Its complex-component descent needs a directly proved registry
  interpretation first. The old consCount interpretation cannot justify it.
  Independently reran the reviewer's count prototype: canonical component
  conversion and both component decreases typecheck with only
  `[propext, Quot.sound]`; output is
  `.tmp/ns1/c0-count-primary-verification.out`. This is numeric feasibility,
  not world convergence or a replay proof.
- **Sum-count consumer:** confirmed `Provers.lean:149`–151 hardcodes
  consCount twice, separately from `muHeads`. If sumCount's registered
  interpretation changes, this consumer must use it as well.
- **Term weight:** independently reproduced the reviewer's rational
  recursion-limit finding in the unchanged Lean model and fresh ACL2.
  Recorded as BUG-029. A complex weight implementation must preserve the
  source's recursive call checks in its rational components, not inherit
  the existing flattened rational shortcut.
- **Addition normal forms:** confirmed the unconditional rational-only
  `plus_eq` and `plus_mkNumber_left` at `Derived.lean:536` and `:636`.
  Under the proposed semantics their right sides lose a complex operand's
  imaginary part, while the left sides preserve it. Replace those helpers
  with properly scoped rational forms or componentwise forms; reprove
  unconditional primitive associativity on the complete numeric domain.
  The stored-rule consumers in GzRules must retain their current statements.

## Decisions after the two C0 reviews

Both authorized reports are available:
[numeric semantics](../audits/2026-09-05_ns1-c0-numeric-review.md) and
[migration consequences](../audits/2026-09-05_ns1-c0-migration-review.md).
The representation is retained. The findings above are in-scope repairs;
they introduce no new trust or proof-mechanism policy. The baseline and
implemented native-spec checks have passed. The charter records the full
C0 gate receipt and checkpoint status.

The count implementation contract is now explicit:

- Add a separate `SExpr.valueCount` with the exact numeric/component count
  described above. Keep `SExpr.consCount` structural and unchanged.
- Use valueCount for the replay registry's `.count` and `.sumCount` rows.
  Keep `.len` and `.nfix` unchanged and retain the recorded route for
  measures it already handles once their totality/TP prerequisites exist.
- Make the sum totality consumer read its registry heads. Supply valueCount
  counterparts for the structural, EVENS/ODDS and ordinal decrease facts
  actually consumed by these replay rows. The convergence proofs underlying
  CountSim may retain their independent structural induction; equality
  transport of a decrease should be parametric in the chosen Nat measure.
- Add realpart/imagpart decreases under the carried COMPLEX-RATIONALP fact,
  and admit them in route classification only alongside matching decrease
  proofs. The existing exact emitted-obligation and ruler checks remain.
  This gives ACL2-COUNT's totality and TP a noncircular bootstrap.
- Existing generated execs may keep their structural termination measures;
  those are independent proof bookkeeping. Extend their measure support only
  when a demanded generated function has the new component calls.

For literal reflection, use explicit smart-constructor applications with
integer/natural component literals, following the checked prototype; do not
depend on default `Repr Rat` for ACL2 printing. Reader tests must include
the review's accepted proper dotted list and normalized inner-`#C` spellings,
as well as rejected genuine nested complexes and zero denominators. The
host's accepted numeric dispatch prefix (`#2C`) is a separately classified
reader frontier unless demanded; it is not silently accepted as something
else or confused with nested complex representation.
