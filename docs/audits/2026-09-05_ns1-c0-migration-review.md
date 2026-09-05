# NS1 C0 review — migration consequences

Dated 2026-09-05. Authorized C0 reviewer 2 of 2, on `mdd/ns1-bvchop` in
`.claude/worktrees/ns1-bvchop`, against the numeric-design candidate based on
`b452b70`. Scope: type sets, numeric lifts, ordering and existing products,
and the count/totality/induction migration. No implementation files changed,
no competing Lake build, no additional agents, no commits.

**Assessment:** the proposed canonical numeric representation admits the
required complex-component decreases. The numeric part of the count proposal
has been typechecked below. The design still needs an explicit bootstrap and
dispatch contract: a recorded-count fallback cannot establish the count
function's own unconditional totality. Two all-value rational-normal-form
lemmas also become false, beyond merely acquiring a new constructor case.
These are repairs within the agreed NS1 scope, not a reason to abandon it.

The primary agent has independently confirmed the count bootstrap and
positive comparison-mask findings and added a verification addendum to the
design note. This review records the original candidate and source evidence;
it does not certify the later implementation.

## Evidence and limits

- Read `CLAUDE.md`, the NS1 charter, the numeric-design candidate, and the
  implementation sites cited below. Source locations are relative to this
  worktree. **Verbatim** denotes source text or observed tool output;
  **inference** denotes a consequence reconstructed from that evidence.
- Inspected the real, complete `.tmp/ns1/bvchop.proof-log`. Its raw ground-zero
  ACL2-COUNT definition and admission clauses at line 433233 contain both
  component calls; its TP record is at line 433235. The complete parser still
  fails on `#C`, so these are raw recorded obligations, **not a reconstructed
  proof-tree inspection**. No log was edited or filtered for replay.
- Inspected `acl2/axioms.lisp:2355`–2388 and the primary agent's actual ACL2
  probe inputs/output. The count formula is a core ACL2 definition, with its
  bootstrapped termination explicitly visible in that source. The probe
  transcript gives `(COUNT (6 15 2))` and `(COUNTS-VERSUS-PARTS (T T))` at
  `.tmp/ns1/numeric-probes.out:50`–51.
- Ran isolated `lake env lean` checks described below. The primary agent's
  full baseline gate was running during review; this reviewer did not claim
  its exit status or a full-corpus result.

## M1 — make the count bootstrap and interpretation choice explicit

**Priority: required design detail before relying on the migration.**

**Verbatim evidence:**

- `ACL2Lean/Count.lean:18`–21 sets every atomic `consCount` to zero.
- `ACL2Lean/Replay/Lemmas/MeasureMu.lean:113`–118 maps both `.count` and
  `.sumCount` to `SExpr.consCount`.
- `ACL2Lean/Replay/Driver/Totality.lean:407`–420 and
  `ACL2Lean/Replay/Driver/Waterfall/Induction.lean:725`–745 currently avoid
  walking a truthy branch only when its test is definitionally NIL; their
  comments name the complex branch of ACL2-COUNT.
- The real capture at `.tmp/ns1/bvchop.proof-log:433233` records the two
  conclusions `(O< (ACL2-COUNT (REALPART X)) (ACL2-COUNT X))` and
  `(O< (ACL2-COUNT (IMAGPART X)) (ACL2-COUNT X))`, under the non-cons,
  non-rational, complex branch. These are actual coverage licenses for the
  new decreases, not imagined call sites.
- `ACL2Lean/Replay/Driver/Decrease.lean:541`–566 requires the count function's
  totality and its standard nonnegative-integer TP to assemble the recorded
  route. `ACL2Lean/Replay/Lemmas/Judgments.lean:1468`–1482 defines
  `interpCount` by convergence of the world's count function; it is not an
  independently executable numeric count.
- `ACL2Lean/Replay/Driver/Provers.lean:149`–151 hardcodes the sum's two
  `SExpr.consCount` applications. The single-variable totality route reads
  `row.muHeads` at lines 182–195; `TpProver.lean:751`–770 and
  `Waterfall.lean:327` also consume that registry.

**Inference:** making COMPLEX-RATIONALP meaningful removes the current
absurdity proof. Falling back to `interpCount` then creates a prerequisite
cycle for ACL2-COUNT itself; using a visible totality hypothesis would retain
debt, not finish the repair. The coherent route is an independently defined
Nat-valued measure with proved complex-component decreases, used by the
generic totality and TP walkers on the emitted calls. Once those proofs
exist, the recorded route may consume their unconditional results for later
functions.

The candidate's exact ACL2-value count is viable for this purpose. A separate
count is necessary: redefining `consCount` to count numeric magnitudes would
destroy its advertised structural meaning. Specify which measure-table rows
use the new count. If `.sumCount` is moved with `.count`, update the hardcoded
sum totality site as well. If structural sum measures remain, record that
choice and preserve their existing matching decrease proofs; a bookkeeping
measure need not numerically equal ACL2-COUNT to prove the same final theorem.

**Typechecked feasibility:**
`.tmp/ns1/c0-migration-count-prototype.lean` extends the proposed datatype
prototype with:

```lean
def rationalCount (q : Rat) : Nat :=
  if q.den = 1 then q.num.natAbs else q.num.natAbs + q.den

def numberCount : ProposedNumber → Nat
  | .int n => n.natAbs
  | .rational n d _ => n.natAbs + d
  | .complex r i _ => 1 + rationalCount r + rationalCount i
```

It proves that `fromRat` preserves `rationalCount`, then proves both realpart
and imagpart strictly decrease `numberCount` on every proposed complex
constructor. It also checks the observed count 15 for `#C(2/3 -4/5)`.

```sh
TMPDIR="$PWD/.tmp" lake env lean .tmp/ns1/c0-migration-count-prototype.lean
```

Final exit: **0**, with no warnings. The three new lemmas' `#print axioms`
output is `[propext, Quot.sound]`. An initial scratch attempt unfolded the
count too early and failed; the final proof preserves the `fromRat` bridge
until rewriting. No failed proof is counted as a result.

**Still unwired / not verified:** this is a representation-and-measure
prototype, not an ACL2Lean theorem or replay artifact. It does not establish
world-function convergence, ACL2-COUNT's TP, or any selected BVCHOP result.
The real implementation must connect `Logic.realpart`/`imagpart` to the
canonical constructor, supply the new count on all SExpr cases, and carry
the chosen measure through totality, TP, and IH decrease generation.
`Decrease.lean:253`–293 hardcodes structural chain proofs;
`Decrease.lean:334`–340 and `:382`–398 consume structural EVENS/ODDS/ordinal
decreases through `CountSim.count_lt_of_eq` (`CountSim.lean:96`–99).
Those sites cannot supply a different measure's inequality without an
appropriate generic bridge or replacement facts. Existing generated execs
may retain independent structural measures when their correspondence proofs
still check; `Imported/ExecGen.lean:1160`–1165 explicitly generates those
measures. The complete restored proof path has not been built.

## M2 — migrate the positive mask and all consumers of the negative mask

**Priority: required semantic repair; candidate names only one polarity.**

**Verbatim evidence:** `TsAlgebra.lean:549`–551 states
`0 < v → InTs 14 v`; `Driver/TsFacts.lean:94`–96 registers the same mask.
The ACL2 probe at `.tmp/ns1/numeric-probes.lisp:19`, with its transcript at
`.tmp/ns1/numeric-probes.out:48`, observes `(< 0 '#C(0 1)) = T` and
`(< '#C(0 -1) 0) = T`. The exact comparison source is
`acl2/axioms.lisp:25444` onward. `TsFacts.lean:124` separately registers mask
48 for proving a test NIL; its theorem is
`TsAlgebra.lean:634`–637. The candidate at
`docs/notes/2026-09-05_ns1-numeric-design.md:150`–157 explicitly names
48→112 but leaves the positive branch to its general review instruction.

**Inference:** once index 6 is inhabited, the positive theorem must admit
complex values as well: **14→78**. Both complexes on either side of zero
have the same basic type index. The negative true-mask update **48→112**
must reach `tsTestNilOf` and `logic_lt_zero_nil_of_ts_disjoint`, not only
`tsFactOf` and `inTs_lt_zero_true`. The existing false-side mask **−49** can
remain: it excludes negative rationals and integers while retaining complex
values. Replacing it mechanically by `~112 = -113` would be false for a
positive complex value.

**Required check:** prove the revised implications and check registry and
containment consumers together, including deleting the index-6 exemption
at `TsFacts.lean:161`–164. Exercise a positive complex and a negative complex
against the exact same type-set index. Mask widening itself must not stand
in for a proof of an emitted leaf.

**Not verified:** no new `tsIndex` implementation exists yet, so the revised
type-set propositions were not typechecked. I inspected the real ACL2 probe
transcript rather than independently rerunning that ACL2 session. I did not
claim this is an exhaustive census of future primitive type-set cells.

## M3 — replace false rational normal forms without weakening numeric rules

**Priority: required proof migration, beyond constructor-case repair.**

**Verbatim evidence:** `Replay/Lemmas/Derived.lean:536`–539 states
unconditionally that `Logic.plus a c` is a `Logic.mkNumber` formed from the
two `Logic.toRat` pairs. `Derived.lean:636`–639 similarly treats addition of
a rational to an arbitrary SExpr as a rational result. The unconditional
associativity theorem at `Derived.lean:663`–673 depends on those forms.
`Replay/GzRules.lean:342` and `:436` consume associativity at arbitrary
environment values. The proposed design expressly retains `toRat` as
rational-or-zero (`numeric-design.md:135`–140).

**Inference:** both normal-form statements become false on complex inputs.
For example, adding zero to `#C(0 1)` yields that complex value, whereas
their rational-only right side yields zero. This cannot be fixed by adding
an empty new constructor case. Restrict the rational helper statements to
their actual rational/completed-nonnumeric domain or replace them with
componentwise normal forms; preserve the original *unconditional* addition
laws by proving them about the whole numeric model. Adding rationality
premises to a replayed commutativity/associativity rule would weaken it and
change the stored-rule contract.

The nonnegative-integer DP lift has a different status. Its conclusion at
`Replay/Lemmas/Discharge.lean:537`–541 is explicitly licensed by INTEGERP,
so complex inhabitants cannot satisfy its premise. Its statement remains
appropriate; the new constructor requires a refutation case. Likewise,
`Imported/ExecGen.lean:159`–164 explicitly assumes `NatValued` on both sides
of its order lift. No widening of that native arithmetic domain is needed.

**Not verified:** the representation has not been installed, so the false
new-domain specializations cannot yet be run in ACL2Lean. The counterexample
is an inference from the specified operations and ACL2 source semantics,
corroborated by the real mixed-addition probe at
`.tmp/ns1/numeric-probes.out:45`. I did not attempt the entire replacement
associativity proof. The baseline DP lift's axiom receipt was checked below.

## Reviewed consequences and fidelity boundaries

The existing native products need no statement changes merely because
complex values become representable. The load-bearing generic ordering
does require repair. `MirrorProofs/OrderBridge.lean:29`–48 constructs
`TotalOrder SExpr` from all four ACL2 lexorder laws; its integer restriction
at lines 52–56 consumes the concrete atomic ordering. The candidate correctly
identifies the now-false all-number cross-product injectivity lemma at
`LexorderOrder.lean:103`–107. I found no further statement-level obstruction
to keeping the Int and Option Int products unchanged. This is a source-based
inference, not post-migration regression evidence.

I independently ran the following isolated receipt check, using already
built worktree imports and no Lake build:

```sh
TMPDIR="$PWD/.tmp" lake env lean .tmp/ns1/c0-migration-existing-axioms.lean
```

Exit **0**. `.tmp/ns1/c0-migration-existing-axioms.out` records:

| Checked declaration | Axioms observed |
| --- | --- |
| `ACL2.lexorder_antisymm` | `propext, Classical.choice, Quot.sound` |
| `ACL2.Replay.dp_nonneg_int_of_tp` | `propext, Quot.sound` |
| `ACL2Lean.MirrorProofs.instTotalOrderSExpr` | `propext, Classical.choice, Quot.sound` |
| `ACL2Lean.MirrorProofs.isort_ordered_int` | `propext, Classical.choice, Quot.sound` |
| `ACL2Lean.MirrorProofs.permWitness_complete_optint` | `propext, Classical.choice, Quot.sound` |
| `ACL2Lean.MirrorProofs.app_assoc_int` | `propext, Classical.choice, Quot.sound` |

These are sampled **pre-migration** receipts, not a new 21-product audit.

Three specificity/fidelity risks should remain explicit during C1/C2:

- **Do not make ACL2-COUNT a builtin shortcut to avoid its new branch.**
  `MeasureTable.lean:34`–38 distinguishes proof bookkeeping from the emitted
  obligations that license it. A separate Nat measure and primitive component
  decrease facts fit that contract. Replacing the world's recorded count
  definition or a waterfall proof by an evaluator shortcut would require a
  different justification. No such shortcut is proposed in the candidate.
- **Do not repair route selection by names alone.**
  `NodeCore/Ctx.lean:582`–595 labels the existing destructor-reach test a
  calibrated heuristic, while `Decrease.lean:207`–217 uses it to discriminate
  the registry/recorded routes. The new complex component route must come
  with matching measure expressions, exact emitted obligations, and proved
  branch facts. The names REALPART and IMAGPART alone do not license descent.
- **Restoring primitive algebra is not permission to hand-prove included
  book dependencies.** The capture labels `REALPART-OF-*` and `IMAGPART-OF-*`
  as `:SOURCE :INCLUDE-BOOK` at lines 823 and 827. Existing
  `GzRules.lean:384`–436 contains hand-proved arithmetic-3 alias rules; its
  presence is not a template for adding a per-rune implementation for each
  new included arithmetic theorem. Definition correspondence for complex
  multiplication is generic core semantics; using it as an alternative
  proof of a required named book dependency would need to be rejected or
  replaced by that dependency's replay. Whether those particular rules are
  in the three targets' selected proof closure is **not verified** while
  reconstruction is blocked. This is a prospective fidelity risk, not a
  claim that the new design has already introduced such a violation.

The remaining acceptance evidence belongs to the implementation: real
reconstructed trees, count totality and TP without residual hypotheses,
restored existing statements, and all three new mirror proofs. The count
prototype demonstrates a concrete local path through the previously empty
numeric branches; it does not shorten that acceptance contract.
