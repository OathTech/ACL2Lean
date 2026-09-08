# Fidelity bug backlog — canonical index

This is the SINGLE canonical list of known fidelity bugs: places where the Lean
interpreter / trusted core diverges from real ACL2. Total faithfulness to ACL2
is the goal, so every mismatch is definitionally a bug and belongs here.

Terminology per `docs/LEXICON.md` (canonical): *replayed statement* /
*waypoint* / *mirror* are three distinct things — entries below use them
in that sense.

**Robustness contract (enforced by `scripts/check-bugs.sh`, run in `just ci`):**
every `open` bug that is `Pinned-by: differential` MUST have at least one live
`;@ known-bug bug:BUG-NNN …` entry in the differential corpus, and every
`bug:BUG-NNN` tag in the corpus MUST reference an `open` bug here. This keeps
the prose index and the self-enforcing differential ratchet in sync — a bug
cannot be silently fixed-and-forgotten (the ratchet FAILs when behavior
changes) nor silently dropped from the index (the cross-check FAILs). Bugs that
CANNOT yet be pinned in the differential (e.g. a builtin not wired into
`callBuiltin`) are `Pinned-by: none (<reason>)` and listed all the same.

Entry format (keep machine-parseable — the checker reads the `BUG-NNN`,
`Status:`, and `Pinned-by:` fields):

```
## BUG-NNN — one-line summary
Status: open | fixed
Pinned-by: differential | none (<reason>)
<prose: what diverges, ACL2's behavior, root cause, fix notes>
```

---

## BUG-059 — empty clausify call records activate legacy assumption folds
Status: open
Pinned-by: none (actual minus-book replay mismatch)

The parser represents both an absent CALL-ASSUMPTIONS field and an emitted
empty list as `[]`. The consumer therefore activates legacy context
reconstruction for a recorded traversal with no successful assumption calls.
In INTEGERP-OF-- and RATIONALP-OF--, Subgoal 2's second literal, it replaces
the nested recognizer of X with NIL; ACL2's leaf retains that recognizer.
The exact leaf check rejects (`c2-minus-negation-frontiers.log`).

Diagnostic source `rewrite.lisp` distinguishes unchanged PUSH terms in
`if-compile` (3336–3433) from CALL rebuilding in `call-stack` (3973 onward).
The leaf observer records the actual call list, including NIL. Preserve its
presence through parsing and tree reconstruction, and select the recorded
consumer even for the empty list. Only genuinely absent legacy fields may
use the pre-existing fallback. Both actual composer chains now kernel-check
with accepted axioms; deleting the field reproduces their mismatches
(`c2-clausify-empty-call-controls.log`). The 24 bootstrap/component dependency
replays and affected builds pass. Full integration remains open; the whole
minus proofs now reach their separate verdict-leaf frontiers.

## BUG-058 — clausify cleanup omits its selected clause reductions
Status: open
Pinned-by: none (proof-capture evidence, not interpreter values)

Literal-clausify records fired flags for the Satriani replacement pass and
the general subsumption loop, but omits which clause was deleted or reduced
to which result. In strict-helper Subgoals 7' and 6', six false leaves become
six final branch windows; four raw segments have no exact final match, and
several final branches are falsified by the same path. The existing unique
branch selector correctly refuses the ambiguous link.

Emit the selected clause reductions where ACL2 performs them, including
discarded-new-clause cases and recursive-pass ordering. Follow that recorded
mapping and kernel-check the final segment's literal facts. Do not pick an
arbitrary matching branch or reconstruct the missing search. Source:
diagnostic `rewrite.lisp`, `quick-and-dirty-subsumption-replacement-step`,
`if-interp-add-clause`, and `subsumption-replacement-loop`. Actual tree/link
receipt: `.tmp/ns1/c2-strict-split-link.log`; whole replay fails in
`.tmp/ns1/c2-strict-with-complex-negation.log`.

Diagnostic producer `df7a28e38c` now retains the selected before/after clauses
at the actual cleanup operations, with a local history on each existing
marker. The unchanged times prefix captures 38/38; all 498 original events
are identical after removing only the new REDUCTIONS fields. Its 121 actual
cleanup markers parse, and nine malformed-record controls reject. The tree
attaches only operations occurring after a leaf was generated. Following
those operations identifies one exact branch for each of the twelve false
leaves in 7'/6'; fourteen used-edge removal controls lose that final branch
(`c2-clausify-reduction-structure-controls.log`). Subgoal 6' now has a checked
conditional proof with five ordinary rules remaining and accepted axioms;
seven replay mutations reject (`c2-clausify-reduction-replay-controls.log`).
Subgoal 7' initially crossed branch selection but retained an assumed verdict
leaf. The subsequent component-sign normalization closes that leaf, yielding
a checked conditional 7' declaration with five ordinary rules still needed
(`c2-component-sign-subtrees-ordered.log`).
Production promotion remains open; no unconditional helper result is claimed.

## BUG-057 — simplify-clause omits its selected HIDE removal
Status: open
Pinned-by: none (proof-capture evidence, not interpreter values)

After a rewrite pass makes no change, ACL2's `unhidden-lit-info` selects a
previously fertilized equivalence inside NOT/HIDE. `simplify-clause1` removes
that HIDE at the selected position and returns the modified clause, citing
HIDE's definition. The capture does not record this selected transformation.

The actual IMAGPART-OF-*-OF-I proof reaches Goal'5' after the retained-equality
FERTILIZE step. Every literal chain there is unchanged; the child Goal'6'
removes HIDE from its first negative equality. The consumer rejects the
unmatched residual clause. HIDE already has checked identity semantics;
what is missing is the recorded proof-search selection, not its model law.
Emit the actual position, input and selected old/new literal at this source
branch, then replay that exact edit and its child. Do not unwrap literals
merely to match the desired child. Source: diagnostic
`.tmp/ns1/acl2-ta-singleton/simplify.lisp:8681–8702,8989–9010`;
actual tree: `.tmp/ns1/c2-imagpart-i-use-tree.log`; replay receipt:
`.tmp/ns1/c2-component-product-imag-i-declarations.log`.

Diagnostic producer `18af17e7a7` now emits this edit at its actual source
branch. The unchanged imagpart book recaptures 9/9; Goal'5' records position
0 and the exact old/new literals. The typed consumer replays the complete
unchanged scan, applies the selected edit using the existing checked HIDE
equation, and replays the matching real child. Eleven replay mutations and
nine parser/tree mutations reject. With its final recorded linear verdict
also checked, whole IMAGPART-OF-*-OF-I replays unconditionally at the quotient
world (`c2-unhide-selection-controls-ordered.log`). Production promotion of
the observer and capture remains open.

## BUG-056 — clausify NOT lookup omits the selected noncommutative assumption
Status: open
Pinned-by: none (proof-capture evidence, not interpreter values)

The diagnostic NOT-call observer records the returned truth value but emits
`BASIS NIL` when the selected lookup is outside its instrumented commutative
binary arm. In the current combined times capture, strict-helper Subgoal
9.17.1' literal 9 queries `(< S '0)` and returns false under the path
`(EQUAL '0 R)`; its selected assumption is absent. The consumer correctly
refuses this record instead of reconstructing a premise from the result.

Producer `7b5da0495c` instruments the successful branches of
`if-interp-assumed-value2`. This query is dispatched by
`if-interp-assumed-value-x` to `if-interp-assumed-value1`, whose exact-term
lookup branches do not record their selection. Emit the actual selected
term and sign at those branches, recapture the unchanged source, and consume
that recorded premise with the existing environment/scope checks. No
hypothesis DP or inference from the desired result is authorized. Receipt:
`.tmp/ns1/c2-strict-assumption-calls.log`; source:
`.tmp/ns1/acl2-ta-singleton/rewrite.lisp:3529–3540,3679–3710`.
Production promotion remains open.

Diagnostic producer `f4a6d954b1` now observes both successful exact-term
lookup branches and registers that raw observer in ACL2's existing raw-code
function list. The hermetic image build passes. The unchanged times prefix
captures 38/38 theorems; its 498 events compare unchanged when only the new
EXACT-TERM bases are returned to their former NIL for comparison. The consumer
checks the six-item basis, exact source/query identity and sign, then uses
its existing selected-premise context demand and environment checks. Six
actual calls kernel-check; 48 invalid mutations reject. Strict-helper 9.17
now replays with two component-product rule conditions and accepted axioms.
Receipts: `.tmp/ns1/c2-clausify-exact-times-event-comparison.log`,
`.tmp/ns1/c2-clausify-exact-controls-hoisted.log`, and
`.tmp/ns1/c2-strict-with-exact-assumptions.log`. Production promotion remains
open, so this bug is not closed.

## BUG-055 — trivial substitution omits its literal-retention decision
Status: open
Pinned-by: none (proof-capture evidence and replay composition)

`remove-trivial-equivalences-rec` records the substitution's sides and
relation, but omits the selected literal position and the actual deletion
flag passed to `subst-equiv-and-maybe-delete-lit`. ACL2 retains a trivial
quote equality, substituting through the other literals. The in-clause
consumer currently substitutes through and deletes every justifying equality.
The residual postpass has a separate retention route, but the top-level
linear-insertion continuation cannot select it from these records.

The fresh bootstrap ADD-DEF-COMPLEX Subgoal 2 retains three inserted zero
equalities; replay instead ends without a matching child. The strict
multiplication helper's Subgoal 9.12 also retains its inserted equality
in the pushed child. After the product query/row repair, replay deletes it
and reaches the legacy equation-add DP fallback, which fails. Neither
whole subtree is claimed checked. Emit the actual selected literal,
position, input clause and deletion decision, then consume the appropriate
recorded route; do not infer retention from the desired child or add a DP
proof for the lost premise. Receipts: `c2-bootstrap-poly-tree.log`,
`c2-bootstrap-poly-declarations.log`, `c2-strict-product-tree.log`, and
`c2-strict-product-subtree.log` under
`.tmp/ns1/`; source: `simplify.lisp`'s two named functions.

Isolated producer `7b5da0495c` now records that selection. The dedicated
linear-insertion continuation consumes the exact input, selected position,
literal and retention flag, applies each recorded substitution/ground fold,
and replays exactly one matching child. Both actual postpasses kernel-check
relative to their recorded children; 26 mutations reject. Whole strict
Subgoal 9.12 now checks under one ordinary real-product rule condition,
with accepted axioms, after bootstrap dependency closure. The six scoped
bootstrap theorems, including whole ADD-DEF-COMPLEX, REALPART-+ and
IMAGPART-+, now replay unconditionally with accepted axioms. Production promotion and the general
retention/deletion coverage remain open; this bug is not closed.

NS1-R's selected-edit implication now consumes deletion as well as retention.
The whole `<-OF-*-AND-*-CANCEL` proof replays unconditionally through all six
recorded deletions with accepted axioms. Two retained and two deleted actual
postpasses check against their recorded children and reject their mutation
controls. Diagnostic `7317fc15cd` also records recursive expression/literal
construction and cleanup. Both whole Boolean-book proofs now replay
unconditionally through the common construction consumer; fourteen whole-proof
query/construction mutation controls reject. Remaining continuation adapters,
legacy retirement and production promotion remain open; this is not a complete
repair of the capture surface.
Evidence: [NS1-R execution](notes/2026-09-07_ns1-r-execution.md).

## BUG-054 — numeric solidification omits the selected type mask
Status: open
Pinned-by: none (proof-capture evidence, not interpreter values)

In the weak multiplication helper's Subgoal 8', `solidify/type-alist`
replaces Y by quoted zero inside the multiplication comparison rule's RHS.
The actual record has no TYPESET or entry basis. `rewrite-solidify-rec`
obtains `ts` before calling `obj-table`, but its observer emits only the
replacement, parents, and runes. The replay supports only Boolean
solidification and refuses this node. Retain the actual selected mask before
adding the singleton consumer; do not infer the replacement from arithmetic.
Receipts: `.tmp/ns1/c2-fc-helper-bound-subst-whole.log` and
`.tmp/ns1/c2-helper-type-zero-rerun.log`.

## BUG-053 — verdict inventory omits closed branches in nonterminal clause nodes
Status: open
Pinned-by: none (proof-tree inventory, not interpreter values)

The weak multiplication helper's Subgoal 9' contains closed type-set branch
windows alongside three pushed children. `theoremDischargeLeaves` collected
verdicts only from clause nodes with no children/induction, so the harness
offered no visible DP condition when one of these actual branch leaves
failed to replay. The corresponding standalone probe also found no leaf.
The inventory now visits every clause node's actual branch items; validation
and full regression remain pending. No previously completed proof is
weakened. Receipts: `.tmp/ns1/c2-fc-helper-rational-boolean-whole.log` and
the NS1 charter's C2 record.

## BUG-052 — IF-test verdicts omit executed type-set query evidence
Status: open
Pinned-by: none (proof-capture evidence, not interpreter values)

The quotient upper bound's Subgoal *1/1' simplifies the RHS of
`<-OF-*-AND-0` using a false IF test `(< (/ J) 0)`. The original marker
retains only runes/parents, while the child chain stops at the conditional.
Its primitive reciprocal masks cannot be supplied by hypothesis automation.

Isolated fork `93c65df94d` records the actual `assume-true-false` query
before branch rewriting. The selected call has `J : 7`, `(/ J) : 11`,
and the comparison table `(11, 1) → 128`. The shared type-set query consumer
checks its recorded lookup snapshot and recursive children, then supplies
the IF collapse's falsity proof. The actual marker passes kernel/axiom
checks and rejects changed results, deleted children and a missing lookup
snapshot (`.tmp/ns1/c2-if-query-controls.log`). Whole quotient replay
crosses this node but remains ASSUMED on other dependencies and two DP
facts (`.tmp/ns1/c2-quotient-shared-if-whole.log`). Production integration,
other emitted query routes and full regression remain open.

NS1-R's complete-tree inventory finds the same missing recursive-evidence
class in known-true recognizer hypotheses: fourteen BOOLEANP queries in the
six product/cancellation targets, five with nested IF arguments, have outer
masks/tuples but no argument branch evidence. The root-IF collector is a
diagnostic re-query, not a record of the original query's executed children.
The shared query protocol must cover the actual recursive calls and branch
contexts at this consumer as well. Diagnostic producer `af782a07af` now
observes these original calls and their IF decisions, plus the original
explicit recognizer and Boolean-collapse queries. The six target trees carry
312 recursive queries, and real source probes exercise both-branch,
true-only and false-only IF decisions. The Boolean-collapse consumer now
uses the shared query path and an explicit ordinary-rule channel; both Boolean
book theorems replay unconditionally and consume the replayed bootstrap
recognizer. The shared consumer now checks original known-true and explicit
primitive recognizer queries, including both-branch and singly pruned IF
queries from the authored probes. Both product-sign theorems replay
unconditionally. Reserved EQUAL-/ reuse exposes a further decision-record
gap: ASSUME-TRUE-FALSE-REC prunes `(NOT (ACL2-NUMBERP X))` by querying X,
but the current IF record omits the selected recognizer decision tuple and
negation normalization. That route is refused; recording and consuming it,
the remaining target proofs and production integration remain open. See the
[NS1-R execution record](notes/2026-09-07_ns1-r-execution.md).

The strict multiplication helper also exercises `:CONSTANT-BOUND`, whose
returned derivation omitted the selected type-alist entry. Isolated producer
`d592add7be` records that entry from the actual successful scan arm; its new
capture and consumer validation are pending. The argument-mask table route
is not a substitute for replaying that recorded bound.

## BUG-051 — context contradiction does not retain its selected FC suffix
Status: open
Pinned-by: none (clause-boundary proof evidence, not interpreter values)

NONNEGATIVE-INTEGER-QUOTIENT-UPPER-BOUND-LINEAR, Subgoal *1/3', reaches
`rewrite-clause/type-alist-contradiction` after six literals. Its actual
obligation is the branch accumulator followed by three negated
forward-chaining conclusions; the current literal is excluded. This is
`rewrite-clause-type-alist`'s documented construction in `simplify.lisp`:
`new-clause ++ cdr(tail) ++ selected-fc-literals`. The existing consumer
supports only the empty FC suffix and correctly refuses this occurrence.

The isolated capture at fork `3d78183cc7` retains the leaf at NIQ log:22440
and clause-level derivations for `<=-OF-*-AND-*-SAME-FORWARD-1` and `-2`
at :21573, including substitutions, parents, and nested supports. The leaf
does not identify which FC pairs the actual parent filter selected, nor
carry their derivations/runes into its own basis. The final residual is
`(NOT (< (* I (/ J)) (NONNEGATIVE-INTEGER-QUOTIENT I J)))`, which is not
the emitted DP obligation. Preserve and replay the selected FC evidence
before peeling the extra disjuncts; do not widen the DP obligation or
assume the FC conclusions. Receipt:
`.tmp/ns1/c2-quotient-known-comparison-tp-whole.log`. No completed quotient
statement or native BVCHOP product is claimed.

Diagnostic buildout, 2026-09-07: isolated fork `5e1f29dd05` now retains
the selected sources, stored implications, executed hypothesis reliefs and
recursive type-set query trees. The consumer checks their substitutions,
hypothesis order, query children, lookup snapshots and exact selected suffix.
All nine selected queries and all three source fragments pass kernel/axiom
checks; the source fragments remain conditional on ordinary FC-rule proofs.
The first whole quotient probe advances to Subgoal *1/1', where the later
reciprocal IF collapse exposes BUG-052. Its isolated repair now crosses that
node, but the quotient retains other conditions and assumed DP facts. The
producer is not promoted, FC dependencies are incomplete, and this bug remains
open through integration.
Receipts: `c2-fc-source-controls-rerun.log`, `c2-fc-context-events-comparison.log`
and `c2-quotient-not-iff-whole.log` under `.tmp/ns1/`.

## BUG-050 — hypothesis instantiation folds are absent from relief records
Status: fixed
Pinned-by: none (proof-capture evidence, not interpreter values)

NONNEGATIVE-INTEGER-QUOTIENT-UPPER-BOUND-LINEAR applies
<-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT with K := '-1. Its actual hypothesis
`(< '-1 '0)` is folded by `sublis-var`/`cons-term` before
`known-whether-nil`; the emitted known-true marker names only `'T`.
The exact hypothesis matcher therefore refuses the rule at Subgoal *1/4.
Computing an unrecorded hypothesis or weakening the substitution check is
not an acceptable repair.

Isolated fork f5cada538a observes the actual instantiation walk and records
its unfolded hypothesis and addressed ground folds on the known-true marker.
The unchanged source prefix through
NONNEGATIVE-INTEGER-QUOTIENT-LOWER-BOUND-LINEAR2 captures successfully
(`.tmp/ns1/c2-substitution-fold-capture/`, 14/12 QED/DEFTHM events); the
actual missing fold is `(:PATH NIL :LHS (< '-1 '0) :RHS 'T)`.
The observer does not rerun the computation. Its image and tagging checks
pass; consumer support and production integration remain open.

Production fork **1167a1ac98** now includes the observer; all 110 captures
are stamped there. Strict parsing preserves the plain hypothesis and every
ordered fold. The consumer checks the captured primitive domain/guard,
quoted computation and exact argument path, then composes to the marker's
hypothesis. All 16 nonempty NIQ markers pass explicit kernel/axiom checks;
deleted folds, changed positions/results and missing guards are rejected.
Permanent malformed-field controls also pass
(`c2-substitution-permanent-tests-build.log`, 3134 jobs). Whole NIQ replay
crosses the original fold and now stops at the separate < '0 J type-set
basis below (BUG-039). Full regression for this increment remains pending.

Validated 2026-09-07: `.gate-runs/0f323b3-20260907T003817Z.log` records
`TRUE_EXIT=0`, with 116 unconditional baseline theorem rows, the unchanged
golden and 21 existing mirrors. P6's five actual two-fold instances also
pass the permanent kernel/axiom and mutation controls. Its stale missing-hyp
pin was corrected to the remaining DEFAULT-<-1/DP conditions; P6 remains
0/1. Production captures now carry the descendant fork `fd27e59021`.

## BUG-049 — linear equation insertion is absent before trivial substitution
Status: open
Pinned-by: none (intermediate clause transformation is missing from the proof log)

The actual <-OF-*-AND-*-CANCEL tree stops at Subgoal 2.9's X2 := X1
branch substitution. Neither orientation of the justifying equality occurs
in the recorded input clause. simplify.lisp's process-equational-polys
first derives and adds a negated equation to that clause; simplify-clause1
then passes the expanded clause to remove-trivial-equivalences. Only the
latter substitution is emitted. The returned step cites
fake-rune-for-linear-equalities but does not record the intermediate clause,
its equation or the numeric-assumption flags. The current consumer refuses
this nonconstant substitution (`c2-positive-boundary-whole-replay.log`).
Capture the actual insertion and its justification, including numeric
completion/forcing distinctions; do not infer an equation from the desired
child clause or loosen the old quoted-substitution guard.

The combined helper capture additionally exposes direct zero rows whose
numericity is established by separate `add-linear-assumption` queries,
with no numeric PT tips in the polynomial itself. Isolated producer
`db2547b38d` records those actual queries, original operands, and their
type-alist snapshot. The first instance queries ACL2-NUMBERP(X1) from mask
64 / PTs 0, 1, 4 and a quoted T for zero. The image and capture pass;
the query consumer and promotion remain open (NS1 charter).

The diagnostic consumer now checks those numeric queries, including
recognizer tuples propagated through REALPART/IMAGPART. Producer
`f9d55fb3e6` additionally records actual POLYS-FROM-TYPE-SET construction
queries for selected rows. Four comparison zero-row insertions and both
Subgoal 2'/3' subtrees check. The strict helper's multiplication query and
selected zero-row insertion also check; its continuation exposes BUG-055.
The baseline msort row classes remain open. The production pointer is unchanged,
so BUG-049 remains open (NS1 charter).

The isolated producer now records the insertion and the original clause
whose literal indices label the polynomial parents (aaaaaea5c4, following
1589f73292). The fresh times capture reconstructs six insertion items in
their actual positions (`c2-linear-parent-reconstructed-tree.log`). A
consumer checks the direct, complementary unit-row class, including PT
numeric premises, and replays its substitution/duplicate/child continuation.
With the unchanged less-than source through NOT-<-SAME supplied, all six
actual insertion subtrees check unconditionally with the accepted axiom trio;
nine mutation controls reject altered or missing evidence
(`c2-linear-insertion-closed-fragments.log`). The whole theorem now reaches
the existing 3M-heartbeat limit in `isDefEq`
(`c2-linear-product-with-less-than.log`). Profiling localizes that cost to
DP leaves. A rational-normalization candidate closes all 12 actual emitted
leaves under the unchanged direct-attempt budget, with accepted axioms
(`c2-rational-product-all-leaves-kernel.log`). The rebuilt driver now
replays the whole cancellation theorem unconditionally from the isolated
capture, using NOT-<-SAME's source tree and the existing multiplication
associativity model proof at its actual :USE instances
(`c2-associativity-use-cancellation.log`, accepted axiom trio).
Msort's fresh diagnostic capture contains additional
count/linear-rule polynomial classes, so this producer has not been
integrated into the production fork. The current production consumer passes
full regression at 2953c78 (`.gate-runs/2953c78-20260906T215722Z.log`,
`TRUE_EXIT=0`); the isolated insertion producer's integration remains open.

## BUG-048 — atom boundary type-set replacement retains the attempted rewrite
Status: fixed
Pinned-by: none (ACL2 instrumentation and proof-tree composition, not interpreter values)

The actual <-OF-*-AND-*-CANCEL tree has six negated POSITIVE multiplication
instances where rewrite-atm's final try-type-set-and-clause succeeds on the
original, expanded IMPLIES atom in isolation. That branch returns the new
type-set proof tree combined with ttree0, discarding the attempted rewrite's
ttree (simplify.lisp:5551–5603). The log retains the attempted recognizer/IF
chain before an ATM/IMPLIES-EXPAND step whose lhs is the original atom,
followed by ATM/TRY-TYPE-SET. These do not form one sequential rewrite chain.
The existing rollback handles keeping an unchanged atom, but does not handle
this successful replacement. The boundary reader also requires definitional
equality to the verdict, which cannot check this nontrivial recorded leaf.
The current whole replay stops at that boundary check
(`c2-positive-negated-if-whole-replay.log`); the reconstructed records are in
`c2-positive-boundaries-rerun2.log`. Repair the emission's retained proof
path and consume the actual boundary verdict with its precise scope.

The isolated producer fix at 56948b4df642 and its fresh capture retain only
the winning path. The consumer checks all six actual prefix/verdict
compositions, with accepted axioms, and rejects removed prefixes, changed
verdict inputs/results and changed polarity
(`c2-positive-boundary-use-controls-rerun2.log`). Whole cancellation now
stops at BUG-049. Production fork aac5e1a45d and all 110 captures now include
the fix; permanent Tests.Ns1Positive controls, Basics and PermBook imports,
and sorting/perm coverage pass (`c2-boundary-production-focused-build.log`).
The full regression rerun remains pending, so this entry stays open.

Full regression recovery, 2026-09-06: the gate at `2953c78` records
`TRUE_EXIT=0` in `.gate-runs/2953c78-20260906T215722Z.log`. The repaired
source pins and controls pass, all 116 baseline theorem rows remain
unconditional, the golden is unchanged, and the 21 existing mirrors pass.
This closes this repair; NS1's three native BVCHOP mirrors remain open.


## BUG-046 — IF window reconstruction drops its test and empty swapped windows
Status: fixed
Pinned-by: none (recursive proof-tree records, not interpreter values)

EQUAL-/ has a recorded BEGIN-IF test and swapped branch windows. The parser
discarded the test, leaving two plausible addresses in the running term,
and discarded empty windows even when their SWAPPED-P field records a
normalization. The branch composer consequently fails before the next
recorded literal result. Retaining the scoped test resolves the first
address ambiguity. The parser now retains empty swapped boundaries and nested
window scope; the consumer also composes the combined IF record's negated-test
swap. EQUAL-/ and EQUAL-/-0 pass whole-proof and source/axiom pins
(`c2-reciprocal-zero-type-cell-build.log`). Changed window tests are rejected
by the permanent context controls. The full gate at 7445845 is red: the
new test filter rejects ORDEREDP-MEMB's actual window anchor, retaining a
condition in ORDERED-PERMS and failing the waypoint/coverage pins. The
repaired consumer shares the existing EQUAL-NIL swap shape with the other
IF normalizers. Both failed modules and a changed-test control now pass
(`c2-ordered-window-regression-pins-build.log`). A full rerun remains pending.

Full regression recovery, 2026-09-06: the gate at `2953c78` records
`TRUE_EXIT=0` in `.gate-runs/2953c78-20260906T215722Z.log`. The repaired
source pins and controls pass, all 116 baseline theorem rows remain
unconditional, the golden is unchanged, and the 21 existing mirrors pass.
This closes this repair; NS1's three native BVCHOP mirrors remain open.


## BUG-047 — rewrite-equal omits Boolean equality normalization
Status: fixed
Pinned-by: none (ACL2 instrumentation, not interpreter values)

rewrite.lisp's two Boolean type-set arms return the nonconstant side of
`(EQUAL value 'T)` or `(EQUAL 'T value)` without logging the step. EQUAL-/
reaches this second orientation with an IF-valued Boolean expression.
Fork ef2746dade adds both actual steps, their consumed type-set masks and
addressed IF leaves. EQUAL-/ passes its whole-proof and source/axiom pins;
changed masks and deleted addressed leaves are rejected. The sorting replay
also exposes a cited Boolean defun TP (PERM), requiring the same consumer to
instantiate that recorded corollary. The repaired focused sorting replay
passes 13/13 unconditional (`c2-equal-boolean-sorting-tp-replay.log`). Full
regression validation remains pending.

Full regression recovery, 2026-09-06: the gate at `2953c78` records
`TRUE_EXIT=0` in `.gate-runs/2953c78-20260906T215722Z.log`. The repaired
source pins and controls pass, all 116 baseline theorem rows remain
unconditional, the golden is unchanged, and the 21 existing mirrors pass.
This closes this repair; NS1's three native BVCHOP mirrors remain open.


## BUG-001 — no character type: `#\a` is modeled as a symbol
Status: fixed
Pinned-by: none (fixed 2026-07-08 — corpus entries reclassified to `match`)
ACL2 has a character type (code points 0–255). Our `Atom` had no character
variant, so `#\a` parsed as a symbol named `#\a`. Consequences: `(equal #\a #\b)`
= t (distinct ACL2 characters collapse) and `(symbolp #\a)` = t (a char is not a
symbol). FIXED 2026-07-08: added `Atom.char (UInt8)` + faithful `#\` parser
(single char + the 6 named chars, error otherwise) + ACL2-faithful printer +
`characterp`/`char-code`/`code-char` (with completion corners). The
differential ratchet flipped the two known-bug entries and five now-modeled
char ops in characters.lisp; all reclassified to `match`. See
docs/notes/2026-07-08_acl2-character-semantics.md. (Residual: `char-upcase`/
`char-downcase`/`char<=`/`coerce` char ops remain `unsupported`.)

## BUG-002 — symbol case: parser lowercases bare symbols
Status: fixed
Pinned-by: none (fixed 2026-07-08 — corpus entries reclassified to `match`)
ACL2's reader UPCASES bare symbols and PRESERVES the case of `|bar|`-escaped
symbols; our parser used to LOWERCASE bare symbols, so the case at which two
spellings collapse differed from ACL2. FIXED 2026-07-08 by adopting ACL2's
readtable-case :upcase exactly (docs/notes/2026-07-08_symbol-case-semantics.md):
the parser now upcases bare symbols AND bare keywords and reads `|bar|` (incl.
`:|bar|`) verbatim; `|NIL|`/`|T|` map to the nil/t constructors (they ARE those
symbols). Symbol NAMES are stored uppercase everywhere on the identity path
(`SExpr.t`, `isNamed` literals, `callBuiltin` keys, world/theorem/rune names);
internal DISPATCH TAGS that happen to arrive as symbols/keywords (rune TYPE,
equiv, processor, origin, clausify outcome/verdict/how/kind, extraField keys)
are lowercased at the ProofLog parse boundary — they are not symbol identities.
The differential ratchet flipped all 12 BUG-002 known-bug entries (across
symbol-identity/symbols-keywords/printing.lisp) to `match`, and surfaced a
latent gap the fix also closed: `:|bar|` keywords were not read verbatim
(`:|ABC|` now equals `:abc`, `:|abc|` stays distinct).

## BUG-003 — printer does not abbreviate `(quote x)` as `'x`
Status: fixed
Pinned-by: none (fixed 2026-07-08 — corpus entries reclassified to `match`)
ACL2's printer renders a 2-element list whose car is the symbol `QUOTE` as
`'x`, recursively at any nesting depth; the exact 2-element form only (`(quote)`,
`(quote a b)`, improper `(1 quote a)` print literally). FIXED 2026-07-08 in
`SExpr.toString` (Syntax.lean) with a case matching `.cons (QUOTE) (.cons x nil)`
→ `"'" ++ toString x`; the recursive call re-enters the case so nesting is free.
Regression guards in printing.lisp (all now `match`).

## BUG-004 — the '.'-token reader path (floats + trailing-dot integers)
Status: fixed
Pinned-by: none (fixed 2026-07-08 — corpus entries reclassified to match/refuse)
Grounded in the ACL2 source: `*acl2-readtable* = (copy-readtable nil)` is the
standard Common Lisp reader, and ACL2 binds `*read-base* = 10` always
(axioms.lisp:21116). So a `.`-bearing token follows CL base-10 number syntax.
FIXED 2026-07-08 in Parser.lean (`numericTokenIsFloat` / `trailingDotInteger?`):
(A) FLOATS refused — a fractional digit after the dot (`5.0`/`1.5`/`.5`) or an
    exponent marker (`5e3`/`1d0`; markers E/S/F/D/L) is a FLOAT; ACL2 has no
    float type and its reader refuses, so we fail-closed (`<refused>`).
(B) TRAILING-DOT INTEGERS read as integers — `[sign] digits+ .` with no
    fractional digit is a DECIMAL INTEGER (`1.`=1, `10.`=10, `-5.`=-5,
    `(integerp '10.)`=T).
Dot-free numbers (`100`/`2/3`) and dotted non-numbers (`foo.bar`) are unchanged.
Regression guards in boundary.lisp (floats `refuse`, trailing-dot `match`).

## BUG-005 — radix integer literals rejected (ACL2 accepts them)
Status: fixed
Pinned-by: none (fixed 2026-07-08 — corpus entries reclassified to `match`)
ACL2 accepts Common-Lisp radix literals: `#xFF`=255, `#b101`=5, `#o17`=15,
`#Nr…`=radix N. FIXED 2026-07-08 in Parser.lean (`readRadixInt`/`digitInBase`
+ `#`-dispatch cases for `#x/#X`, `#b/#B`, `#o/#O`, `#Nr/#NR`): case-insensitive
prefix+digits, signed, value is the integer, radix 2–36. Regression guards in
boundary.lisp (all now `match`).

## BUG-006 — lexorder atomKind: keyword has its own order class
Status: fixed
Pinned-by: differential (Tests/differential/corpus/target-ordering.lisp)
ACL2 `alphorder` (axioms.lisp:26995): keywords ARE symbols and sort within the
symbol class by `symbol<`. FIXED 2026-07-08 in the `lexorder`/`atomKind`
FUNCTION (keyword folded into the symbol kind); lexorder was then WIRED into
callBuiltin (Task #7, 2026-07-08) and is now differentially pinned vs real ACL2.
NOTE: the order-property PROOFS (refl/antisym/trans/total) are DONE
(2026-07-12, LexorderOrder.lean — kernel-checked against the corrected
lexorder, enabled by the BUG-012/013/014 canonicity fixes).

## BUG-007 — lexorder atomKind: no character class
Status: fixed
Pinned-by: differential (Tests/differential/corpus/target-ordering.lisp)
`alphorder` orders characters between rationals and strings (by `char-code`).
FIXED 2026-07-08 in the function (character kind added between number and
string, compared by char-code), alongside BUG-001's character type; wired +
differentially pinned 2026-07-08. Proofs commented out pending re-proof.

## BUG-008 — lexorder symbol comparison is not `symbol<`
Status: fixed
Pinned-by: differential (Tests/differential/corpus/target-ordering.lisp)
`Lexorder.lean` compared symbols by `name` then `package`; ACL2's `symbol<`
compares symbol-name via `string<`, tie-break by package-name via `string<`.
FIXED 2026-07-08 with a faithful `symbolLe` (name via `String.<`, tie-break
package) covering both symbols and keywords; wired + differentially pinned
2026-07-08 (`:abc` vs `'abc`, `acl2::foo` vs `common-lisp::foo` confirmed).
Proofs commented out pending re-proof. Residual fidelity question: Lean
`String.<` vs ACL2 `string<` char-ordering — validate when lexorder is wired +
differentially
tested.

## BUG-009 — no complex-rational class (numbers/lexorder)
Status: fixed
Pinned-by: differential (Tests/differential/corpus/complex-arith.lisp,
complex-reader.lisp, complex-and-packages.lisp)
`alphorder` places complex/complex-rationals between rationals and characters.
The pre-NS1 model omitted complex numbers entirely.

**Fixed at NS1 C1 (2026-09-06):** canonical complex values, arithmetic/completion,
reader/reflection, numeric and alphabetical ordering, exact ACL2 value count,
and inhabited type-set bit 6 are implemented. The complex-bit discount is
removed. Three real captured complex theorems pass unconditional statement
and axiom pins in `Tests/ComplexReplay.lean`. The ordinary differential suite
passes with 529 matches, 138 unsupported cases, 10 known bugs, 25 refusals and
zero failures (`.tmp/ns1/c1-full-differential-thin.log`). The full migration
gate passes (`.gate-runs/31d8e42-20260906T010720Z.log`, `TRUE_EXIT=0`),
preserving 116 unconditional rows, the unchanged golden and 21 native
products. `#2C` dispatch arguments remain an explicitly refused reader
syntax, separately classified `unsupported`; genuine complex values are
represented and evaluated. See the
[NS1 charter](plans/2026-09-05_bvchop-foundation-charter.md).

**New-book reproduction (2026-09-05):** a fresh capture of
`acl2/books/kestrel/bv/bvchop.lisp` at fork `e8d78e513d6867d04002f0df644da1723cc96e89`
succeeds, but `acl2lean-replay --dump` rejects it with
`Parse error: unrecognized reader macro: #C`. The included arithmetic theorem
`EQUAL-OF-+-OF-*-OF-I` and its stored rule contain `#C(0 1)`: even this
integer-oriented book reaches the limitation through its dependencies.
Commands and scope are recorded in the
[post-sorting assessment](notes/2026-09-05_next-north-star-assessment.md).

**Pre-migration dependency record:** the dated notes below describe the
former implementation and explain the scope the NS1 repair must cover.

Dependency note (2026-07-20, STRINGP-lift audit): `Logic.rationalp` coincides
with `Logic.acl2Numberp` ON THE MODEL (both true exactly on `.atom (.number _)`)
precisely because of this bug — and the DP-lift registry now consumes
`RATIONALP` through that coincidence. If complex numbers are ever modeled,
`Logic.rationalp` must diverge from `acl2Numberp` (nil on complex) and the
DP-lift discharge of RATIONALP leaves must be revisited alongside.

**Dependency note (2026-07-29, sorting arc):** `Logic.complexRationalp`
is now a trusted-core builtin defined CONSTANTLY nil (with
`realpart`/`imagpart` on the complex-free space), differentially pinned
(numerator-denominator.lisp), and LOAD-BEARING in two vacuous-branch
discharges: the totality walk (`Totality.lean`, the definitionally-nil
truthy branch — ACL2-COUNT's complex admission case) and the induction
walk (`Waterfall/Induction.lean`, same pattern). Both close ACL2's
complex case by absurdity — a DOMAIN RESTRICTION of the model (SExpr
admits no complex values), not a statement weakening, and fail-closed
under a future fix here (the `isDefEq _ nil` guards stop matching and
those proofs stop elaborating, loudly).

**Dependency note (2026-08-15, T1+2 sprint P4b) — THIRD SITE, the
TYPE-SET comparison.** `ACL2Lean/Replay/Driver/TsFacts.lean`'s
`tsAcl2MaskOk`, consumed by `recogVerdictFromTs`
(`Replay/Driver/NodeCore/TypeSetWalk.lean`). ACL2 encodes basic type
INDEX 6 as `*ts-complex-rational*`; `tsIndex`
(`Replay/Lemmas/TsAlgebra.lean`) never returns 6, so `InTs m v` and
`InTs (m ∪ {6}) v` are the SAME proposition on this model and a derived
mask can never carry that bit. ACL2's `<` DOES order complex rationals,
so `(< N '0)` true is emitted with `:TYPESET 112` where the model
derives `48` — 112 = 48 ∪ {bit 6} exactly. The cross-check "ACL2's
emitted mask must be inside the one we derived" therefore demanded the
impossible and refused a strictly-STRONGER derivation (`CD2-BOUND`'s
`Subgoal 1`, recorded as charter J-P4a-g). The comparison now discounts
index 6 AND NOTHING ELSE — any other bit ACL2 has and we do not still
fails, closed. The verdict is unchanged (still ACL2's) and the proof
still runs on OUR mask and OUR `InTs` fact; this is the same domain
restriction as the two sites above, applied at one more place. Fail
direction under a future fix: index 6 becomes inhabited and the discount
becomes unsound to keep, so `tsAcl2MaskOk` must be DELETED (reverting to
`tsSubsumedM`) alongside any fix here — its docstring says so at the
site.

## BUG-028 — reader accepts a rational literal with denominator zero
Status: fixed
Pinned-by: differential (Tests/differential/corpus/complex-reader.lisp)

The pre-NS1 `Parser.lean` rational-token branch passed any parsed natural denominator
to `Logic.mkNumber`. That smart constructor's zero-denominator completion
returns integer zero, so `(quote 1/0)` evaluates to `0` in ACL2Lean.
The pinned ACL2 reader rejects the token with `READER-ERROR`, caused by
`DIVISION-BY-ZERO`. Reader acceptance must not inherit arithmetic completion.

Reproduced 2026-09-05 at ACL2Lean `b452b70` and fork
`e8d78e513d6867d04002f0df644da1723cc96e89`: the built Lean CLI's
`eval "(quote 1/0)"` prints `0`; the freshly built ACL2 image reading
`(value-triple '1/0)` emits the reader error. Transcripts are in the NS1
worktree's `.tmp/ns1/zero-denominator-{lean,acl2}.out`.
The new complex reader would inherit this divergence if it accepted
components through the current rational parser. Reject zero denominators
at the reader boundary and cover ordinary and complex-component literals
with isolated differential tests. See the
[NS1 numeric design](notes/2026-09-05_ns1-numeric-design.md).

**Fixed 2026-09-06:** the reader rejects zero denominators before numeric
construction. Isolated ordinary and complex-component refusal cases pass
the full differential suite; the C1 full claim gate records `TRUE_EXIT=0`
in `.gate-runs/31d8e42-20260906T010720Z.log`.

## BUG-029 — rational term-order weight drops the recursive call limit
Status: fixed
Pinned-by: none (internal term-weight API; source/ACL2 boundary probes and
Tests/TermOrderTest.lean guards pin the repaired rational and complex paths)

The pre-NS1 `TermOrder.fnCountEvgAtom` expanded a rational's numerator and denominator
with direct `fnCountEvgInt` calls, omitting the recursive call-count checks
of ACL2's `fn-count-evg-rec` (`linear-a.lisp:1492` onward). Near the limit,
this computes a small weight where ACL2 saturates at 200000 and can change
term-order tie-breaking.

Reproduced 2026-09-05 on the unchanged model: `fnCountEvgRec` of `1/2`,
accumulator 0 and calls 997, 998, 999 gives `[6, 6, 6]`; the same three
calls to the freshly built ACL2 image give `(6 200000 200000)`.
Complex constants recurse through the same component path: ACL2 gives
`(9 200000 200000)` for `#C(1/2 1)` at calls 995, 996, 997.
Inputs and outputs are in `.tmp/ns1/term-weight-{lean,acl2}.*` in the NS1
worktree. Preserve both accumulator saturation and call-count saturation
when adding complex weights, and repair the existing rational path with
source-based boundary checks. See the
[NS1 numeric design](notes/2026-09-05_ns1-numeric-design.md).

**Fixed 2026-09-06:** every rational/complex component visit checks both
source limits, preserving the component order and call increments. The
focused guards include a public 499-cons input; full C1 coverage is golden
byte-identical. Gate `.gate-runs/31d8e42-20260906T010720Z.log` records
`TRUE_EXIT=0`.

## BUG-030 — inherited LOCAL mislabels imported definitions as witnesses
Status: fixed
Pinned-by: none (proof-log provenance; NS1 local-include capture/replay probe)

The DEFUN emitter treats every non-nil `in-local-flg` as a local witness.
ACL2 uses `LOCAL-INCLUDE-BOOK` when an enclosing include is local but the
definition is ordinary within the included book
(`other-events.lisp:3874`, `include-book-process-embedded-events`). The
unchanged BVCHOP capture therefore labels ALL-VARS-NEGATED as LOCAL-WITNESS;
reconstruction correctly rejects it outside an encapsulate scope.

Reproduced with `.tmp/ns1/local-include-probe.lisp`: an ordinary helper
definition imported by LOCAL is emitted as LOCAL-WITNESS. NS1 C2's emitter
repair recognizes precisely LOCAL-INCLUDE-BOOK with an active include path;
actual LOCAL events still take the witness arm. A rebuilt image emits
INCLUDE-BOOK for the helper, and its actual theorem replays 1/1 unconditionally
(`.tmp/ns1/c2-local-include-replay.log`). The clean fork commit/recapture and full provenance/witness regressions
pass in the C2 checkpoint gate recorded below. See the
[NS1 charter](plans/2026-09-05_bvchop-foundation-charter.md).

Fixed 2026-09-06; full checkpoint gate
`.gate-runs/aec7fcd-20260906T034924Z.log` records `TRUE_EXIT=0`.

## BUG-031 — a clause contradiction leaves a spurious literal opening
Status: fixed
Pinned-by: none (proof-log structure; NS1 BVCHOP-BOUND capture)

`rewrite-clause` emits BEGIN-LITERAL before constructing the type-alist.
When that construction finds a contradiction, ACL2 closes the whole clause
without rewriting the literal, emits its verdict and returns without an
END-LITERAL. Inside a branch this makes reconstruction encounter END-BRANCH
inside an apparently open literal. Reproduced in unchanged BVCHOP-BOUND,
`Goal''/simplify-clause`, and two arithmetic dependencies
(`.tmp/ns1/c2-context-{bvchop,mod,mod-and-expt}-tree.log`). The actual fragment
is at lines 29972–29989 of `.tmp/ns1/c2-captures/bvchop.proof-log`.

NS1 C2 moves the opening marker to the non-contradiction path, preserving
the existing clause-level verdict and the path-window reset. No rewrite
or literal result is invented. The rebuilt image's fresh BVCHOP, MOD,
MOD-AND-EXPT and UNSIGNED-BYTE-P captures all reconstruct
(`.tmp/ns1/c2-balanced-*-tree.log`). The clean fork commit/recapture cycle and full regression gate now pass.

Fixed 2026-09-06; full checkpoint gate
`.gate-runs/aec7fcd-20260906T034924Z.log` records `TRUE_EXIT=0`.

## BUG-032 — clausification folds evaluator builtins beyond ACL2's primitive domain
Status: fixed
Pinned-by: none (actual BVCHOP-UPPER-BOUND branch-collapse frontier)

`collapseEval` uses absence from the Lean World as its ground primitive test.
That conflates interpreter builtins with ACL2 primitives: EXPT is an ordinary
ACL2 defun, so `call-stack`/`cons-term` leaves `(EXPT '2 '0)` intact when
clausifying BVCHOP-UPPER-BOUND's Goal'. The replay folds it to `'1` and then
fails its exact leaf-value check (`.tmp/ns1/c2-bvchop-upper-registry-replay.log`).
The same test omits cons-term's guard requirement: `basis-b.lisp` constructs
its cases from `*primitive-formals-and-guards*`, with explicit exclusions.

NS1 C2 emits that actual primitive/guard domain as CONS-TERM-GUARDS and
using it to gate closed folds. The closed computation and surrounding proof
remain kernel-checked. The fresh BVCHOP-UPPER-BOUND tree passes this node and now retains only
three linear DP obligations. Full regression validation passes; no completed
BVCHOP mirror is claimed.

Fixed 2026-09-06; full checkpoint gate
`.gate-runs/aec7fcd-20260906T034924Z.log` records `TRUE_EXIT=0`.

Reopened 2026-09-06 for the compiler boundary of the same folding path.
EQUAL-/ retains `(EQUAL (EQUAL Y '0) 'T)` as a leaf, while `collapseEval`
reduces it to `(EQUAL Y '0)`. `if-compile` PUSHes an application unchanged
when its arguments contain no IF; only CALL invokes the primitive folds in
`call-stack`. The primitive-domain/guard repair above remains in place;
the additional compiler-boundary repair is in progress.

Full regression recovery, 2026-09-06: the gate at `2953c78` records
`TRUE_EXIT=0` in `.gate-runs/2953c78-20260906T215722Z.log`. The repaired
source pins and controls pass, all 116 baseline theorem rows remain
unconditional, the golden is unchanged, and the 21 existing mirrors pass.
This closes this repair; NS1's three native BVCHOP mirrors remain open.


## BUG-033 — snapshot collector treats quoted symbol data as function references
Status: fixed
Pinned-by: none (real FLOOR capture and cov-quoted-snapshot)

The raw `prin1$` collector records every printed symbol. Quoted package-import
lists in emitted rules therefore demand unrelated ground-zero definitions,
including the APPLY$ clique whose `:?` measure cannot be reconstructed. The
unchanged FLOOR book completes its proofs but snapshot emission aborts.
NS1 C2 suspends collection inside both flat and pretty quote printers; their
printed bytes and logical behavior stay the same. Actual references outside
quotes and the transitive definition/measure closure remain collected. The
raw-code registration follows ACL2's logic-function registry. The clean image, real quoted-name capture, all quoted-name statement pins
and full regression gate pass.

Fixed 2026-09-06; full checkpoint gate
`.gate-runs/aec7fcd-20260906T034924Z.log` records `TRUE_EXIT=0`.

## BUG-034 — capture checks confuse literal diagnostic/NUL data with failure
Status: fixed
Pinned-by: none (real FLOOR capture and cov-quoted-snapshot)

FLOOR's expanded ground-zero snapshot contains ERROR-FMS-CHANNEL's literal
`HARD ACL2 ERROR` string. The unanchored failure grep rejects this source data
as an actual error. NUL bytes in ordinary ACL2 strings also make the local
event-count grep suppress matches and report zero source proofs. The repair recognizes actual diagnostic lines and scans the event census as text.
The real quoted diagnostic/NUL book is the positive control; a copy with an
injected actual error line is the negative control. Completion, QED pairing,
event-failure and source/provenance checks still apply. The clean recapture, positive/negative controls and full gate pass.

Fixed 2026-09-06; full checkpoint gate
`.gate-runs/aec7fcd-20260906T034924Z.log` records `TRUE_EXIT=0`.

## BUG-035 — capture passes Latin-1 bytes to a UTF-8 proof-log reader
Status: fixed
Pinned-by: none (FLOOR snapshot and real quoted-nul-data statement pin)

ACL2's `acl2-set-character-encoding` selects ISO-8859-1, including at SBCL
restart. Ordinary literal bytes above 127 in FLOOR's ground-zero snapshot
therefore make Lean's UTF-8 file reader reject a complete capture. Capture
now transcodes ISO-8859-1 to UTF-8 before completeness checks and promotion,
recording both encodings in the sidecar. The transformation preserves each
character. `Tests.Ns1Ingestion.nulReplayed` pins the real emitted string to
characters H, 0 and 255 and checks the replayed statement's axiom set. Clean
recapture and full gates pass.

Fixed 2026-09-06; full checkpoint gate
`.gate-runs/aec7fcd-20260906T034924Z.log` records `TRUE_EXIT=0`.

## BUG-037 — preprocess computation records omit their positions
Status: fixed
Pinned-by: none (actual FLOOR-OF-0-ARG1 capture pins the repeated-call failure)
FLOOR-OF-0-ARG1 expands translated LETs into two occurrences of
`(NONNEGATIVE-INTEGER-QUOTIENT '0 '1)`. The actual preprocess evaluator records
both computations but omitted the argument paths, leaving replay unable to
identify which occurrence each step changes. The six computation/IF/equality
emission sites in `acl2/induct.lisp` now carry the same abbreviation-walker
path already used by definition and beta steps. The consumer navigates and
checks those positions; it does not choose between repeated occurrences.
The clean image, real recapture and FLOOR-OF-0-ARG1 replay pass, with
an independent source-formula pin and the accepted axiom trio in
Tests.Ns1Arithmetic. Full regression validation passes.

Fixed 2026-09-06; full checkpoint gate
`.gate-runs/aec7fcd-20260906T034924Z.log` records `TRUE_EXIT=0`.

## BUG-036 — forcing-round detail prose survives structured output
Status: fixed
Pinned-by: none (actual full FLOOR capture/parser frontier)
The full unchanged FLOOR capture formerly printed explanatory prose after its
structured FORCING-ROUND event, including an unquoted `2.1` clause number that
the reader correctly refused as a float. `process-assumptions-msg` in
`acl2/prove.lisp` suppressed the first announcement but still called
`process-assumptions-msg1` and the final prose printer. Both remaining calls
are now suppressed in structured mode.

The clean fork's full FLOOR recapture completes all 125 source theorem events
(`.tmp/ns1/c2-floor-clean-full-capture.log`). Parsing now reports the explicit
unsupported FORCING ROUND 1 frontier, with no stray-prose failure
(`.tmp/ns1/c2-floor-clean-full-forcing-frontier.log`). Forcing-round proof
composition remains excluded from NS1 and is still open in TODO. ACL2's native
LD name filter captures an unchanged prefix when only earlier dependencies
are needed; it removes no event from an existing log.

Fixed 2026-09-06; full checkpoint gate
`.gate-runs/aec7fcd-20260906T034924Z.log` records `TRUE_EXIT=0`.

## BUG-045 — branch boundaries exclude the branch's initial simplification
Status: fixed
Pinned-by: none (proof-log structure; the value differential cannot observe branch ownership)
`rewrite-clause-lst` invokes `crunch-clause-segments` before emitting its
BEGIN-BRANCH marker. That invocation may emit branch substitutions and
constant folds, which consequently reconstruct as steps of the enclosing
branch. RIGHT-CANCELLATION-FOR-* in arithmetic-3/pass1/basic-arithmetic-helper
exhibits Y := 0, X := 0 and Z := 0 outside their actual branch windows.
Replay reaches an unmatched vacuous residual. Move the producer's opening
marker before the crunch call, preserve the actual execution order, recapture,
and consume those steps inside their branch. Do not infer ownership by
matching substitution terms to later segments. Producer `f486834ebf` now
opens the window before crunching. A fresh production image and all 107
recaptures carry that fork identity; the actual cancellation proof crosses
the residual branch through the recorded substitutions. Full regression
validation passes at `3fb7763`:
`.gate-runs/3fb7763-20260906T161407Z.log`, **TRUE_EXIT=0**, with the
116 unconditional baseline rows, unchanged golden and 21 existing products.
Fixed 2026-09-06. BUG-032/039's reciprocal proof paths remain separate work.

## BUG-044 — induction retains clause facts from an outer environment
Status: fixed
Pinned-by: none (actual CD2-BOUND replay and its existing exact coverage pin)

The NS1 full gate at `ca5e1dd` exposes a rejected proof in CD2-BOUND.
The induction step replaces the environment with a fresh variable but clears
only value pins and literal facts, retaining outer branch/segment facts.
Recognizer lookup can select one of those facts by the syntactic ACL2 term
alone. The resulting proof mixes `env` and `e`; kernel checking rejects it.
This is a replay regression, not an accepted theorem with an extra axiom.

The repair clears the environment-bound facts and context aliases at the
induction step and checks recognizer lookup candidates against the expected
value-level proposition. Fourteen reset sites now share `clearEnvFacts`.
The affected build, existing coverage pin, focused CD2/denominator replays,
and static checks passed before the full checkpoint below. The earlier full gate
`.gate-runs/ca5e1dd-20260906T123257Z.log` remains `TRUE_EXIT=1`.

Fixed 2026-09-06 at the full checkpoint `.gate-runs/e7829b5-20260906T135512Z.log`
(`TRUE_EXIT=0`): 116/116 unconditional baseline rows, unchanged golden,
and all 21 existing mirror products. Earlier failed receipts remain failed.

## BUG-043 — proof-log reporting skips declarations with rule-class metadata
Status: fixed
Pinned-by: none (parsed-record regression in Tests/Ns1Contexts.lean)

Discovered 2026-09-06 on the real NS1 numerator/denominator capture.
`ProofLog.summary` and `ProofLog.splitByTheorem` matched `defthm` with only
three of its four fields. Lean supplies the optional fourth pattern as
`none`, so modern records carrying `:CLASSES` disappeared from the summary
and theorem segmentation. The canonical `ClauseTree.buildDevelopment`
consumer already matches all four fields; this did not remove its replay
rows or change their statements. No production consumer currently calls the
segmentation helper, while the CLI displays the summary.

The branch repair explicitly matches the class field in both helpers.
`Tests.Ns1Contexts` checks their names/count against all declaration records
in the unchanged real capture, including the target theorem. The full
checkpoint below validates the repair.

Fixed 2026-09-06 at the full checkpoint `.gate-runs/e7829b5-20260906T135512Z.log`
(`TRUE_EXIT=0`): 116/116 unconditional baseline rows, unchanged golden,
and all 21 existing mirror products. Earlier failed receipts remain failed.

## BUG-042 — USE instance substitutions are logged before term translation
Status: fixed
Pinned-by: none (proof-log payload; actual arithmetic-3 helper capture exposes the mismatch)

`prove.lisp`'s USE-HINT/PAYLOAD records `:LMI-LST` from the source hint,
while `:HYPS` contains ACL2's translated instances. The consumer applies
that raw substitution to the translated dependency statement, so source
macros such as `(* X Y)` and `(- Y)` disagree with the recorded `BINARY-*`
and `UNARY--` terms. It correctly refuses the mismatch. The real
FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT tree cites
UNIQUENESS-OF-+-INVERSES-LEMMA with both shapes; the clean d973 capture is
`.tmp/ns1/c2-d973-dependencies/pass1/basic-arithmetic-helper.proof-log`,
and the measured refusal is `c2-pass1-helper-first-replay-rerun.log`.

ACL2's `history-management.lisp:translate-lmi/instance` already computes
and adjusts the translated substitution before `sublis-var`. Replay needs
that evidence, aligned with the original LMI and instantiated hypothesis;
matching the result backwards or implementing source macro expansion in
the checker would conceal the missing record. The existing verbatim
instance check must remain. Other plain-instance consumers in the same
capture exhibit the same refusal. Nested and functional instances retain
their existing explicit scope boundaries.

The repair is implemented at fork `2f0dd071ca`: the successful, adjusted
alist is recorded at `translate-lmi/instance` and joined to the emitted
hypothesis by the pre-instance formula, raw substitution, and resulting
hypothesis. Source and translated LMIs are both retained; the replay's
verbatim instance check remains. The actual helper advances to its next
primitive-axiom/DP frontiers. `Tests.Ns1UseInstances` consumes an actual
ACL2 book using the same source macros and rejects missing, altered, and
misaligned records in memory. Clean corpus recapture is complete; the full
checkpoint below validates the repair.

Fixed 2026-09-06 at the full checkpoint `.gate-runs/e7829b5-20260906T135512Z.log`
(`TRUE_EXIT=0`): 116/116 unconditional baseline rows, unchanged golden,
and all 21 existing mirror products. Earlier failed receipts remain failed.

## BUG-041 — a top-level LOCAL defun is emitted as an encapsulation witness
Status: fixed
Pinned-by: none (proof-log provenance; Tests.Ns1LocalDefinitions pins the actual dependency capture)

The unchanged kestrel/arithmetic-light/nonnegative-integer-quotient book
declares NONNEGATIVE-INTEGER-QUOTIENT-DOUBLE-INDUCT inside LOCAL, outside an
ENCAPSULATE. The DEFUN emitter's remaining non-nil in-local-flg arm labels
it LOCAL-WITNESS. Reconstruction then rejects the witness outside a scope.
BUG-030 distinguished inherited LOCAL-INCLUDE-BOOK, but did not distinguish
this actual local helper from a constrained function's witness. The capture
at fork d03226496d is `.tmp/ns1/c2-d032-dependencies/nonnegative-integer-quotient.proof-log`;
`c2-d032-niq-tree.log` records the rejection. A repair must preserve local
definition provenance and admission evidence while preserving the existing
parametric statement boundary for encapsulated functions. `toWorld` already
includes witness bodies in the canonical model (ratified R6); the protection
is statement abstraction and the witness-dereference guard, not exclusion
from that model. Some older source comments still describe the superseded
exclusion mechanism; those comments are corrected with this repair.

Fork `d97312a6ba18` distinguishes LOCAL-HELPER using ACL2's actual encapsulate
stack, preserving the previous include-book and witness classifications.
The reader retains helper bodies and admission evidence, rejects helpers
inside encapsulate, and refuses conflicting definitions involving a helper
in the current flat model. The actual NIQ control changes only the two helper
SOURCE fields; cov-encapsulate's proof events are unchanged
(`.tmp/ns1/c2-local-helper-emission-comparison.log`). The permanent pin checks
the real captures and rejects misplaced provenance and conflicting bodies
with in-memory negative controls.

Fixed 2026-09-06. Full checkpoint gate
`.gate-runs/9a73b92-20260906T085449Z.log` records `TRUE_EXIT=0`: 102 permanent
captures at clean d973, the unchanged 116 unconditional baseline rows, and
all 21 existing mirror products. This closes ingestion of these private
helpers; the NIQ dependency proofs and the three NS1 mirrors remain open.

## BUG-040 — capture's source theorem census miscounts reader comments and redundant declarations
Status: fixed
Pinned-by: none (capture completeness metadata; exercised by actual arithmetic-3 sources)
The line-based source census counts three commented-out DEFTHMs in
arithmetic-3/bind-free/basic.lisp. In simplify.lisp, two explicitly written
declarations redundantly repeat already included theorems; ACL2 emits their
INCLUDE-BOOK records and starts no new proof. Comparing all source declarations
to fresh LOCAL proofs rejects both complete runs.
The NS1 fix uses one lexical census that respects comments, strings and escaped
names. A local-count shortfall is accepted only when every explicit source
name is present in the log; QED pairing, the scoped final theorem, failure and
capture-end checks still apply. The actual captures and existing negative
provenance tests pass. Redundant source declarations now receive a separate
metadata event, with no invented QED or new theorem offer; its control preserves
all 77 original events and adds exactly the declaration
(`.tmp/ns1/c2-redundant-event-comparison-final.log`).

Fixed 2026-09-06. Full checkpoint gate
`.gate-runs/d676937-20260906T072938Z.log` records `TRUE_EXIT=0`: all 101
permanent captures are stamped at d03226496d, the 116 unconditional baseline
rows and coverage golden are preserved, and the 21 existing mirrors pass.
This is a capture/consumer repair; the NS1 native mirrors remain open.

## BUG-039 — silent hypothesis relief omits its type-set basis
Status: fixed
Pinned-by: none (proof-capture/replay provenance; no interpreter-value divergence)
MOD-BOUND-LINEAR-ARG2 exposes two distinct missing records. The known-true
marker for PREFER-POSITIVE-ADDENDS-<'s ACL2-NUMBERP arithmetic-result hypothesis
omits the argument type-set and enabled recognizer tuple actually consulted.
The type-alist lookup marker for ACL2-NUMBERP Y omits the matched Y entry and
the requested numeric mask; its supporting clause literal is RATIONALP Y.
A literal-equality lookup therefore cannot replay either step, and inferring
new type facts in Lean would violate the emitted-data rule.
Fork `d03226496d` records the consumed recognizer basis without rerunning
its query, and the successful lookup's exact entry via its returned list tail.
Consumers use those records to gate kernel-proved primitive closure and the
existing type-set algebra. Clean MOD replay crosses both recorded steps;
its composed bound is conditional only on MY-FLOOR-LOWER-BOUND-ALT
(`.tmp/ns1/c2-d032-mod-dependency-closure-replay.log`). The hypothesis-basis
control preserves all 2083 original events modulo the new fields
(`.tmp/ns1/c2-hyp-basis-control-event-comparison.log`). This entry does not claim the bound or a native mirror complete.

Fixed 2026-09-06. Full checkpoint gate
`.gate-runs/d676937-20260906T072938Z.log` records `TRUE_EXIT=0`: all 101
permanent captures are stamped at d03226496d, the 116 unconditional baseline
rows and coverage golden are preserved, and the 21 existing mirrors pass.
This is a capture/consumer repair; the NS1 native mirrors remain open.

Reopened 2026-09-06 for the root-IF query in EQUAL-/'s DEFAULT-UNARY-/
hypothesis. The earlier recognizer and lookup repairs remain intact, but
`(IF (NOT (ACL2-NUMBERP X)) (NOT (ACL2-NUMBERP X)) (EQUAL X '0))`
has neither basis. The isolated producer at `268a219360` emits the actual
root mask 256, its addressed reachable leaf, and the pruned leaf's mask 0
(`.tmp/ns1/c2-known-if-clean-captures/basic-arithmetic-helper.proof-log`).
Production fork `f486834ebf` now includes that emission. The parser retains
the strict root/leaf structure; the consumer checks it using the existing
type-set walker and the actual branch facts. The exact hypothesis node
checks with the accepted axiom trio, and deleting its pruned leaf is rejected
(`.tmp/ns1/c2-known-if-actual-node.log`). All 107 production captures are
stamped at the new fork. Whole EQUAL-/ replay and full regression validation
remain pending. This consumer does not invoke a hypothesis DP.

Full regression recovery, 2026-09-06: the gate at `2953c78` records
`TRUE_EXIT=0` in `.gate-runs/2953c78-20260906T215722Z.log`. The repaired
source pins and controls pass, all 116 baseline theorem rows remain
unconditional, the golden is unchanged, and the 21 existing mirrors pass.
This closes this repair; NS1's three native BVCHOP mirrors remain open.

Reopened 2026-09-06 for NONNEGATIVE-INTEGER-QUOTIENT-UPPER-BOUND-LINEAR's
application of <-OF-*-OF-/-ARG1-ARG2. The known-true marker for `(< '0 J)`
has no recognizer/IF basis or parent record; its context contains integer,
nonnegative and nonzero facts for J. The current replay refuses that marker
(`c2-quotient-production-after-folds.log`; production NIQ log:20435ff).
Capture the actual type-set lookup/comparison route before adding its
consumer. Do not replace this hypothesis relief with a DP or infer the
missing type-set evidence. The earlier repaired basis classes remain intact.

Isolated progress, 2026-09-06: fork `3d78183cc7` observes the actual selected
route. Both upper-bound comparison nodes use the numeric table with masks
1 and 6 and result 256. Their reconstructed records now drive the existing
type-set membership and zero/positive-rational comparison proofs; both
actual nodes pass explicit kernel and axiom checks, with removed context,
removed route/basis, and changed-result controls rejected. All 462 original
events are unchanged modulo this new field. The whole quotient replay also
passes its following cited-TP recognizer after forwarding that marker's
existing citations; it now refuses the distinct FC suffix in BUG-051.
Receipts: `c2-known-comparison-actual-controls-rerun.log`,
`c2-known-comparison-event-comparison.log`, and
`c2-quotient-known-comparison-tp-whole.log`, under `.tmp/ns1/`.
Production fork `fd27e59021` now includes the observer; all 110 permanent
captures carry that stamp. Focused regression builds pass, including
`Tests.Ns1Comparison`, `Tests.Ns1Mod`, and the existing substitution,
positive/context and tamper controls (`c2-known-comparison-production-regression-build-rerun.log`).
Full regression for this increment remains pending. Constant-bound routes
in unselected `basic` events are retained but not implemented by this consumer.

Validated 2026-09-07: `.gate-runs/0f323b3-20260907T003817Z.log` records
`TRUE_EXIT=0`; all 116 unconditional baseline theorem rows and 21 existing
mirrors are preserved. This closes the selected comparison-table repair.
The unselected constant-bound consumer frontier remains as described above;
the quotient still requires BUG-051 and its ordinary book dependencies.


## BUG-038 — linear DP premises ignore the recorded clause rune set
Status: fixed
Pinned-by: none (actual BVCHOP upper-bound premise construction)
The linear premise adapter scans all end-of-book snapshot offers using only
max-term matching. BVCHOP-UPPER-BOUND's three linear leaves cite only
MOD-BOUND-LINEAR-ARG2-STRONG, but widening the adapter to arbitrary stored
hypotheses also supplied MOD-BOUND-LINEAR-ARG1 and MOD-BOUND-LINEAR-ARG2.
The rule proofs would remain kernel obligations, but these extra premises
are not justified by the recorded clause's cited rules. This is the earlier
DP-scan defect documented in the 2026-08-10 restructure audit; admission
bundle gating landed there, while ordinary clause replay remained ungated.

C2 threads each clause node's recorded rune set through the replay
context and gates linear injection on that set. Offers remain intact when
descending so a child can use its own cited rules. The actual upper-bound row uses only the cited strong MOD linear rule;
its composed row has no assumed DP condition. The clean scoped target tree
is `.tmp/ns1/c2-d032-upper-current-tree.log`; ordinary dependency conditions
remain visible until their own replays close.

Fixed 2026-09-06. Full checkpoint gate
`.gate-runs/d676937-20260906T072938Z.log` records `TRUE_EXIT=0`: all 101
permanent captures are stamped at d03226496d, the 116 unconditional baseline
rows and coverage golden are preserved, and the 21 existing mirrors pass.
This is a capture/consumer repair; the NS1 native mirrors remain open.

## BUG-010 — mixed/partial escaping within a symbol token
Status: fixed
Pinned-by: none (parser guards and matching differential cases recorded below)
The parser formerly refused mixed escapes, qualified escaped names and single
backslash escapes. ACL2 upcases only unescaped character runs and recognizes
only unescaped colons as package markers. NS1 encountered the actual qualified
formal `ACL2::|(CAR REMAINDER)|` in FLOOR's snapshot. The general token reader
now preserves that identity and empty escaped names, while rejecting malformed
escapes/package markers. `Tests.ParserTest` pins decoded identities and token
boundaries. The focused differential run checks all 25 symbol-escaping cases
(20 matches, five refusals), plus reader/number controls: 88 matches, two
unsupported, one unrelated known bug, five refusals, zero failures
(`.tmp/ns1/c2-reader-corrected-differential.log`). The full differential run has 549 matches, 138 unsupported, seven known
bugs, 30 refusals and zero failures; the full regression gate also passes. Import/export-table identity (BUG-013/015) remains a separate frontier.

Fixed 2026-09-06; full checkpoint gate
`.gate-runs/aec7fcd-20260906T034924Z.log` records `TRUE_EXIT=0`.

## BUG-013 — package-IMPORT symbol identity not modeled (nil/t/car duplicates)
Status: open
Pinned-by: differential
(MINIMAL fix landed 2026-07-11; the full import table remains — hence open.)
ACL2's ACL2 package IMPORTS ~977 symbols from COMMON-LISP
(`*common-lisp-symbols-from-main-lisp-package*`): `COMMON-LISP::NIL` IS
`nil`, `ACL2::NIL` resolves to it by import, and `'car` IS
`COMMON-LISP::CAR` (`symbol-package-name 'car` = "COMMON-LISP"). The parser
originally stored the literal source-text (package, name) pair UNRESOLVED,
so these were DISTINCT symbols — live wrong VALUES (the dangerous class):
`(equal 'common-lisp::nil nil)` = NIL vs ACL2 T; `(if 'common-lisp::nil
'truthy 'falsy)` = TRUTHY vs ACL2 FALSY; `(equal 'acl2::nil nil)` = NIL vs
T; `(equal 'car 'common-lisp::car)` = NIL vs T. Found during the lexorder
order-proof work: the nil/t duplicates are ALSO a second instance of the
BUG-012 pattern — two SExpr representations of one ACL2 value that
`lexorder`'s view collapses but `equal` distinguishes — falsifying
lexorder antisymmetry/transitivity over SExpr.
MINIMAL FIX LANDED 2026-07-11 (MDD-ratified option (i)): the parser maps
the import-resolved NIL/T spellings to the canonical `SExpr.nil`/`SExpr.t`,
and the COMMON-LISP::NIL/T identities are UNREPRESENTABLE as `Symbol`s
(`canonSym`, Syntax.lean) — restoring equal/if faithfulness for nil/t and
the view-injectivity the order proofs rest on (LexorderOrder.lean).
Regression guards + the still-open `car` row in complex-and-packages.lisp
(verified vs running ACL2 2026-07-11).
STILL OPEN — full import-table modeling (the fixed ~977 list; changes
builtin identities' packages and printing — e.g. `(equal 'car
'common-lisp::car)` and `symbol-package-name 'car`); options (ii)/(iii) in
the design doc §D5 addendum #2. Related frontier noted at BUG-002 §4 and
the lexorder note's representation section.

## BUG-014 — KEYWORD-package symbols duplicate keywords
Status: fixed
Pinned-by: none (fixed 2026-07-12 — regression guards `match` in
complex-and-packages.lisp)
`keyword::foo` IS `:foo` in ACL2 — KEYWORD is the keywords' HOME package
(not an import; verified vs running ACL2 2026-07-12: `(equal :foo
'keyword::foo)` = T, `(symbol-package-name 'keyword::foo)` = "KEYWORD").
Our parser built `Symbol {package := "KEYWORD", name := "FOO"}` for it — a
SECOND representation of the keyword `.keyword "FOO"` (the BUG-012/013
duplication pattern, third instance): a live wrong value (`(equal :foo
'keyword::foo)` = NIL vs T) and a falsifier of lexorder ANTISYMMETRY (both
representations have the same lexorder view `(name . "KEYWORD")`, so
lexorder held both ways between distinct values). Found during the
lexorder order-proof work — exactly where the memory of the pattern said
to look (the remaining duplicate-representation class after numbers and
nil/t). FIXED 2026-07-12: `canonSym` (Syntax.lean) additionally forbids
package "KEYWORD" (the `.keyword` constructor is the unique
representation), and the parser maps KEYWORD-package tokens to it
(Parser.lean). This completed `lexView?` injectivity, on which the order
proofs (LexorderOrder.lean) rest.

## BUG-015 — single-colon package markers not fully modeled
Status: open
Pinned-by: differential
(Interim fail-closed fix landed 2026-07-12; full external-set modeling
remains — hence still open.)
The CL reader (ACL2's reader) treats `pkg:name` (ONE colon) as
EXTERNAL-symbol access: `keyword:foo` IS `:foo` (the KEYWORD package
exports everything), `common-lisp:car` IS `common-lisp::car` (the standard
symbols are external), and `acl2:car` is a READER ERROR ("The symbol CAR
is not external in the ACL2 package" — the ACL2 package exports nothing).
All verified vs running ACL2 2026-07-12 (found while fidelity-checking the
BUG-014 fix). Our tokenizer originally split package markers on `::` ONLY,
so a single-colon token silently parsed as an ordinary ACL2-package symbol
with the colon IN ITS NAME (`'keyword:foo` → symbol "KEYWORD:FOO") — silent
wrong values (the dangerous class): `(equal :foo 'keyword:foo)` = NIL vs T,
`(equal 'common-lisp:car 'common-lisp::car)` = NIL vs T.
INTERIM FIX LANDED 2026-07-12 (Parser.lean): an unescaped colon is ALWAYS a
package marker (leading-colon keywords and `|…|`-escaped tokens are handled
earlier), so a colon-bearing token is intercepted up front and ONLY the
double-colon `pkg::name` form is accepted; single-colon `pkg:name` and every
other colon shape (`a:::b`, `a::b::c`, `foo::`, `pkg::name.x`) FAIL CLOSED
(parse error). Over-strict where ACL2 accepts external access, but never a
silent wrong value. Pinned in boundary.lisp (isolate path — a parse error
aborts the batched Lean stream, so these live with the other `<refused>`
boundary forms; 2 `known-bug lean <refused>` + control-guards
(`acl2::foo`/`keyword::foo`/`foo.bar` `match`, `|a:b|` under BUG-016) so
the fix cannot over-reject double-colon/dotted/escaped forms). The
`acl2:car` error case is not corpus-pinnable — the raw-Lisp abort emits no
value line. STILL OPEN — the faithful resolution needs external-ness per
package: trivial for KEYWORD (all external → map to `.keyword` like
BUG-014) and ACL2 (none → reader error), but COMMON-LISP's external set is
exactly the standard-symbol list — the BUG-013 import-table surface. Fold
into the BUG-013 full fix.

## BUG-016 — printer does not escape non-standard symbol names with `|…|`
Status: open
Pinned-by: differential
ACL2's printer wraps a symbol NAME in `|…|` bars whenever the name is not a
plain readtable-`:upcase` token — i.e. when it contains a colon, whitespace,
lowercase, or other special chars — so the printed form reads back as the
same symbol: `|a:b|` prints `|a:b|`, `|a b|` prints `|a b|`, `|abc|` (name
"abc", lowercase) prints `|abc|`, while `|FOO|` (name "FOO") prints bare
`FOO` (all verified vs running ACL2 2026-07-12). Our `Repr Symbol`
(Syntax.lean:79-81) renders the name VERBATIM (`a:b`, `a b`, `abc`), so the
printed form is not read-faithful for such names. Distinct from the
reader-side BUG-014/015 — parsing is CORRECT (`(equal '|a:b| '|a:b|)` = T,
`(symbol-name '|a:b|)` = "a:b"); only OUTPUT diverges. Surfaced 2026-07-12
by the BUG-015 control-guard round-trip. Pinned `known-bug bug:BUG-016 lean
a:b` on `'|a:b|` in boundary.lisp. Fix: teach the printer ACL2's
`needs-slashes`/`may-need-slashes` logic (axioms.lisp print path) — escape a
name that is not a bare uppercase token. Keyword printing (`:foo`) and the
plain-uppercase common case are already faithful; this is the escaped-name
tail.

## BUG-021 — four unwired `Logic.lean` primitives diverge from ACL2, were documented as faithful
Status: fixed
Pinned-by: differential (`evenp-expt-string.lisp`, 21 match entries incl.
the corner oracles `(expt 0 -1)`=0, `(expt 5 'b)`=1, `(evenp nil)`=T —
fixed to guard-off semantics AND wired into `callBuiltin`/`builtinNames`
2026-07-26, pin-first per H3; two LogicTest #guards that had pinned the
divergent behavior updated to the oracle values)
`Logic.evenp`/`Logic.oddp` match only `.atom (.number (.int n))` and give
nil otherwise; real guard-off ACL2 gives `(evenp nil)`=T, `(evenp 'abc)`=T,
`(oddp 3/2)`=T. `Logic.expt` funnels both args through `toInt`, truncating
rational bases (`(expt 1/2 2)`=1/4 in ACL2). `Logic.string_append` returns
`""` unless both args are strings (`(string-append "ab" 'c)`="ab" in
ACL2). All four oracle values verified against `acl2/saved_acl2` by the
2026-07-26 full-pipeline audit (F6). Latent — but `builtinNames` makes
wiring a one-line change, and the definitions claimed faithfulness. The
tier-1 paperwork commit first marked the definition sites ⚠
NOT-YET-FAITHFUL; the fix then replaced the marks with the guard-off
definitions, whose docstrings cite this entry.

## BUG-023 — the congruence-license lookup was a shape inference; :DEFTHM emits no rule-classes
Status: Lean-side consumption FIXED (2026-07-30, the perm-lane pre-merge
audit's convergent finding — the (fn, pos, R) registry match is now
ANCHORED to the step-cited `(:CONGRUENCE <name>)` rune in the processor's
:RUNES; a collapse whose matched spec is not step-cited hard-fails);
fork-side emission refinements OPEN
Pinned-by: none (proof-log consumption/emission, not interpreter
behavior; the Lean-side guard is the citation anchoring itself, which
fail-closes any uncited license)

Found by the perm-lane pre-merge audit (both reviewers independently,
2026-07-30). G2 rung 2's congruence registry (`congSpecOfFormula?` +
`replayCongCollapse`) shape-parses every strictly-earlier single-literal
local theorem and selected the license by (fn, arg-position, relation)
alone. Two defects in that:
1. INFERENCE where ACL2 emits the answer: the enclosing `:STEP`'s
   `:RUNES` names the licensing rule (`(:CONGRUENCE
   PERM-IMPLIES-EQUAL-ALL-REL-2)` at qsort *1/3.2) and
   `geneqv-refinementp` returns the exact `cr-rune` at the fork's push
   site (acl2/induct.lisp:102-114) — neither was consumed. FIXED
   Lean-side: the registry match must be step-cited.
2. The registry could not distinguish a theorem STORED as :congruence
   from a congruence-SHAPED :rewrite theorem, because the emitted
   `:DEFTHM` event carried only :FORMULA and :SOURCE — no rule-classes.
   With the citation anchoring this can no longer select a wrong
   license (the cited name gates it).
   **HALF LANDED (verified 2026-08-13):** the rule-classes ARE now
   emitted — `:DEFTHM` events carry a `:CLASSES` field (e.g.
   `acl2_samples/sorting/qsort.proof-log:39`:
   `(:DEFTHM PERM-IS-AN-EQUIVALENCE … :CLASSES (:EQUIVALENCE) …)`; also
   `:CLASSES (:REWRITE)`, `:CLASSES :TYPE-PRESCRIPTION`, `:CLASSES NIL`).
   STILL OPEN (fork): emit `:cong-rune` on abbreviation-expansion steps
   (one line at acl2/induct.lisp:158-177) — the per-step congruence
   rune is the remaining emission gap.
   **RT2 LANDING (2026-08-15, T1+2 sprint fork round-trip 2; acl2 @
   `e8d78e513d`).** Ask 3 SHIPPED the OTHER half of defect 1's
   emission: `:CR-RUNE` at the solidify site — the licensing rune the
   fork's `geneqv-refinementp` returns is now emitted, 361 records
   corpus-wide, and PERM-TLFIX's G1 replay reads the exact predicted
   rune. Two things this did NOT do, stated so no reader infers them:
   (a) the `acl2/induct.lisp` abbreviation-expansion site above is a
   DIFFERENT site and remains open — the Status line stands; (b) it did
   NOT fix class D's anchor (`cov-cong-consume`) — that step is a
   STORED-RULE rewrite, not a solidify site, so the push `:CR-RUNE`
   rides on never runs there, and its step-level `:RUNES` still carry
   only `((:DEFINITION SYNP))`.
Related (same audit, tracked in the design note, not bugs): the
:EQUIVALENCE-rule implicit self-congruences and :REFINEMENT rules are
licensing mechanisms with no emitted defthm shape at all — rung-3 work.

## BUG-024 — proof-log emission const-folded instantiated fields (`:UNREWRITTEN-TEST`, `:hyp`, induction `:MEASURE`)
Status: fixed
Pinned-by: none (proof-log emission, not interpreter behavior — no value
stream to diff; verified by the fold-back audit's corpus detector:
529 folded records before the fix, 0 after)

Found by the path-emission fold-back audit (reviewer A + default-refute
verifier, 2026-07-31, V1/A-F1). Seven emission sites instantiated recorded
terms with `sublis-var`, which builds through `cons-term` and CONST-FOLDS
ground primitive calls (even with an empty substitution, via
`cons-term1-mv2`) — the same mechanism as the 2026-07-26 F3 class, whose
fix moved `:LHS`/`:RHS` to `structured-sublis-var-plain` but missed these:
the three `:UNREWRITTEN-TEST` sites (`if-finish/if-test`,
`if-finish/begin-if`, `rewrite-if/constant-if-test` — all 529 corpus hits
came from the last), the three `:hyp-relief` sites
(`relieve-hyp/type-alist`, `/ground-unit`, `/ground-unit-search`), and the
induction `:MEASURE` instantiation (induct.lisp). Witness class: a
recognizer step `(CONSP 'NIL) → 'NIL` followed by `:IF-TEST-FALSE
:UNREWRITTEN-TEST 'NIL` — the field re-performed the collapse instead of
recording the term. FIXED (acl2 9f12ded573): all seven sites use
`structured-sublis-var-plain`, now loop-visible (program-mode
mutual-recursion) so the loop-mode induct.lisp site can call it. Blast
radius at fix time was zero (the parser stored, and the tree builder
dropped, all three `ifTest*` events; nothing read `:hyp`/`:MEASURE`
foldings on the gated corpus) — fixed at the source per "emission is dumb
logging".

## BUG-025 — `IF-FINISH/COMBINED` `:LHS` spliced rule-formal branches (uninstantiated + folded); guard emitted spurious no-op steps
Status: fixed
Pinned-by: none (proof-log emission — the Lean guard is the combined
recipe's running-term ground truth + the final `== rhs` gate, which
fail-close on any misuse; verified by the fold-back audit's detector:
547 hard formal leaks before the fix, 0 after; record count 729 → 138)

Found by the path-emission fold-back audit (reviewer C + verifier,
2026-07-31, V2/C-F1) — BUG-022's "related latency" gone live: the combined
step's `:lhs (mcons-term* 'if test left right)` used the UNREWRITTEN
formal-level branches under a non-nil rewrite alist, leaking rule formals
(`X`, `J`, `I`, `E`, …) into 547 of 729 corpus records — an `:LHS` that
was not a subterm of any running term (witness: FIX's body emitted
`:LHS (IF (ACL2-NUMBERP A) X '0)` for a step ACL2 never took). It also
silently disabled `bridgeIfNegTestSwap`'s target case (`swapped == lhs`
can never match a formal-leaking record) — fail-closed but a coverage
suppressor. FIXED (acl2 9f12ded573): `:lhs` is the ACTUAL input to
`rewrite-if1` — `(list 'if test rewritten-left rewritten-right)`, raw
cons — i.e. exactly the running subterm after the branch windows apply,
and the emit guard compares against the same shape, so a combined step is
emitted exactly when `rewrite-if1` changed the term (this dropped ~591
spurious no-op records the old folded guard let through).

## BUG-026 — the rewrite-if branch swap was UNRECORDED (`:SWAPPED-P`)
Status: fixed
Pinned-by: none (proof-log emission; verified by the fold-back audit's
exact detector — 19 swap occurrences across 7 corpus books, 0 `:SWAPPED-P`
keys before the fix, emitted after)

Found by the path-emission fold-back audit (reviewers A/C + verifier,
2026-07-31, V3). `rewrite-if` normalizes a rewritten test of the negation
shape `(if x nil t)` by stripping it and EXCHANGING the branches
(`rewrite.lisp` mv-let, scoping over all six if-window sites and both
`rewrite-if-finish` calls; `rewrite-if-avoid-swap` is attached to
`constant-nil-function-arity-0`, so `if-call` never un-swaps). The swap
was silent: window KINDs and if-record orientations were post-swap with
nothing marking it, so the replay worked only because two UNRECORDED
normalizations cancelled (the driver's kind↦branch binding vs its
`normalizeSwapsToward`/`bridgeIfNegTestSwap` re-derivation inventory,
~190 lines). FIXED (acl2 9f12ded573): `:swapped-p` is emitted on the six
if-left/if-right window begins, both if-test events, the combined record,
and the constant-test record. Consumed (2026-07-31): the tree carries
`swapped`/`innerSwapped`; the if-finish partition hard-checks window flags
against the combined record's; the inline-window anchoring uses the flag
for pre-swap branch naming. REMAINING (parent-arc epicycle item): the
`if1/if11` record family still lacks the field, so the shape-directed
swap-bridge inventory is validated-but-not-yet-retired — retiring it
(record-directed swap replay) is tracked in TODO.md.

## BUG-027 — truthy-equal edges widened the J6 solidify equation closure without ratification
Status: open — DECISION RECORDED (MDD 2026-08-02): NARROW via emission.
Emit the type-alist equation-edge justifications from the fork (ACL2
consulted those facts and has them) and gate the truthy-equal edges on
the emitted provenance. Open until that emission lands.
Pinned-by: none (replay-side derivation scope, not a differential-visible
divergence — no value stream to diff)

Raised by the fold-back audit (reviewer B, B-F7, 2026-07-31). The
solidify/type-alist recipe's clause-context equation closure
(`inScopeEquations`/`eqChain?`/`composeEqChain`) gained TRUTHY-EQUAL edges
(a TRUE `(equal a b)` branch fact decodes to `a = b` via
`Logic.eq_of_equal_ne_nil`) during the sorting-completion-2 arc. This
widens what the J6 verdict-class carve-out (ratified 2026-06-09) lets the
replay re-derive for a verdict-only type-alist step: the closure now
composes equalities ACL2 justified by its type-alist machinery from MORE
in-scope sources. Each edge is kernel-checked and fail-closed (the
composition must reach the node's emitted `:EQUIV-TERM` target), so this
is a carve-out SCOPE question, not a soundness hole: either ratify the
widened closure as part of the J6 verdict class (it re-derives only from
clause-context facts ACL2 itself consulted) or narrow it behind emitted
justifications. Decide at the parent-arc merge review.

## BUG-022 — the proof-log `:EQUIV` mislabel class: iff-only steps emitted `:EQUIV EQUAL`
Status: fixed (emission sites); one emission-GAP sibling documented open
Pinned-by: none (proof-log emission, not interpreter behavior — no value
stream to diff; the guard is the Lean replay's R-typed chain barrier,
which fail-closes on any mislabeled step it meets: an iff-only fact
consumed as an eval-equality cannot elaborate)

Found by the equiv-lane pre-merge audit (outside reviewer, 2026-07-30).
Four sites in the fork share ACL2's or-shape collapse guard
`(and unrewritten-test (geneqv-refinementp 'iff geneqv wrld)
(equal unrewritten-test left))` or an explicit `*geneqv-iff*` guard, under
which the step is IFF-only (the produced 'T agrees with the value only in
truthiness); the emissions labeled them `:equiv 'equal`:

1. `rewrite.lisp` rewrite-if-finish combined step — FIXED (acl2
   2265010346, equiv-lane inc-2a): `:equiv` recomputes the guard.
2. `rewrite.lisp` rewrite-if quotep-test arm — FIXED (this entry's
   commit): when the truthy-constant test's collapse guard fires, ACL2
   returns `*t*`, not the rewrite of `left` — the record's `:rhs` ALSO
   diverged (said `(subst left)`); now `:rhs *t*` + `:equiv 'iff` under
   the recomputed guard.
3. `rewrite.lisp` rewrite-if11 type-alist-disjoint arm — FIXED (this
   entry's commit): explicitly `*geneqv-iff*`-guarded, `term => 'T`
   IFF-only; was `:equiv 'equal`, now `'iff`. No corpus occurrence yet.
4. `rewrite.lisp` rewrite-if-finish must-be-true arm — OPEN (an emission
   GAP, not a mislabel): the collapse returns `*t*` with NO rewrite-step
   emitted at all. A consumer meeting it fails closed on the chain
   mismatch (the recorded next step's lhs will not occur). Emit when a
   record demands it.

Related latency (same audit): the site-1 combined step's `:lhs`
`(mcons-term* 'if test left right)` splices the REWRITTEN test with
UNSUBSTITUTED left/right — only well-formed when the rewrite alist is
nil; no corpus record exercises a non-nil alist there yet. Fix by
substituting left/right when a record demands it. [This latency went
LIVE and is fixed — see BUG-025.]

## BUG-020 — reader ignores CL's terminating macro characters (fail-OPEN)
Status: fixed
Pinned-by: differential (`reader-terminators.lisp`, 4 match entries —
fixed 2026-07-26 by giving `isAtomChar` the same terminator set as
`isCharTokChar` / `*acl2-read-character-terminators*`; `;` cannot be
pinned in the corpus format and backquote/comma are unmodeled forms —
they now TERMINATE tokens, and a backquote form fails parse loudly)
`Parser.lean`'s `isAtomChar` USED TO end tokens on only
`( ) space \n \r \t` — CL's terminating macro characters
`"` `'` `` ` `` `,` `;` did NOT end a token, while `isCharTokChar` (the
`#\` path) already carried ACL2's real terminator list: an internal
inconsistency. Verified head-to-head (audit F5): ACL2 reads
`(A B;C D)` as `(A B D)`, `(A'B)` as `(A 'B)`, `(A"b")` as `(A "b")`;
the old reader took `B;C`, `A'B`, `A"B"` as single tokens — SILENTLY.
Unlike BUG-010/BUG-015, which hard-fail, this WAS the reader's one
fail-open gap, and it WOULD HAVE BECOME a live soundness hole the
moment gen-world output was wired into the certified pipeline (TODO's
frontend-replacement item) — which is why it was closed as a
prerequisite for that wiring rather than left open.
Fix (2026-07-26): `isAtomChar` was given the same terminator set as
`isCharTokChar` (`*acl2-read-character-terminators*`), and the family
was differential-pinned (the `Pinned-by` line above records what could
and could not be pinned in the corpus format).

## BUG-019 — `local` witnesses entered the World: replayed statements stated about the witness
Status: fixed
Pinned-by: none (pattern-corpus pin: cov-encapsulate's log carries
`:SOURCE :LOCAL-WITNESS` — sig-gated by check-pattern-map; a
differential form cannot express a replay-layer statement bug).
Fix EVOLUTION (2026-08-04, Phase 4's witness scoping — the ratified
tag+scope resolution): the interim fail-closed PARSE REFUSAL is
replaced by structural exclusion — a `:LOCAL-WITNESS` defun is
recorded as a SCOPED `witnessDefun` event (hard-fail outside any
encapsulate bracket) and `Development.toWorld` excludes it BY
CONSTRUCTION, so the certified world never contains a witness body
and the false-green statement substitution is unreachable
(cov-encapsulate now reconstructs and replays honestly red — the
constrained fn is opaque; equisort reconstructs end-to-end).
Every `.defun` event entered the World unconditionally
(ClauseTree.lean), and the fork emitted an encapsulate/defstub/
defevaluator LOCAL witness's admission as a plain `(:DEFUN …)` — so the
World bound the constrained function to its DISCARDED witness body, and
every replayed statement (and every `total:`/`tp:` hypothesis) was about
the witness instead of the constrained function. cov-encapsulate
reported 2/2 REPLAYED, unconditional and axiom-clean, about `λx. 0` —
while the same world validated `(EQUAL (CF X) '0)`, which real ACL2
refuses as a theorem (surfaced by the 2026-07-26 full-pipeline audit,
F1/CONFIRMED; the mechanism was known as a design note since
2026-07-20 — what the audit established is that it failed GREEN).
Nothing false was kernel-certified (each replayed statement is a true statement
about the witness world); the defect is STATEMENT SUBSTITUTION.
Fix (2026-07-26): the fork emits explicit provenance on every
world-entering `:DEFUN` (`:ADMITTED` / `:INCLUDE-BOOK` /
`:GROUND-ZERO` / `:LOCAL-WITNESS` — detected via `in-local-flg`, the
`local` macro's own binding), and the parser HARD-FAILS on
`:LOCAL-WITNESS` (and on missing/unknown provenance) with the named
frontier. Encapsulate SUPPORT (stating replayed statements over the exported
:CONSTRAINT list) remains an unbuilt frontier; the four S2b probe
books were rewritten from defstubs to disabled real defuns (their
green rows had been witness-substituted too). Known ADJACENT surface,
out of this fix's scope: local defTHMs' rules (ordered-perms) are
recorded in `(:RULES …)` without locality provenance — rule-provenance
is the same invariant one layer up.

## BUG-018 — duplicate `let`/lambda bindings: ACL2 refuses, we bind (inconsistently)
Status: open
Pinned-by: differential
Real ACL2's translate REJECTS a duplicate bound variable — `(let ((x '1)
(x '2)) x)` and its translated form `((lambda (x x) x) '1 '2)` both give
"improper let expression because it attempts to bind X, which occurs more
than once in the list" (verified against `acl2/saved_acl2`, 2026-07-25).
Our interpreter evaluates both, and — worse — the two spellings of what
ACL2 regards as ONE construct disagree with each other: the surface `LET`
arm's binding fold is last-binding-wins (`(let ((x '1) (x '2)) x)` ⇒ `2`),
while the LAMBDA arm's `bindArgsOver` is first-formal-wins
(`((lambda (x x) x) '1 '2)` ⇒ `1`). Surfaced by the S2 scoping audit
(2026-07-25; the LET side is pre-S2, the lambda side widened it). Fix
direction: refuse duplicate bound variables in both arms (`none`), matching
translate — a well-formedness check, not a semantics choice.

## BUG-017 — builtin dispatch keys on symbol NAME only, dropping the package
Status: open
Pinned-by: none (packages are only partially modeled — BUG-013/015 interim
fail-closed handling refuses the multi-package forms that would express a
divergence, so no differential form currently reaches the dispatch with a
same-name/foreign-package symbol)
`evalOpt` resolves an application head world-first, then falls to
`callBuiltin s.name` (EvalOpt.lean) — the builtin table is keyed by the
symbol's NAME with the package DROPPED. In real ACL2, `MYPKG::CONSP` (a
fresh symbol in a package that does NOT import `COMMON-LISP::CONSP`) is an
undefined function, not the builtin; our interpreter would silently give it
builtin semantics — the dangerous silent-wrong-value class. Not triggered
by the current corpus (single-package; the BUG-015 interim parser refuses
most multi-package forms fail-closed). Surfaced by the 2026-07-18 pre-merge
audit of the induction-generality arc (inherited, not introduced, by it).
SCOPE WIDENED by S2 (audit 2026-07-25): the same name-only `isNamed`
dispatch now also selects the SPECIAL FORMS — `QUOTE`/`IF`/`LET`/`LET*` and
the new `LAMBDA` application head — so a foreign-package `MYPKG::LAMBDA`
gets binder semantics the same way `MYPKG::CONSP` gets builtin semantics.
Same fix (full symbol identity), one more surface.
Fix direction: key the builtin table by full symbol identity (the canonical
COMMON-LISP/ACL2 homes), which is the same import-table surface as the
BUG-013 full fix — fold into it.

## BUG-012 — SExpr admits non-canonical numbers outside ACL2's value space
Status: fixed
Pinned-by: none (fixed 2026-07-11; the junk values were UNREACHABLE from
the ACL2-visible surface, so no differential form could exhibit them — the
divergence lived in the ∀-env quantification of replayed statements, and the
fix makes them UNREPRESENTABLE)
`Number` formerly admitted `.rational 2 4`, `.rational 1 1`, `.decimal …` —
multiple representations of one rational value — while ACL2's value space
has exactly one (reduced ratio, or integer). Recognizers accepted the junk,
arithmetic normalized it (`(* 1 x)` canonicalizes), and `equal`/`==` are
structural — so VALUE-equal junk representations were distinguishable.
Consequences (found by the external-knowledge WP3 spike, 2026-07-11,
countermodel EXECUTED):
(a) `lexorder` transitivity was FALSE over all SExpr — x=((2/4) . 5),
    y=((1/2) . nil), z=((2/4) . 3) gave lexorder x y = T, y z = T,
    x z = NIL (the cons branch's structural `==` vs value-compare on cars);
(b) replayed statements of canonicity-sensitive ACL2 theorems were FALSE as ∀-env
    statements — verified `(equal (* 1 q) q)` = NIL for q = `.rational 2 4`,
    so e.g. `(implies (rationalp x) (equal (* 1 x) x))` (a true ACL2
    theorem) had a false replayed statement.
NOT a proof-of-false-statement unsoundness (a false hypothesis can never be
discharged — fail-closed), but a statement-meaning divergence of the
trust-note class, blocking the external-knowledge D5/WP3 order proofs.
FIXED 2026-07-11 (MDD-ratified Option A — mirror ACL2's value-space
restriction at the type level; docs/notes/2026-07-11_canonical-number-
design.md): `Number.rational` carries a decidable canonicity invariant
(`canonRat`: denominator ≥ 2, reduced), the unreachable `.decimal`
constructor is DELETED, and `Logic.mkNumber` is the proving smart
constructor (the sole construction route). Junk is unrepresentable; the
lexorder order proofs (LexorderOrder.lean) rest on the injectivity this
buys. Gates green with behavior byte-identical (the values were already
canonicalized dynamically).

## BUG-011 — ACL2's own numeric reader macros `#f` / `#d` / `#u`
Status: open
Pinned-by: differential
`*acl2-readtable*` redefines several `#` dispatch chars via
`modify-acl2-readtable` (acl2.lisp) → `define-sharp-f`/`-d`/`-u`; the source is
acl2-fns.lisp (`sharp-f-read`:1469, `sharp-d-read`:1531, `sharp-u-read`:1416,
`read-digits`:1444). These read into EXACT ACL2 numbers, not host floats.
`#f` and `#u` FIXED 2026-07-09 (Parser.lean `readSharpF` + the `#u` case):
`#f<float>` rationalizes decimal/hex float syntax to an exact rational (verified
vs real ACL2: `#f1.5`=3/2, `#f2.0`=2, `#f-1.5`=-3/2, `#fx1.8`=3/2, `#fx1p4`=16,
`#f1e3`=1000, `#f1.5e-2`=3/200); `#u<num>` discards `_` separators, with a
B/O/X prefix taken as radix (`#u1_000`=1000, `#ux1F`=31, `#ub1_0_1`=5).
REMAINING (still open): `#d` (double-float / the `df` feature) — no double-float
type is modeled, so it stays fail-closed (`<refused>`), pinned
`known-bug bug:BUG-011 lean <refused>` in sharp-numeric.lisp; needs the df type
first (a modeling decision, deferred). Distinct from BUG-004 (bare `.`-token
floats, no `#`) and BUG-005 (radix `#x/#b/#o/#Nr`, the standard CL reader).
