# qsort-frontiers arc — working notes (2026-07-20)

Branch `mdd/qsort-frontiers` off main 3c8a197. Target: the remaining qsort /
bsort / sorts-equivalent frontier rows (golden rows as of 35/79).

## Investigation results (2026-07-20)

### `*-IS-ISORT` (MSORT/QSORT/BSORT-IS-ISORT) — functional instantiation wall

All three are `:use (:functional-instance …)` applications of equisort's
constrained theorems (`strong-ssortfn1-is-ssortfn2` / `weak-sortfn1-is-sortfn2`),
proved about ENCAPSULATED functions. Two distinct gaps:

1. **Emission gap (small):** the `apply-top-hints-clause` node's recorded
   rewrites navigate an IF-conjunction of the six instantiated constraint
   obligations, but that root term is never emitted (`:INPUTCLAUSE` is the
   goal clause only). Paths miss → `pathStepsFromFrames` error.
2. **Mechanism gap (the real wall):** the log records the encapsulate's LOCAL
   WITNESSES as plain `:DEFUN`s — the encapsulate boundary is not emitted at
   all, so our world gives `ssortfn1/2` the witness bodies and the mirror of
   the constrained theorem is about the witnesses. That cannot justify the
   msort/qsort instances. Faithful replay needs the constrained theorem stated
   WORLD-PARAMETRICALLY (constraints as rule-hypotheses — exactly the L3
   encapsulate trajectory) plus an instantiation step that discharges the
   constraint obligations via the recorded chain. Design-review item; NOT
   started.

### HOW-MANY-FILTER-1 (and the ALL-REL-FILTER / composeSplit classes)

One row peeled through FIVE stacked walls; fixes landed for the first five
(each also hit by other rows — see the classes):

1. **Stale branch frame after a folded root collapse** (`if-finish/combined`
   error): the dead-branch/identity relaxation arms replayed a ROOT
   constant-test collapse but did not extend `strip`, so the next sibling's
   gstack branch frame mis-navigated. Fix: both arms now mirror the generic
   root-if strip rule. (NodeCore)
2. **Surviving-branch display folds** (ALL-REL-FILTER-2 signature):
   `sublis-var`/`cons-term` pre-evaluates ground `(EQUAL 'c1 'c2)` tests
   inside the SURVIVING branch of a recorded collapse lhs. Fix: the folded-
   collapse arm now pins the test + record self-consistency (rhs == recorded
   taken branch) and replays the collapse on the RUNNING branch; subsequent
   recorded exec/collapse steps reconcile the folds, each fail-closed.
   (NodeCore)
3. **Constant-resolved tests in the split spine** (`composeSplit
   how=constant`, ALL-REL-RM-1 signature): a test that collapsed to a quoted
   constant under earlier splits is re-derived by evaluation (decide),
   fail-closed against the recorded verdict. (Waterfall/Compose)
4. **DP-fact cone slicing**: `proveDpFact` can now run the split fallback on
   the CONCLUSION-CONE values when the full value count exceeds the split
   bound (deterministic relevance slice mirroring `dpValExpr` abstraction;
   out-of-cone values + their hypotheses cleared at the split goal — a fact
   needing them fails loudly). `total ≤ 3` behavior unchanged. (Discharge)
5. **Leaf tactic: split hypothesis ifs** (`split_ifs at *` in branch 2): a
   `toBool` match stuck on an unreduced decidable if in a HYPOTHESIS starved
   omega of the plus-equation fact. Both *1/3.5 and *1/3.1 tau leaves now
   discharge ✓ (were ◌/✗). Also: `proveDpFact` leaf failures now report the
   failing LEAF goal, and `dpSplitVars` takes explicit binder names.

**Remaining bottom for this row (NOT fixed):** literal 4's
`LEXORDER-TRANSITIVE` relief is `relieve-hyp/free-type-alist` where the
type-alist entry was DERIVED by forward-chaining (`LEXORDER-TOTAL`) from
another literal's falsity. Only the marker is emitted, not the derivation —
the known "type-alist derived entries" class. Fix at the source: emit the
type-alist entry's provenance (parent literal(s) + FC rule), then replay that
derivation. Instrumentation + recapture item.

### Increment 2 — recognizer booleanness in the DP leaf tactic (2026-07-20)

TRUE-LISTP-ISORT's *1.1/2'' tau leaf needs `trueListp` two-valuedness
(`≠ nil → = t`) — what tau itself knows about every recognizer. Blocker
found empirically: `Logic.toBool`'s global `@[simp]` eq_def unfolds
`toBool X` on a SYMBOLIC recognizer application into a stuck raw `match`
that no lemma can rewrite (matcher-aux keying; reuse does not apply across
modules). Fix: the leaf tactic erases `-Logic.toBool` and adds the
propositional bridges `Logic.toBool_eq_true/false` +
`Logic.trueListp_ne_nil_iff` (new lemmas in Logic.lean, NOT global simp).
The leaf then closes in ~2 s. TRUE-LISTP-ISORT's discharge went ◌→✓ and the
row advanced into the definition-chain IF-normalization class (the known
`(EQUAL X 'NIL)` vs `(IF X 'NIL 'T)` ×5 signature — now ×6).

Future recognizer leaves will want the same bridge per recognizer — if a
third one appears, registry-ize (name ↦ booleanness lemma, dpLiftHeads
style) instead of growing the simp list ad hoc.

### Increment 3 — the ALL-REL composer walls (2026-07-20)

Three linked fixes, all driven off the ALL-REL-FILTER-1 / ALL-REL-RM-1
trees (qsort book):

1. **∧-decomposition traces** (`parseTraceTree`): on `(if v X 'nil)`,
   if-interp emits the SEGMENT-OPEN leaf `v` (the `[v]`-segment child of
   `lit ≡ v ∧ X`) and CONTINUES at the SAME path — the leaf is not
   terminal, which our grammar rejected as "trailing events". Reading for
   the composer: the decision split on `v` (¬v → literal is 'nil and the
   `[v]` branch is selectable; v → the continuation's decisions).
   Synthesized as exactly that split; every downstream check stays
   fail-closed.
2. **collapseEval takes constant-collapsed tests**: when an if TEST
   collapses to a quoted constant (litFact-driven), take the branch with
   `re_if_true/false` instead of leaving the if "in place" (previously
   only composer-`facts`-resolved tests selected branches). Also: the
   identity if-simplification arm now delegates symbolic-test running
   subterms to collapseEval (record folded past the constant — observed
   `'T ⇒ 'T` with running `(IF (EQUAL (CAR X) E) 'NIL 'T)` under that
   segment literal's falsity). TraceTree/parseTraceTree/collapseEval
   moved above replayRewritesWith for this.
3. **Segment-justified branch-substitution + fact transport** (Core):
   remove-trivial-equivalences justified by a SEGMENT literal (not in
   the walked disjunction) — its falsity is already proved (segFacts),
   so no case split: derive var = val, diffCollapse the disjunction, and
   TRANSPORT every in-scope litFact/segFact across the substitution
   (appended; originals keep index bindings), each bridged along the
   var≡val chain, hard-failing if unbridgeable.

Rows: ALL-REL-FILTER-1 ✓, ALL-REL-RM-1 ✓ (36→38 expected pending sweep).
ALL-REL-RM-2 unchanged (residual-survivor mismatch — different class).

### Increment 4 — emitted leaf segments (fork c648e0bd5a) + spine arms

The ALL-REL-RM-2 investigation exposed that the leaf→branch link is
UNDERDETERMINED by the current emission: `convert-assumptions-to-clause-
segment` drops literals subsumed by an assumed constant equality (e.g.
`FN='GT` true drops `(EQUAL FN 'LT)`/`(EQUAL FN 'LTE)`), so distinct
leaves map to overlapping recorded branches and derivable-falsity
selection is ambiguous. Per the no-inference rule: EMIT MORE —
`emit/if-interp/leaf` now carries `:SEGMENT` (the exact constructed
segment) on segment-* leaves (fork commit c648e0bd5a; full recapture).
Consumers: parser (required for segment outcomes, forbidden on dropped),
`SplitDecision.leaf`/`TraceTree.leaf` threading; composeSplit selection =
EXACT emitted match first, falling back to derivable-falsity uniqueness
when the Satriani/subsumption post-pass MERGED segments (complementary-
literal consensus — observed `[LT,LTE,GT,LEX] + [LT,LTE,¬GT,LEX] →
[LT,LTE,LEX]`); the ∧-synthetic split's fSide leaf carries the open
leaf's emitted segment.

Also this increment (spine arms, from the same row):
- Core: VACUOUS residual path — a last literal collapsing to 'nil with an
  EMPTY segment pushes accClause as the child; all its literals have
  falsity facts, so the child's proof contradicts the path (ex falso).
- collapseEval: flipped-EQUAL spine-fact lookup (logic_equal_comm
  transport, mirroring composeSplit's resolved-test path).

### Increment 5 — EQUAL transport through segment equalities (2026-07-21)

ALL-REL-RM-2's last wall: an identity `'T ⇒ 'T` if-simplification with
running `(IF (EQUAL D E) 'NIL 'T)`. In scope: `(NOT (EQUAL D (CAR X)))`
false (so D = (CAR X)) and `(EQUAL (CAR X) E)` false — ACL2's type-alist
canonicalized `(EQUAL D E)` through the segment equality. collapseEval
now resolves an `(EQUAL x y)` test via: direct fact, commuted fact
(`logic_equal_comm`), or ONE transport step through an in-scope segment
equality (`logic_not_equal_nil_eq` + `congrArg`, all four orientations) —
a bounded, proof-carrying rule set mirroring if-interp-assumed-value2;
anything beyond stays unresolved and fail-closes. The identity-arm error
now also lists the in-scope seg/lit fact keys (frontier forensics).

ALL-REL-RM-2 ✓ → 39/79.

### Increment 6 — the EQUAL-nil normalization class (2026-07-21)

`rewrite-equal`'s built-in NIL case (rewrite.lisp:18089-92) is
UNCONDITIONAL and never recorded: `(equal 'nil x)` / `(equal x 'nil)` ⇒
`(if x 'nil 't)`. This was the `(EQUAL X 'NIL)` vs `(IF X 'NIL 'T)`
chain-end signature (×6 rows + PERM-IMPLIES-EQUAL-ALL-REL-2). Landed:

- EvalLemmas: `logic_equal_nil_eq_ite`, `re_val_if_nil_t`,
  `re_equal_nil_norm_l/_r` (fuel-eq between the two forms, existential
  conv hypothesis so `proveConv` feeds it directly).
- NodeCore: `bridgeEqualNilNorm` — fires ONLY on the exact shape (same
  `x`, reached `(EQUAL 'NIL x)`/`(EQUAL x 'NIL)`, recorded
  `(IF x 'NIL 'T)`); wired at both chain-end mismatch sites (definition
  recipe, literal chain).
- Follow-the-row arms surfaced by APP-NIL *1/3 (each exact-shape,
  fail-closed): branch-substitution justified by the VARIABLE literal's
  own falsity (`X ⇒ 'NIL` from segment `(X)`); clause-level
  EXECUTABLE-COUNTERPART steps (remove-trivial-equivalences' ground
  evaluations — replayExecGround + diffCollapse across the disjunction);
  the ground-'T literal closer (ATM/TYPE-SET-TRUE, `:RESULT :TRUE`).
- composeSplit: VACUOUS singleton arm (segment-false leaf on a singleton
  clause — the emitted segment + accClause child contradicts the path,
  ex falso; mirrors the spine's vacuous residual arm).

Rows confirmed: APP-NIL ×2 ✓, TRUE-LISTP-REV ✓, TLP-APP-NIL ✓,
TRUE-LISTP-ISORT ✓ (+5). PERM-IMPLIES-EQUAL-ALL-REL-2 advanced to
branch-substitution UNDER THE PERM EQUIVALENCE — genuine L2
R-parameterized rewriting; PARKED as design wall #3. REV-REV advanced to
a post-substitution path-navigation mismatch (new signature).

### Increment 7 — CAR-RM + EQUAL-CONS (fold set + normalization variants)

- collapseEval fold set (each pinned to if-interp's own rules,
  rewrite.lisp:3671-3800): GROUND-PRIMITIVE cons-term fold (argument-
  ground application of an UNDEFINED head folds via the exec carve-out —
  `(CAR 'NIL) ⇒ 'NIL`, CAR-RM); `(equal (equal a b) 't) = (equal a b)`
  and mirror (lemmas `logic_equal_equal_t_r/_l`).
- bridgeEqualNilNorm: the EQUALITYP variant (rewrite.lisp:18093) —
  reached `(EQUAL (EQUAL a b) r)`, recorded
  `(IF (EQUAL a b) (EQUAL r 'T) (IF r 'NIL 'T))` — lemma
  `re_equal_equalityp_norm` (two-valuedness of Logic.equal).
- Branch-substitution: justifying literal LAST in the clause → keep the
  now-trivial literal (nothing later references it) and walk the
  substituted clause directly (EQUAL-CONS Subgoal 4, chained
  substitutions).
- collectContextDemands: recognizer/true|false nodes now demand their
  context fact (a later literal being the negation — hoisting is a no-op
  when derivable otherwise).
- composeSplit vacuous arm: accept the UNIQUE child whose clause is an
  order-preserving SUBSET of the constructed residual
  (subsumption-simplified push; every used literal still needs its own
  falsity fact).

Rows: CAR-RM ✓, EQUAL-CONS ✓.

## Status

- Increments 1–6 verified + committed (c947d97, f1a0ee2, 9376778,
  8f5dca4, 1cae4dd, 4f6a7e4): 45/79, DP ✓24 ◌12 ✗0, fork c648e0bd5a.
- Increment 7 landed (CAR-RM, EQUAL-CONS → 47/79 expected); sweep
  pending.
