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

## Status

- Fixes 1–5 landed on the branch; full-corpus sweep + golden review pending.
