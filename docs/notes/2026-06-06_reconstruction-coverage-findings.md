# Reconstruction coverage findings & improvement plan

**Date:** 2026-06-06
**Branch:** mdd/hand-proof-my-len-my-app
**Method:** 8 targeted ACL2 proofs in `acl2_samples/recon-tests/`, each isolating
one or more features. Captured `.proof-log` + reconstructed `.dump` via
`scripts/recon-test-dump.sh`, then compared source ↔ log ↔ dump.

Goal of this exercise (per the §D.1 if-simplification fix that preceded it):
harden the proof-log → proof-tree **reconstruction** before building the
`my-len-my-app` replay against it. We may change **any** stage (ACL2 producer,
reconstruction, or output) but must avoid *all* fragile heuristics: the proof
tree must be built **deterministically** from what ACL2 logs.

> ⚠ Snapshot note: line numbers below refer to the logs/dumps regenerated on
> 2026-06-06. `*.proof-log` and `*.dump` are gitignored; regenerate with
> `./scripts/recon-test-dump.sh`.

---

## Results at a glance

| File | defthms in source | theorems reconstructed | verdict |
|------|------------------|------------------------|---------|
| `00-direct` | 3 | **0** | no `:DEFTHM` events emitted at all (F2) |
| `01-multi-theorem` | 3 | 3 | separation OK; but proof *bodies* are empty shells (F3) |
| `02-rev` | 5 | 5 | OK after F1 fix; bodies still shells / clause tree dropped (F3) |
| `03-linear` | 3 | 3 | all render as bare "direct proof", no reasoning (F3/F4) |
| `04-multi-case-induction` | 2 | 2 | bare "direct proof"; induction/case detail gone (F3) |
| `05-hints` | 4 | 4 | hint provenance (`:use`/`:induct`/`:in-theory`) absent (F8) |
| `06-measure` | 1 | 1 | OK after F1 fix; measure/defun context dropped (F5/F7) |
| `07-mutual-recursion` | 2 | 2 | ground theorems render as "direct proof"; bundle not modeled (F5) |

> The `02`/`06` counts above are **after** root-causing F1 (below) and fixing
> the two test-proof bugs it exposed. Before that, `02` reconstructed only 2 of
> its theorems and `06` zero — both because their logs were silently truncated.

The distinct waterfall processors that appeared across these logs:
`PREPROCESS-CLAUSE`, `SIMPLIFY-CLAUSE`, `SETTLED-DOWN-CLAUSE`, `PUSH-CLAUSE`,
`ELIMINATE-DESTRUCTORS-CLAUSE`, `ELIMINATE-IRRELEVANCE-CLAUSE`,
`FERTILIZE-CLAUSE`, `GENERALIZE-CLAUSE`, `APPLY-TOP-HINTS-CLAUSE`.
Reconstruction models exactly **one** of these (the rewriter detail inside
`SIMPLIFY-CLAUSE`); all others are silently dropped.

---

## Findings

### F1 — CRITICAL (producer): a failed event silently truncates the log
**Root-caused (2026-06-06).** The logs were not mysteriously truncated by the
instrumentation — an *event failed*, `ld` halted with `(:STOP-LD 2)`, and under
`:structured` format ACL2's error text is **suppressed**, so the log just ends
with no failure record. Reproduced by re-running each file *without*
`:structured`:

- `02-rev`: `rev-app` genuinely fails in base ACL2. Checkpoint
  `Subgoal *1/2': (implies (not (consp a)) (equal (rev b) (app (rev b) nil)))`
  needs `(app x nil) = x` on true-lists — supporting lemmas (`true-listp-rev`,
  `app-nil`) the test didn't provide. `ld` stops; `rev-rev` never runs.
- `06-measure`: `ack`'s `:measure (llist ...) :well-founded-relation l<` fails —
  `LLIST` is undefined in base ACL2 (it lives in
  `books/ordinals/lexicographic-ordering`): `ACL2 Error [Translate] ... LLIST
  has neither a function nor macro definition`. `ld` stops; `my-len` and
  `count-down-zero` never run.

Two distinct problems were tangled here:
1. *Test-proof bugs* (now fixed): `02` gained the missing lemmas; `06`'s `ack`
   was replaced with a summed-measure `zip-lists` that stays in base ACL2. Both
   logs are now complete (5/5 and 1/1 theorems).
2. *The real producer finding* (still open): the `:structured` logger emits **no
   failure/abort event** and suppresses ACL2's error output, so downstream
   cannot distinguish "proof complete" from "`ld` aborted on a failed event".
   This is the producer-side "never silently skip".

Stopgap already applied: `scripts/capture-proof-log.sh` had its redirect fixed
(`2>&1 > OUT` → `> OUT 2>&1`, which previously sent stderr to the terminal) and
now greps the output for `:STOP-LD`/`FAILED` and warns that the log is
incomplete. The durable fixes are P-side (emit a failure event) and R-side (R5
completeness check).

### F2 — CRITICAL (producer): not every admitted theorem emits `:DEFTHM`
`00-direct.proof-log` has **zero** `:DEFTHM` events for its 3 ground theorems
(`(equal (+ 1 2 3) 6)` etc.). Trivially-proved goals appear to be dispatched
before the instrumented waterfall runs, so nothing is logged → the theorem
vanishes from reconstruction. (F1 also makes `rev-rev` vanish.) A theorem ACL2
admitted must always leave a record.

### F3 — CRITICAL (reconstruction): only rewriter detail becomes tree nodes
`buildAllTheoremProofs` (ACL2Lean/ProofTree.lean:195) keeps a step **only** when
`s.result == .proved && !s.traceEvents.isEmpty`. Every other clause-level step
is discarded, even though each one carries `:INPUTCLAUSE` and (for `:SUBGOALS`)
`:NEWCLAUSES` — e.g. the `FERTILIZE-CLAUSE` record in `02-rev` has both the
clause it consumed and the clause it produced. So `03-linear` / `04` reconstruct
to a bare goal + `(no induction — direct proof)` with **no body at all**: the
actual `PREPROCESS → SIMPLIFY → SIMPLIFY` chain (and fertilize/generalize/
eliminate-destructors elsewhere) is thrown away. This both loses the proof and
silently skips data that is present in the log.

### F4 — (reconstruction): the top-level `"Goal"` clause is filtered out
`buildAllTheoremProofs` drops every case with `clauseId == "Goal"`. A pure
non-inductive proof lives entirely under `"Goal"`, so it reconstructs to
nothing. Combined with F3 this is why direct proofs are empty shells.

### F5 — (representation): the file is a forest, not a list of trees
The log is one ordered event stream: `:DEFUN`, termination proofs,
`:TYPE-PRESCRIPTION`, `:DEFTHM`, … Each theorem proof is justified against the
**world the prior events built** (e.g. `rev-rev` consumes `rev-app` as a
`:REWRITE` rune). Reconstruction returns a flat `List TheoremProof` that
discards ordering, the defun/measure context, and the dependency between
theorems. `07`'s `mutual-recursion` bundle (flag function + shared measure) has
no representation at all. The defs and theorems really live in "the same tree".

### F6 — (representation/reconstruction): one induction per theorem
`buildAllTheoremProofs` stores `curInduction : Option InductionStep` and
overwrites it on each `:INDUCTION` event. Nested / multiple inductions (and the
`:SCHEME` clauses ACL2 emits) cannot be represented.

### F7 — (producer): measure / termination is not logged
`06`'s `:DEFUN COUNT-DOWN` records `:FORMALS`/`:BODY`/`:ORIGIN` and a
`:TYPE-PRESCRIPTION`, but **no `:MEASURE`, no `:WELL-FOUNDED-RELATION`**, and the
termination (measure-conjecture) proof is not linked to the defun. The
reconstruction `defun` event (ACL2Lean/ProofLog.lean:101) likewise has no
measure field. Measure support requires emitting these from ACL2.

### F8 — (producer): hint provenance is dropped
`05-hints` exercises `:use`, `:induct`, `:in-theory`. A `:use` lemma becomes an
extra hypothesis clause, but the fact that it *came from* `:instance lemma X`
is not recorded; `:induct`/`:in-theory` leave no structured trace. A clause then
appears "from nowhere", which a deterministic reconstruction cannot justify.

### F9 — (output): the renderer presents empty shells as finished proofs
Because of F3/F4 the dump prints `(no induction — direct proof)` with no body
for `03`/`04`, which reads as "nothing to prove" rather than "reasoning
dropped". Once the clause tree is reconstructed the renderer must show it.

---

## The architectural fix: reconstruct the **clause tree**

The credible, deterministic proof tree is already in the log. For every clause
ACL2 processes it emits a `:STEP` with:
`:CLAUSEID`, `:PROCESSOR`, `:INPUTCLAUSE`, `:RESULT` (`:PROVED` | `:SUBGOALS`),
`:NEWCLAUSES`, `:RUNES`; and for induction a `:INDUCTION` with `:TERM`,
`:SUBGOALS`, and the full `:SCHEME` (the case clauses). The clause-ids
(`"Goal"` → `"Goal'"` → `"Subgoal *1/2"` → `"Subgoal *1.1/2''"`) encode the tree
lineage, and `:NEWCLAUSES` gives the children explicitly.

So the proof tree should be: **clause node = (clauseId, inputClause, processor,
children)**, linked parent→child by ACL2's documented clause-id lineage and
`:NEWCLAUSES`. Every processor is a node — `PREPROCESS`, `FERTILIZE`,
`GENERALIZE`, `ELIMINATE-DESTRUCTORS`, induction, … The rewriter trace events we
already model become a **sub-tree of detail hanging off a `SIMPLIFY-CLAUSE`
node** (the literal-by-literal rewriting), not the whole tree.

This is deterministic and heuristic-free: the structure is literally the
clause-id lineage + `:NEWCLAUSES` in the log. Where the log lacks data (measure,
hints, dropped theorems), the fix is to **emit more from ACL2**, never to infer
in Lean.

### Proposed representation change (F5/F6)
Replace flat `List TheoremProof` with an ordered event forest:

```
ProofWorld := List WorldEvent          -- file order preserved
WorldEvent := defun (name, formals, body, measure?, wfRel?, termProof?: ClauseTree)
            | typePrescription ...
            | mutualRecursion (List defun, sharedMeasure, flagFn)   -- F5
            | theorem (name, formula, proof: ClauseTree)            -- F1/F3
ClauseTree := node (clauseId, inputClause, processor,
                    induction?: InductionScheme,                    -- F6 (nestable)
                    rewriteDetail?: List LiteralProof,              -- existing detail
                    children: List ClauseTree)
```

---

## Improvement set (for sign-off, sequenced)

**Stage R — Reconstruction (no producer change needed; data already present):**
- **R1.** Build the full clause tree from `:CLAUSEID`/`:INPUTCLAUSE`/`:PROCESSOR`/
  `:NEWCLAUSES`, linking by clause-id lineage. (Fixes F3.)
- **R2.** Stop the two silent filters: keep `"Goal"`; do not require non-empty
  trace events. An unrecognized processor must **hard-fail**, not drop. (F3/F4.)
- **R3.** New representation: ordered `ProofWorld` event forest with `ClauseTree`
  per proof; nestable induction. (F5/F6.)
- **R4.** Hang the existing rewriter literal/trace sub-tree off `SIMPLIFY` nodes.
- **R5.** Completeness check: every `:DEFTHM` must reach a closing QED and a
  closed clause tree; otherwise hard-fail. This makes F1 *detectable* downstream
  even before the producer is fixed.

**Stage P — Producer (ACL2; favor emitting more):**
- **P1.** Emit a structured **failure/abort event** when an event fails (and stop
  suppressing ACL2's error text under `:structured`), so a truncated log is
  self-describing rather than indistinguishable from a complete one (F1, real
  finding). *Highest priority — the log is ground truth.* (Capture-script
  stopgap already in place; this is the durable producer fix.)
- **P2.** Emit a `:DEFTHM` event for every admitted theorem, incl. trivially
  proved ones (F2).
- **P3.** Emit `:MEASURE`, `:WELL-FOUNDED-RELATION`, and the termination proof
  (as a clause tree keyed to the defun) on admission; ensure every defun emits a
  `:DEFUN` event (F7).
- **P4.** Tag clauses/steps with hint provenance (`:use`/`:by`/`:induct`/
  `:in-theory`) so reconstruction can justify clauses that hints introduce (F8).

**Stage O — Output:**
- **O1.** Render the clause tree (processor-labeled nodes, subgoal lineage,
  induction scheme) and the world events in order; no more empty shells (F9).

**Determinism guardrails (apply throughout):** link clauses by ACL2's documented
clause-id scheme + `:NEWCLAUSES`, never by fuzzy term matching; unknown
processor / missing QED / theorem-without-proof ⇒ hard-fail; no inference in the
checker — when data is missing, emit it from ACL2.

---

## Replay-sufficiency review (2026-06-06, after the clause-tree rebuild)

Second review, different angle: does the reconstructed clause tree carry
*everything the eventual Lean replay needs* to push a kernel-checked proof in the
same shape? Verdict: **`my-len-my-app`'s tree is a well-formed, complete proof
skeleton** (induction → 2 case subgoals → per-literal rewrite chains, every leaf
a closed goal); all its node types (definition/recognizer/if-simplification/
with-lemma-arithmetic/equal-self, plus the induction `:SCHEME`) carry sufficient
data — **with one blocking gap**, and a set of corpus-wide producer gaps that
don't bite the target theorem but bite the rest.

### R-A — LINCHPIN (producer): the induction hypothesis is never linked to its use
The step case discharges its conclusion via a `:REWRITING-EQUIVALENCE`
(solidify) node whose `:EQUIV-TERM` is the IH — but ACL2 logs `:PARENTS NIL`, so
nothing records *that this rewrite is justified by the IH assumption*. Verified
against `acl2_samples/simple.proof-log`:
- step-case IH literal (index 2, negated): `(my-len (my-app (cdr x) y)) =
  (binary-+ (my-len (cdr x)) (my-len y))`
- solidify `:EQUIV-TERM`: `(binary-+ (my-len y) (my-len (cdr x))) =
  (my-len (my-app (cdr x) y))`

These match only up to orientation **and** `commutativity-of-+`, so a
reconstruction-side structural match would require AC reasoning = inference =
forbidden. `:PARENTS` is `NIL` on *every* step in the log (the slot exists, is
never populated). **Fix (producer):** populate `:PARENTS` on
`rewriting-equivalence`/solidify steps with the clause literal / assumption id
the solidify used. This is the single most important fix to make the target
theorem's step case replayable faithfully.

### Corpus-wide replay gaps (producer; do not block `my-len-my-app`)
- **R-B `WITH-LEMMA` rewrites carry no `:SUBST`.** Fine for builtin-arithmetic
  axioms (my-len-my-app), but a rewrite by a *prior user theorem* (e.g.
  `app-assoc` inside `rev-app`) needs the instantiating substitution to invoke
  the imported Lean lemma. Emit `:SUBST`/`:UNIFY-SUBST` on `WITH-LEMMA` steps.
- **R-C `eliminate-destructors`** loses the `car/cdr`→fresh-var elim
  substitution. Emit it.
- **R-D `generalize`** records no term→var map or restrictions. Emit them.
- **R-E `fertilize`** records neither the equality used nor its direction. Emit
  the literal id + orientation.
- **R-F `preprocess` that closes by an external rune** has no per-literal trace
  (just the rune name). Route its closing rewrite through the SIMPLIFY trace.
- **R-G `clause-context-resolution`** (literal true by a context assumption)
  carries only lhs/rhs, not which assumption (same shape as R-A).

### Could not verify
- That the replay machinery consumes these fields end-to-end — `ProofProducer`
  handles only 3 node types and throws on definition/recognizer/rewrite/
  rewriting-equivalence; its chaining bottoms out at a `sorry` (T1 in
  `EvalLemmas`). The *tree* carries the data; no consumer exercises it yet. The
  reference hand-proof (`SimpleWorld.lean`) is itself all `sorry`.
- Whether the recognizer `typeSet`/`trueTs` bit-encodings are load-bearing for
  replay or redundant with the structural `lhs⇒rhs`.
- Whether `:SCHEME` alone suffices to derive the *exact* Lean induction principle
  for multi-case schemes (e.g. the 3-subgoal inductions in `02-rev`), with no
  `:MEASURE` emitted.
- Forcing-round / `Dk` linking (no sample exercises them).
