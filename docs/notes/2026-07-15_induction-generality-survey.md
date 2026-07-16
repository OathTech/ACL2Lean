# Induction generality — Stage 0 ground-truth survey (2026-07-15)

Grounding for the induction-generality design arc (the highest-leverage
frontier item from `2026-07-15_external-knowledge-execution-outcomes.md`).
Everything below is read off the REAL reconstructed trees
(`lake exe acl2lean dump-proof-tree`) and the real failure messages — not the
mental model. Stage 1 (design doc) builds on this; nothing here is a design
decision.

## What `replayInduction` consumes today (its frontier guards, Driver.lean)

The current scaffold hard-fails unless ALL of:
- measure is literally `(ACL2-COUNT v)` for a single symbol `v`;
- well-founded relation is `O<`;
- controllers list is exactly `[v]`;
- the step case's ruling tests contain `(CONSP v)` or `(NOT (ENDP v))`
  (hardwired cdr-decrease justification);
- one IH per step case, substitution shape checked against cdr-decrease.

The EMITTED induction block is much richer than this consumption: every
failing tree already carries the measure TERM, the wf relation, the measured
subset ("on: …"), per-case ruling-test lists, per-case IH substitution
alists (possibly several per case), and the scheme clauses.

## Replay-level axes (each anchored to a failing row's real tree)

### A1 — multiple IHs per case (10-tree-induction / TRUE-LISTP-FLATTEN)
```
INDUCTION on (FLATTEN X); measure (ACL2-COUNT X); on: X
  case [(CONSP X)]:  IH: X := (CAR X)   IH: X := (CDR X)
```
Current wall: `IH maps controller X to (CAR X), expected (cdr X)`.
Structural observation: a WF induction over the measure yields ONE IH
quantified over all measure-smaller instances; instantiating it at both
`(CAR X)` and `(CDR X)` (each justified by `acl2Count_car/cdr_lt_of_consp`,
both already in Count.lean) is scaffold work, not new mathematics.

### A2 — compound ruling tests (12/LEN-ZIP2, 16/LEN-ZIP3)
```
case [(NOT (IF (ATOM X) (ATOM X) (ATOM Y)))]:  IH: X := (CDR X), Y := (CDR Y)
```
Current wall: tests "lack (consp X) / (not (endp X))". The step-entry fact is
an emitted TEST TERM (here: X and Y both non-atoms), from which the measured
variable's consp-ness must be DERIVED (value-level, from the branch fact),
not pattern-matched. ZIP3 is the same shape one deeper.

### A3 — substitutions of UNMEASURED variables (12, 16, also 10's `Y := Y`)
`Y := (CDR Y)` rides along in ZIP2's IH; only X is measured ("on: X"). The
generic IH is quantified over the unmeasured variables (or over env), so
unmeasured substitution entries need instantiation, not justification.

### A4 — measure TERMS beyond (acl2-count v) (13/LEN-INTERLEAVE)
```
measure (BINARY-+ (ACL2-COUNT X) (ACL2-COUNT Y)); on: Y, X
  case [(NOT (ATOM X))]:  IH: X := Y, Y := (CDR X)     -- variable SWAP
```
Needs: (i) a measure-term VALUE layer (a Nat-valued interpretation of the
emitted measure term over the pinned variable values — sums of acl2Counts
first; CD2's custom measure `(NFIX N)`-style later), and (ii) per-case
decrease proofs of that value under the IH substitution from the case's
branch facts (here: acl2Count(Y)+acl2Count(cdr X) < acl2Count(X)+acl2Count(Y)
given (NOT (ATOM X))). Count.lean already carries sum lemmas
(`acl2Count_cdr_sum_lt_left/right[_consp]`) and even `evens/odds` lemmas
(anticipating msort). NOTE the carve-out framing question for Stage 1:
induction-measure decrease is the same verdict-class obligation as admission
decrease (already MDD-ratified for the totality prover) — the design should
say explicitly whether the same ratification covers the scheme's decrease
side conditions or a new one is needed.

### A5 — nested inductions (15/NESTED-INDUCTION)
Outer induction's scheme clauses embed the INNER theorem's formula as an
if-hypothesis; current wall: `2 scheme clauses for 1 recomputed
(non-tautological) case clauses (mismatch)` — the scheme-clause ↔ recomputed
case-clause matching (tautology filtering) breaks on the embedded
implication shape. This is a matching/normalization axis, not a measure axis.

## Reconstruction-level walls (UPSTREAM of replayInduction — scaffold work
## does NOT unlock these)

- **msort, ordered-perms**: `ClauseTree: no PUSH-CLAUSE with :POOLNAME [1]
  for the induction the pool considered there` — pool/push linkage frontier
  in buildDevelopment (an induction whose pool-root lineage the
  push→induct adjacency synthesis doesn't cover).
- **bsort**: `rewriting-equivalence node (EQUAL (CAR (CDR X)) (CAR X))
  matches no clause/segment hypothesis and its :PATH has no if-branch frame —
  unknown equivalence source` — an IH/solidify linking frontier.
- **qsort**: `Parse error: RULES: bad rune: (:REWRITE FLOOR-POSITIVE . 1)` —
  the dotted-rune parse frontier (also blocks sorts-equivalent, the D7
  consumer).

Row coverage if ONLY the replay axes A1–A5 land: TRUE-LISTP-FLATTEN,
LEN-ZIP2, LEN-INTERLEAVE, LEN-ZIP3, NESTED-INDUCTION (5 rows). The sorting
books additionally need the two reconstruction frontiers + the parser fix.

## Inputs Stage 1 must consult

- ACL2's `induct.lisp` (the induction machine: how cases/tests/substitutions
  are derived from the scheme function's induction machine) — to confirm the
  emitted data is complete for the generic scaffold, and what (if anything)
  needs MORE emission (e.g. per-case measure-decrease verdicts).
- The current WF scaffold in Driver.lean (`replayInduction`) and the #37
  totality prover's decrease machinery (per-call-site covering clauses) —
  candidate for sharing the measure-decrease layer.
- Count.lean's existing surface (sum lemmas, evens/odds — partial msort
  anticipation).
- Binding invariants L1–L3 (fragment-local consolidation; no monolithic
  inductive; world-parametric).
