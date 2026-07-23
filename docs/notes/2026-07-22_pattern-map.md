# The pattern map — anchored circles over the replay's mechanism space

Created 2026-07-22 (mapping arc increment 1; the arc spec is the TODO.md
top block, MDD-ratified 2026-07-21). This document is the arc's SPINE:
one entry per replay mechanism ("pattern"), each recording

- **source**: the generating ACL2 code site — the ground truth whose
  branch structure defines the circle's axes (never imagination);
- **axes**: what that code actually branches on — each axis point is a
  candidate synthetic book;
- **anchor**: the wild corpus row(s) that prove the pattern is real;
- **books**: the authored pattern-corpus books covering the axes
  (`acl2_samples/pattern-tests/`, each through real ACL2 + capture, each
  with a native lift where feasible — the anti-mangling guard);
- **status**: `recipe-landed` / `emission-pending` / `design-parked`,
  and per-axis coverage.

Method (the amended CLAUDE.md rule): synthetic BOOKS yes, synthetic
ARTIFACTS never. An axis point ACL2 refuses to reach from a small book
is recorded as `unreachable-by-construction`, not silently skipped.
Books whose natural native statement is Logic-bound (ACL2-quirk
circles) are FLAGGED as such — lack of a lift must be visible.

Seeded from the emission arc's conquered mechanisms (each source site
was read during implementation; see
`docs/notes/2026-07-21_emission-arc.md` for the increment evidence).
No pattern books exist yet — authoring them is the arc's work.

## Rewriter-core patterns

### P1 — rewrite-if SWAPPED-P normalization
- source: `acl2/rewrite.lisp:17726-37` (negation-shaped rewritten test
  `(IF c 'NIL 'T)` → strip + swap branches, unrecorded).
- axes: firing position (frame descends into the if / node ON the if /
  at the if-finish JOINT); nested double-negation (swap fires twice);
  interaction with the or-optimization directly below it in the source
  (`(if x x y)` with `unrewritten-test == left` → `*t*` under iff);
  swap inside hyp-relief vs body vs rhs blocks.
- anchor: LEN-ZIP2/3 (descend+target), ORDEREDP-MEMB (joint).
- books: none yet. status: recipe-landed
  (`bridgeIfNegTestSwap`/`normalizeSwapsToward`); or-optimization axis
  UNEXERCISED — no corpus row, no book.

### P2 — the RUNOUT pass (rewritten-body)
- source: `acl2/rewrite.lisp` ~20613 (`rewrite-fncall` re-rewrites the
  rewritten body, gstack `'rewritten-body`); fork: the bkptr
  inner-block kind list.
- axes: recursive vs non-recursive fn; runout children carrying their
  own root collapses (the pass-local strip case); nested unfolds inside
  the runout; runout under a rule RHS block.
- anchor: REV-REV, HOW-MANY-ISORT, ORDEREDP-RM;
  HOW-MANY-EVENS-AND-ODDS (pass-local strip).
- books: none yet. status: recipe-landed.

### P3 — chain-root strip / pass locality
- source: ACL2's gstack branch-frame residue per rewrite pass
  (`rewrite-if` keeping the if on the gstack while rewriting a branch).
- axes: block kind (BODY/RHS/HYP/REWRITTEN-BODY); two same-kind blocks
  under one parent (audit-refuted as unobserved — an axis point to
  probe deliberately); collapse selecting then vs else; folded vs
  unfolded recorded lhs.
- anchor: HOW-MANY-EVENS-AND-ODDS.
- books: none yet. status: recipe-landed (kind-tagged); the same-kind
  collision axis is exactly what a book should try to construct.

### P4 — EQUAL-commuted stored-rule match
- source: `acl2/translate.lisp:6916-31` (`one-way-unify1` EQUAL
  special case).
- axes: direct vs commuted; ambiguity (both orientations matching
  DIFFERENT stored rules — must stay hard-fail); commuted match with
  hyps; non-EQUAL equivalences (must NOT commute).
- anchor: CAR-APPEND.
- books: none yet. status: recipe-landed.

### P5 — rewrite-equal built-in normalizations
- source: `acl2/rewrite.lisp:18089-98` (NIL forms, EQUALITYP form);
  if-interp call-stack folds `:3742-3849`.
- axes: each normalization form; chain-end vs mid-chain occurrence.
- anchor: qsort-arc rows (ALL-REL family).
- books: none yet. status: recipe-landed (`bridgeEqualNilNorm` et al).

## Clause/waterfall patterns

### P6 — induction clean-up (trivial-clause drops)
- source: `acl2/induct.lisp:7047` → `trivial-clause-p`
  (simplify.lisp:6808) → `tautologyp`/`if-tautologyp`
  (rewrite.lisp:5852-5960) + SINGLE-PASS `expand-some-non-rec-fns`;
  fork `:SCHEME-DROPPED` (a291c2ec22).
- axes: each expansion fn (implies/iff/eq/eql/=/zerop/…— note the
  audit's single-pass subtlety: introduced EQL stays opaque);
  EQUAL/IFF commutation depth; complement folds (add-literal, never
  emitted) vs trivial drops (emitted in :SCHEME-DROPPED); base-case vs
  IH-selection drops.
- anchor: ORDEREDP-MEMB.
- books: none yet. status: recipe-landed + emission-landed.

### P7 — multi-record ELIM rounds
- source: `eliminate-destructors-clause` (the per-record erase/prepend/σ
  reorder rule, validated vs :NEWCLAUSES).
- axes: record count; fresh vs occurring elim vars; guard-literal
  position; per-level pinning.
- anchor: msort rows.
- books: none yet. status: recipe-landed.

### P8 — strip-branches conjunction split
- source: `acl2/rewrite.lisp:4318` (`(IF p q 'NIL)` unions the two
  sides' clause sets — NO if-interp test event).
- axes: and-shape at literal root; nested and-shapes; and-shape whose
  p side itself splits.
- anchor: ORDEREDP-ISORT (Subgoal *1.1/3').
- books: none yet. status: EMISSION-PENDING (fork queue: emit a
  conjunction-split event), then a spine-walker arm.

### P9 — FC-derived type-alist facts
- source: forward-chaining rules feeding the type-alist
  (`:TA-RUNES` provenance, fork); `type-alist-clause` contradictions.
- axes: relief via a single FC rule (LEXORDER-TOTAL, landed); the
  commuted-source demand; FC CONTRADICTION closing a whole clause
  (HOW-MANY-FILTER-1 *1/3.3 — EMISSION-PENDING: no discharge node);
  DEFAULT-CDR-style primitive type-set entries whose source is a
  segment fact (EMISSION/threading-pending).
- anchor: qsort ALL-REL rows; HOW-MANY-FILTER-1;
  HOW-MANY-EVENS-AND-ODDS.
- books: none yet. status: partially landed; two emission-pending axes.

### P10 — verdict-class recognizers and TP pins
- source: type-set recognizer resolution (`rewrite-recognizer`,
  assume-true-false); compound-recognizer rules; gz TP corollaries.
- axes: recognizer × fact-source matrix (litFact / segFact /
  branchFact / TP hypothesis / builtin TP via emitted gz corollary /
  compound-recognizer rule); the registered kernel derivations
  (ATOM-from-CONSP-false, ZP-from-INTEGERP-false, unicity int pins).
- anchor: LEN-INTERLEAVE class, LEN-ZIP2, CD2-BOUND.
- books: none yet. status: recipe-landed for the exercised cells; the
  matrix's unexercised cells are the book targets.

## Interpreter-layer twin (differential families)

Each trusted-core primitive pinned WITH a differential family
(`Tests/differential/`), H3 made systematic. Queue seeded by the
corpus: NUMERATOR/DENOMINATOR (H3 pin-first, design-parked), the
lexorder total-order surface (partially pinned), `zp`/`nfix` numeric
coercions (newly load-bearing via P10/the NFIX measure single).

## Design-parked circles (MDD review before any build)

L2 equivalence ladder (IFF→PERM congruences), encapsulate/functional
instantiation, admission-waterfall replay, `:use`-hint Goal structure,
NFIX μ-measure + decrease-prover arm, trivial-equiv branch
substitution (the type-alist substitution class).
