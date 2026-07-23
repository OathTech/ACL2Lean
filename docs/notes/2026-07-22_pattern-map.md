# The pattern map — anchored circles over the ACL2 situation space

Created 2026-07-22 (mapping arc increment 1; the arc spec is the TODO.md
top block, MDD-ratified 2026-07-21). **Scope correction (MDD,
2026-07-22): the arc maps COVERAGE of ACL2's situation/proof space —
how to SUPPORT a construct is a secondary, downstream question, and
the map must never limit itself to what the replay can handle today.**
A book that fails at a named frontier, or does not even reconstruct,
is a SUCCESSFUL mapping outcome: it pins where the frontier is with a
real captured artifact. The replay scoreboard is recorded per book but
is NOT the arc's metric; situation-space coverage is.

## The coverage frame (top-down, from ACL2's own inventory)

Enumerated from ACL2's documented structure — NOT from what we have
built (the P1–P11 entries below were seeded bottom-up from conquered
mechanisms and are the survivor-biased half of the picture). Status
per item: `corpus` (wild anchor exists), `books` (pattern books
authored), `frontier-pinned` (book captured, observed failure
recorded), `UNCOVERED` (no artifact at all — the priority).

**Event forms:** defun `corpus`; mutual-recursion `corpus`
(recon-07); defthm `corpus`; include-book `corpus` (isort);
encapsulate/constrained-fns `UNCOVERED` (design-parked, no artifact);
defun-sk (quantifiers) `UNCOVERED`; defchoose `UNCOVERED`; defconst
`UNCOVERED`; local `UNCOVERED`; defequiv/defcong `UNCOVERED` (L2
anchors are wild rows only); defattach `UNCOVERED` (likely
out-of-tier); verify-guards/guard-obligations `UNCOVERED`.

**Rule classes:** :rewrite `corpus+books`; :definition `corpus`;
:type-prescription `corpus`; :elim `corpus`; :forward-chaining
`corpus`; :compound-recognizer `corpus` (CD2-BOUND);
:induction `corpus` (12-multi-controller); :linear `UNCOVERED` (cited
in runes, never as the authored subject); :congruence `UNCOVERED`;
:equivalence `UNCOVERED`; :refinement `UNCOVERED`; :meta `UNCOVERED`;
:clause-processor `UNCOVERED`; :built-in-clause `UNCOVERED`;
:tau-system `corpus` (discharge leaves only); :generalize-rule
`UNCOVERED`; :well-founded-relation `UNCOVERED`.

**Waterfall processors:** preprocess `corpus`; simplify `corpus`;
settled-down `corpus`; fertilize `corpus`; generalize `corpus`
(msort); eliminate-destructors `corpus`; eliminate-irrelevance
`corpus` (thin — one wild row class); push/induct `corpus`.

**Rewriter situations:** geneqv equal `corpus+books`; geneqv iff
`frontier-pinned` (p1-or-opt-probe); user geneqv `UNCOVERED`;
free-var hyp relief `corpus`; FORCING / case-split
`UNCOVERED` (forcing rounds — a whole proof structure we have never
captured); backchain limits `UNCOVERED`; syntaxp/bind-free `corpus`
(SYNP relief); rewrite-cache effects `UNCOVERED`; linear-pot
integration `UNCOVERED` (beyond discharge leaves).

**Hints:** :use `corpus` (LEN2-APP-VIA-USE, recon-05, frontier);
:induct `corpus` (recon-05?); :expand `UNCOVERED`; :cases
`UNCOVERED`; :by `UNCOVERED`; :in-theory `corpus` (implicit);
computed hints `UNCOVERED`.

**Value/interpreter surface:** integers `corpus`; rationals
`frontier-pinned` (NUMERATOR rows, design-parked); complex numbers
`UNCOVERED`; characters/strings `corpus` (STRINGP lift); symbols/
packages `corpus` (BUG-002 family); guard-vs-logic-mode distinctions
`UNCOVERED`.

Priority for book authoring: the `UNCOVERED` items above, breadth
first — one minimal book each, captured through real ACL2, observed
behavior catalogued here (capture / parse / reconstruct / replay
frontier), REGARDLESS of support status. **This branch does NOT wire
books into the replay sweep, add pipeline code, or build support of
any kind — coverage only.** Sweep wiring, emission fixes, recipes,
and native lifts are all support-side follow-ups sequenced AFTER the
map is good.

## Frontier tier (captured; observed behavior catalogued)

(populated as breadth books land — each entry: book, observed
behavior at capture/parse/reconstruction, and what it pins)

This document is the arc's SPINE:
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

**Generalize-before-baking (MDD, 2026-07-22).** A quirk a probe
surfaces is treated as a SIGN of a more general rule until shown
otherwise: locate the family's generating structure in the ACL2
source and probe THAT — the map's unit is the family, not the
instance.

**There is no "silent normalization" (MDD, 2026-07-22).** The emission
format is entirely OUR design; a rewrite the log does not show is an
UN-INSTRUMENTED EMISSION SITE — the project's top-level rule applied
again (find where reconstruction lacks information → instrument the
fork there, in FUTURE support work). The map's job is only to
enumerate and pin those sites with books.

### P0 — un-instrumented emission sites (future fork instrumentation)
- the sites where our current instrumentation does not record what the
  rewriter did, enumerable by reading the rewriter source:
  rewrite-equal's NIL/EQUALITYP forms (rewrite.lisp:18089-98),
  rewrite-if's swapped-p (17726-37) and the or/and *T*/left-copy
  identities beside it, the if-interp call-stack folds (3742-3849),
  strip-branches' and-shape union (4318), sublis-var display folds,
  rewrite-time FC contradictions, primitive type-set entries'
  provenance.
- coverage task (THIS arc): source-sweep the rewriter for the full
  site list; give each a book pinning its observed log shape.
- support task (FUTURE, not this branch): instrument each site;
  today's replay-side reconstructions of some of them then become
  redundant and can be retired.

### P11 — the geneqv landscape
- source: ACL2's geneqv computation (`geneqv-lst`, congruence-rule
  application) — which argument positions rewrite under which
  equivalence.
- coverage task: books that put the same redex under equal-geneqv vs
  iff-geneqv vs user-geneqv positions and catalogue the recorded
  chains. The observed shapes are the requirements data for the
  (future, design-parked) L2 support work.

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
- books (first circle, 2026-07-22 — `acl2_samples/pattern-tests/`):
  - `p1-swap-descend` (or-guard base case) — REPLAYS ✓;
  - `p1-swap-joint` ((NOT (EQUAL …)) body test) — REPLAYS ✓;
  - `p1-swap-double-neg` (iterated swap ×2) — REPLAYS ✓. Probe finding:
    a (NOT (NOT …)) DEFUN body is normalized at admission
    (unreachable-by-construction); the THEOREM-hypothesis route reaches
    it.
  - `p1-or-opt-probe` — axis PINNED by a real captured shape: ACL2
    replaces the or-test's then-copy by *T* under IFF geneqv
    (`(iff (if x x y) (if x t y))`, the identity directly below the
    swap site). Row FAIL (named if-finish mismatch) — this is the L2
    frontier in miniature; note: at a TEST position the identity IS
    eval-sound (`(IF (IF x x y) a b) ≡eval (IF (IF x 'T y) a b)`), so a
    positional bridge is designable short of full L2. Design note for
    the L2 ladder.
- status: 4/4 axes have captured books (observed via focused replay:
  3 replay under existing support, 1 pins the iff-identity shape).
  Native lifts and any sweep wiring: support-side, future.

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
