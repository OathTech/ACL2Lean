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
encapsulate/constrained-fns `books` (cov-encapsulate — reconstructs);
defun-sk (quantifiers) `frontier-pinned` (cov-defun-sk — recon fails, -suff shape); defchoose `books` (cov-defchoose); defconst `books-partial` +
local `frontier-pinned` (cov-defconst-local — the top-level LOCAL
defthm logs with :SOURCE :LOCAL, then the session HALTS before the
next event; capture-layer pin);  defequiv/defcong `books` (cov-congruence — obligations reconstruct; consumption-side book queued); defattach `UNCOVERED` (likely
out-of-tier); verify-guards `frontier-pinned` (cov-verify-guards — the defun/TP
events emit but the GUARD OBLIGATION PROOF is entirely absent from
the log; an emission-coverage gap pinned).

**Rule classes:** :rewrite `corpus+books`; :definition `corpus`;
:type-prescription `corpus`; :elim `corpus`; :forward-chaining
`corpus`; :compound-recognizer `corpus` (CD2-BOUND);
:induction `corpus` (12-multi-controller); :linear `books` (cov-linear); :congruence `books`;
:equivalence `books`; :refinement `books` (cov-refinement); :meta `frontier-pinned`
(cov-meta-rule — parse fails on LAMBDA path frames); :clause-processor
`frontier-pinned` (cov-clause-processor — same LAMBDA-frame parse
frontier); :built-in-clause `books` (cov-built-in-clause);
:tau-system `corpus` (discharge leaves only); :generalize-rule `books` (cov-generalize-rule); :well-founded-relation
`books` (cov-wf-relation — the defun event emits :WFREL MY-LT with
termination clauses in the custom relation).

**Waterfall processors:** preprocess `corpus`; simplify `corpus`;
settled-down `corpus`; fertilize `corpus`; generalize `corpus`
(msort); eliminate-destructors `corpus`; eliminate-irrelevance
`corpus` (thin — one wild row class); push/induct `corpus`; apply-top-hints-clause `books` (cov-by-hint —
a processor MISSING from this frame until the book surfaced it; :by
discharges through it as a PROVED step with no rewrites).

**Rewriter situations:** geneqv equal `corpus+books`; geneqv iff
`frontier-pinned` (p1-or-opt-probe); user geneqv `books` (cov-cong-consume — a with-lemma step recorded
with :EQUIV SAME-LEN2, the L2 lane's core artifact);
free-var hyp relief `corpus`; FORCING / case-split `books-partial` (cov-force — forced-hyp rule covered; the forcing ROUND itself did not fire, stronger probe queued); backchain limits `UNCOVERED`; syntaxp/bind-free `corpus`
(SYNP relief); rewrite-cache effects `UNCOVERED`; linear-pot
integration `UNCOVERED` (beyond discharge leaves).

**Hints:** :use `corpus` (LEN2-APP-VIA-USE, recon-05, frontier);
:induct `corpus` (recon-05?); :expand `books` (cov-expand-hint); :cases `books` (cov-cases-hint); :by `books` (cov-by-hint); :in-theory `corpus` (implicit);
computed hints `books` (cov-computed-hint).

**Value/interpreter surface:** integers `corpus`; rationals
`frontier-pinned` (NUMERATOR rows, design-parked); complex numbers `frontier-pinned` (cov-complex — CAPTURE-layer halt); characters/strings `corpus` (STRINGP lift); symbols/
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

Breadth batch 1 (2026-07-22, `cov-*.lisp` — 9 books authored, all
through real ACL2):

- `cov-complex` — **CAPTURE-layer halt**: ACL2/instrumentation stops
  at the first event (log = banner + `(:BEGIN-PROOF-LOG)` only; the
  capture integrity net flagged INCOMPLETE). The complex-number value
  surface's frontier starts at the fork's emitters, before parse or
  replay. Pins: instrumentation cannot yet log a book containing `#c`
  literals.
- `cov-defun-sk` — captures (1 QED) but **RECONSTRUCTION fails**:
  `theorem 'EXISTS-DOUBLE-SUFF' has no closing (:QED) before included
  theorem 'EXISTS-DOUBLE-SUFF'` — defun-sk's generated `-suff` rule is
  admitted without the standard proof-log shape. Pins the defun-sk
  event structure.
- `cov-encapsulate` — RECONSTRUCTS (constrained-fn events survive
  stages 3–4 structurally); replay support entirely unprobed (and out
  of scope here).
- `cov-congruence` — RECONSTRUCTS, including the defequiv-generated
  equivalence obligation and the defcong congruence theorem as
  ordinary defthms. The rule-class CONSUMPTION side (rewriting under
  the user equivalence) is not exercised by this book — follow-up
  book needed where a later theorem rewrites UNDER `same-len`.
- `cov-defchoose`, `cov-linear`, `cov-cases-hint`, `cov-expand-hint`
  — all RECONSTRUCT; observed tree shapes catalogued by capture.
- `cov-force` — reconstructs, but NO forcing round fired (the forced
  hyp relieved immediately by type-set in both theorems). The
  forcing-ROUND proof structure is still unpinned — stronger probe
  queued (a forced hyp not relievable at use time, e.g. via a
  constrained function).

Breadth batch 2 (2026-07-22, 11 more books):

- `cov-meta-rule`, `cov-clause-processor` — **PARSE frontier**: both
  defevaluator-based books (16 generated internal theorems each, all
  captured, 7k-line logs) fail parse on `:PATH frame fn not a symbol
  (lambda/quote unsupported)` — the generated evaluator proofs rewrite
  inside LAMBDA applications and the path frames carry the LAMBDA
  term. Pins the lambda-path event shape (parse-layer sibling of the
  known dpValExpr LAMBDA frontier).
- `cov-cong-consume` — the L2 core artifact: a with-lemma step
  recorded `:EQUIV SAME-LEN2` (a rewrite under a USER equivalence
  inside a defcong-blessed argument position), plus the `(:RULES …)`
  storage of a SAME-LEN2-equiv rule. **Behavioral pin from the first
  version**: a HYP-FREE user-equivalence rule loops ACL2's
  PREPROCESSOR (call-depth hard error) — preprocess classes it
  "simple"/abbreviation and IGNORES loop-stoppers; the syntaxp guard
  routes it through the full rewriter.
- `cov-defconst-local` — **CAPTURE-layer pin**: the top-level LOCAL
  defthm runs and logs (`:SOURCE :LOCAL`), then the ACL2 session
  halts before the next event (k-fixed never starts). defconst itself
  substitutes fine at translate (the formula shows `(+ 42 0)`).
- `cov-verify-guards` — the defun/TP events emit but the GUARD
  OBLIGATION PROOF is entirely absent from the log — verify-guards
  runs a real proof our instrumentation does not see. Emission-
  coverage pin.
- `cov-by-hint` — `:by` discharges through APPLY-TOP-HINTS-CLAUSE
  (`:RESULT :PROVED`, no rewrites) — a waterfall processor missing
  from this frame until the book surfaced it.
- `cov-wf-relation` — custom well-founded relation flows through
  admission emission: `:WFREL MY-LT`, termination clauses stated in
  MY-LT. Reconstructs.
- `cov-refinement`, `cov-built-in-clause`, `cov-generalize-rule`,
  `cov-computed-hint` — all reconstruct; shapes catalogued.

## Driver inventory — candidate fake-replay infrastructure (pin now, kill later)

MDD directive (2026-07-22): mechanisms in the CURRENT driver that
RE-DERIVE what ACL2 could emit are candidate fake-replay
infrastructure. This branch pins each with coverage; the kill-path
(principled emission + recorded-step replay) is future support work.
Graded: [bridge] = reconstructs an unlogged rewrite at a mismatch
point; [rederive] = recomputes a resolution ACL2 made from data we do
not consume; [mirror] = deterministic recompute of a documented ACL2
function validated against emitted output (most defensible, still
listed).

1. [bridge] `bridgeEqualNilNorm` — rewrite-equal NIL/EQUALITYP forms.
2. [bridge] `bridgeIfNegTestSwap` / `normalizeSwapsToward` /
   `liftNegTestSwap` — rewrite-if swapped-p. (Books: p1-swap-*.)
3. [bridge] display-folded constant-test collapse arms
   (`mkConstTestCollapse` on folded records) — sublis-var folds.
4. [rederive] `collapseEval` symbolic-test resolution — "re-derives
   the resolution from the SAME facts if-interp consulted".
5. [rederive] the test-resolution reconciliation arm (unemitted
   type-alist lookups, if-interp-assumed-value2).
6. [rederive] recognizer registry derivations (ATOM-from-CONSP-false,
   ZP-from-INTEGERP-false, two-valued registries) — NOTE: the log
   already carries `:TYPESET`/`:TRUETS` integers on recognizer steps
   that we DO NOT consume; principled replay would decode the emitted
   type-set instead of re-deriving membership.
7. [rederive] `collectContextDemands` demand hoisting — re-derives
   what ACL2's type-alist had in scope (incl. the commuted-lexorder
   special case).
8. [rederive] FC-relief registry (LEXORDER-TOTAL) — consumes the
   emitted snapshot but re-derives the relief chain.
9. [mirror] chain-root strip / pass-local tagging — re-derives gstack
   frame residue from bkptr paths (structure not emitted).
10. [mirror] elim reorder recompute (erase+prepend+σ) — validated vs
    emitted :NEWCLAUSES.
11. [mirror] induction clean-up recompute (trivial-clause-p/ifTaut) —
    now validated vs emitted :SCHEME-DROPPED; the (i)-class
    add-literal complement folds are still recompute-only.
12. [mirror] pool-subsumption witness recompute (`subsumeWitness`),
    `dumbNegateLit`/`substTerm` mirrors, clausify mirror
    (`expandTerm`/`clausifyChecked`).
13. [rederive] `clause-context-resolution` verify-then-drop markers.

Each [bridge]/[rederive] entry needs: (a) a book pinning the
underlying ACL2 mechanism (quirk-derived backlog below), (b) a named
future emission that would retire it. The [mirror] class is retained
by design where the emitted artifact fully validates the recompute —
graded acceptable, but listed so the boundary stays visible.

## Quirk-derived book backlog

From the emission arc's bespoke mechanisms (each pins one inventory
entry): equal-NIL normalization shapes; EQUAL-commuted rule match
(one-way-unify1); display-folded collapses; a MINIMAL trivial-clause
drop (ORDEREDP-MEMB's is embedded in a big book); free-var relief via
type-alist (:TA-RUNES); strip-branches and-shape union; elim
multi-record rounds; clause-context-resolution marker; runout
minimal book; :TYPESET-decode probes (books whose recognizer verdicts
exercise distinct type-set bits). Plus follow-ups from batch 1:
forcing-round-for-real, congruence-consumption, defun-sk variants
(forall; nested), complex-number minimal repro for the fork.

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
