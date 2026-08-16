# THE MASTER PLAN — demo close-out (drafted 2026-08-12, for Mike)

End state: **Track FREE is genuinely nearly free** (a new ACL2 book's
metric layer costs ~zero human work) and **Track REAL is maximally
machine-assisted** (a user's mirror costs the definitions + the
correspondence declarations, and little else). The mirror spec
(`ACL2Lean/Mirrors/Sorting.lean`, 13 Props) is the definition of done
for sorting; the demo is the finished product presented honestly.

## The architecture question first: how mirrors meet the replay

The replay delivers theorems at ONE order (`lexorder`) over ONE
universe (`SExpr`). The mirror Props are polymorphic over
`TotalOrder α`. Two honest routes, staged:

1. **Instance mirrors (the near-term product).** Types that embed
   order-compatibly into the ACL2 value universe — `Int`, `Nat`,
   `String`, `Char` (atom fragments where `lexorder` restricts to the
   native order; the restriction facts are CORE-LOGIC theorems,
   source 2). The user's theorem: the Prop instantiated at those
   types. Machinery: an embedding class
   (`Acl2Embed α`: injection into a fragment + order compatibility)
   + generic transport. This is what the pathfinder proves out.
2. **Order-generic mirrors (the capstone).** ACL2's own polymorphism
   is ENCAPSULATE: a book variant proving the sorting theorems over a
   CONSTRAINED order (only the total-order axioms) replays to an
   order-generic statement, which transports to `∀ TotalOrder α`
   with NO embedding needed. The parametric machinery
   (`parametric_replayed%`, `instantiate_parametric%`, the R6
   doctrine) already exists for exactly this shape (equisort). This
   is a RULED, synthetic-book-through-real-ACL2 route (the pattern
   corpus amendment covers it). Deliberately later: it needs the
   encapsulate replay lane at full strength.

## PHASE A — the pathfinder (prove the route, minimal scope)

RE-SCOPED (Mike, 2026-08-12 — the narrow-slice method): the pathfinder
runs on `Mirrors/Basics.lean` (len/app/rev/revAcc — the project's
original examples), NOT sorting. The basics slice has NO order
dimension, so the transfer kit's core (refinement relation, relator,
operation squares, skeleton-induction transport) is built on pure
structure; sorting then widens the aperture by exactly one dimension
(TotalOrder + the lexorder embedding).

- A0. `Mirrors/Basics.lean` (DONE): our own len/app/rev/revAcc, six
  book properties as Props. Waypoint rows: APP-ASSOC green CLEAN,
  MY-LEN-MY-APP + LEN-REV-ACC green (TP debt), the rev family
  pending (named frontiers).
- A1. **`app_assoc` end-to-end FIRST** — its waypoint is already
  unconditional and trio-clean, so the first mirror theorem lands
  with zero inherited debt: the refinement relation (element-opaque
  List relator + enc), the app square, theorem transport. THE
  route-proof.
- A2. `len_app` — adds the Nat-result reading (count/len transport)
  and the honest debt inheritance (drv_tp_mylen, surfaced).
- A3. `len_revAcc` — the ACCUMULATOR (def-acc, the original
  example): the template gate's decisive case at mirror level;
  industrialize what A1-A3 hand-built (the kit's first generated
  squares) to north-star quality BEFORE sorting.
- A4 (formerly the whole phase): sorting's `isort_ordered` +
  `isort_perm` at `Int` — now the aperture-widening slice:
  - `Acl2Embed Int` (intRep exists waypoint-side) + the core-logic
  restriction lemma (`lexorder` on int atoms ≡ `Int.≤` — belongs
  next to LexorderOrder.lean).
  - The mirror-iso: `isort`/`insertOrd` (mirror) ↔
  `isortL`/`insertL` (waypoint) along the embedding — HAND-WRITTEN
  this once, template-shaped deliberately (it becomes the
  generator's T1 spec in Phase C).
  - Predicate transport: mirror `Ordered` ↔ waypoint chain
  (`orderedpRec`), mirror `Permuted`/`howMany` ↔ waypoint
  `howManyL`/perm layer — same iso discipline.
  - The theorems: derived from the ISORT waypoint theorems
  (replayed-backed) through A1–A3. Product discipline: content from
  replay only; glue only; no library lemmas (none exist for our
  predicates — by construction).
- EXIT: two mirror theorems, `#print axioms` = trio (+ any inherited
  waypoint debt, honestly surfaced — ISORT's row is
  `.nativeSorried` on `dis_insert_tp`, so the mirror inherits
  `sorryAx` until the TP route lands; state it, don't hide it).
  **UPDATE 2026-08-16: `dis_insert_tp` was RETIRED 2026-08-13** (the
  TP-replay arc, CONS return-path increment) — ISORT's row is not
  `.nativeSorried` and nothing inherits `sorryAx`; the whole
  FORBIDDEN-DEBT class has been empty since 2026-08-15.
- Every hand-written thing on this path gets logged as a Phase B/C
  work item at the moment it is written (the pathfinder's second
  deliverable is THE LIST).

## PHASE B — Track FREE to nearly-free (the metric layer)

Ordered by what the pathfinder + mirrors actually consume.
**STATUS (added 2026-08-16 by the post-audit repair batch, A3-T2-3):
B1–B4 all LANDED, via the T1+2 sprint** (`docs/plans/2026-08-14_t12-sprint-charter.md`).
- B1. **The TP-replay route** — **DONE** (the TP-replay arc 2026-08-12/13
  + T1+2 sprint P1 `b71e1be` and P5b `01faf39`). `tp:` row conditions
  are **0/0**; `dis_insert_tp` and every other TP-class debt sorry are
  retired. (The "195 kept conditions" figure was the
  DISCHARGE-bracket surface, not the row surface — see the LEXICON's
  ROW vs DISCHARGE-BRACKET entry.) The single biggest lever, and it
  was.
- B2. **with_termination coverage** (REQUIRED class, 5) + the usefi
  totality lift → the three `*-IS-ISORT` capstone rows re-green —
  **DONE** (R3 `b3f6174` for the measure table, P3b `9e5977e` for the
  ordinal route). The REQUIRED class is empty.
- B3. **The R-lane** (PERM-TLFIX, G1) → CONVERT-PERM chain +
  `dis_convert_perm` retires → `perm_iff_howMany` +
  `permWitness_complete` mirrors become derivable — **DONE**
  (G1-M `90839d4`; `dis_convert_perm` retired at P3c `9f41bd3`).
- B4. **The linear-class design** (ruling before build) → the bsort
  rows → `bsort_*` mirrors — **the rows are DONE, the ruling was
  NOT taken.** The `linear:` class was unlocked at P5a
  (`gz_linear_defn_branch`, a parametric class lemma) and reached at
  P6, as delegated sprint judgment calls, WITHOUT the pre-build ruling
  this line reserved. Flagged in the end-of-branch audit's ruling
  queue (A6-B2 / synthesis R-7); the ruling point below is therefore
  still live, now retrospectively.
- B5. **Auto-extraction**: generated body/symbol/formula constants
  from the logs (retire the hand transcriptions; the by-decide pins
  become generated canaries).
- B6. **Generator coverage**: M3+ measure shapes (retire the 4 hand
  exec kits); the decode-assembly generator (retire the ~43 hand
  decode proofs).
- B7. **Catalog auto-registration** (rows registered mechanically;
  hand text only for pend/skip dispositions).
- ACCEPTANCE TEST (the "genuinely nearly free" measurement): import
  a book we have NEVER imported (a fresh sorting-adjacent .lisp run
  through real ACL2), metric layer end-to-end, with ZERO hand Lean.
  Until that test passes, Track FREE is not free.

## PHASE C — Track REAL industrialized (the iso machinery)

Built from the pathfinder's LIST, generalized without
sorting-coupling (the old L-rules apply):
- C1. **The embedding kit**: `Acl2Embed` instances for
  Int/Nat/String/Char, each backed by core-logic restriction
  theorems; generic transport lemmas for the common predicate shapes
  (chains, counts, membership, erasure) over ANY embedding.
- C2. **`mirror_iso%`**: the generator — user declares
  `mirror def ↔ waypoint def [via embedding]`; the template proves
  it (the derive_sim% design one level up: same-recursion walk;
  template failure = hard error = the reading reassociates;
  the escape is a book theorem, replayed).
- C3. **Theorem transport assembly**: from waypoint theorem +
  declared isos → the mirror theorem statement + proof, generated
  (the decode-assembly generator's sibling).
- C4. **The product seam gate**: a mirror theorem's proof must
  transitively consume replayed constants (claims-tier, like
  check-mirrors-pure); plus the mirror purity gate already in ci.
- ACCEPTANCE TEST: `msort_ordered` + `msort_perm` at Int land
  with user input ≈ the two iso declarations (count the user lines;
  publish the number — the Track REAL metric is USER-LINES PER
  MIRROR, and it must fall book over book).

## PHASE D — sorting close-out (all 13 Props become theorems)

- qsort/bsort mirrors via C machinery as B3/B4 unlock rows.
- `ordered_perm_unique` (ORDERED-PERMS) + `sorts_agree` (the three
  capstones, post-B2) + `perm_iff_howMany`/`permWitness_complete`
  (post-B3).
- `sorter_unique` (the abstract capstone) via the
  parametric/encapsulate lane — and the ORDER-GENERIC ruling: attempt
  route 2 (the constrained-order book variant) here if the
  encapsulate lane is strong enough; else instance-scope the Prop
  honestly and log route 2 as the successor.
- EXIT: every Prop in Mirrors/Sorting.lean is a theorem (or its
  blocking frontier is named IN the file, dated).

## PHASE E — the demo, round two (on the real product)

Presentation only, built on D: the mirror file IS the front page;
the trust story is now genuinely two files (the spec + the kernel);
the metric layer is the appendix. The fresh-eyes Lean-expert test
(Mike's brief) is the acceptance audit — rerun until a first-time
reader reconstructs the trust base unaided.

## Sequencing & dependencies

A first (route-proof; nothing else starts until the route works).
Then B1 ∥ C1–C2 (independent), B2/B3 behind B1's machinery where
shared, C3–C4 behind C2, D behind {B2,B3,B4,C}, E last. Ruling
points: B4 design; the order-generic attempt (D); any mint outside
existing debt classes; per the goal rule every arc carries the
standard escape hatch. Audits: per-phase exit under the two-standard
rule (adversarial only for claims/semantics/records; gates get the
deletion review); the fresh-eyes test at E.

## What "done" means for the demo

The Track FREE acceptance test passes (a never-seen book, zero hand
Lean in the metric layer); every Mirrors/Sorting.lean Prop is a
theorem or carries a named, dated frontier; user-lines-per-mirror is
published and falling; the fresh-eyes reader answers "what do I read,
what do I trust" with: this file, the kernel, nothing else.
