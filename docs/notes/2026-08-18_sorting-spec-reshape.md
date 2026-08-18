# The sorting mirror spec's RESHAPE — the 16-`Prop` bijection

**Date:** 2026-08-18 (R4 wave 2f)
**Subject:** `ACL2Lean/Mirrors/Sorting.lean`'s target-property section
**Status:** RULED and LANDED. Mike approved the reshape checkpoint on
2026-08-18 ("Agree on all"); this note is the permanent record.

This is the record the shop window points to NOWHERE. `Mirrors/
Sorting.lean` is reader-facing and now carries only forward-looking
text: what each `Prop` says and which book theorem it mirrors. The
history — what the section used to say, why each row moved, and what
was checked before it moved — lives here, and a future reader finds it
through the docs, not through a comment in the spec.

---

## Why the section was re-opened

The target-property section is the DEFINITION OF DONE for sorting: the
buildout is finished when every `Prop` there is a `theorem` proved via
replay. That makes the section's CONTENT a claim in its own right — it
asserts both "these are the things the ACL2 corpus proves" and "these
are all of them". Neither half had ever been checked against the
corpus. It had accreted, `Prop` by `Prop`, from what each wave happened
to be aiming at.

Three waves of measurement had already reported symptoms without
naming the cause:

* wave 2c: **`isort_perm` — NOT a machinery gap: THE BOOK DOES NOT
  PROVE IT.** The `Prop` said `∀ xs, Permuted (isort xs) xs`; the isort
  book proves `HOW-MANY-ISORT`. Reaching the `Prop` needed a
  COMPOSITION of two book theorems, i.e. a meta-theorem mechanism that
  does not exist.
* wave 2e: **`perm_iff_howMany` — THE BOOK DOES NOT PROVE THE
  `∀`-FORM.** The `→` direction ("a permutation has equal counts
  EVERYWHERE") is in no `(:DEFTHM …)` row of the corpus; closing it in
  Lean would be `List.Perm.count_eq`, the ornamental-import
  antipattern.
* wave 2e: **`sorts_agree` … is additionally a COMPOSITION**
  (`mirror_transport%` cites ONE waypoint exactly), because one `Prop`
  bundled three separate book capstones.

Each was recorded as a frontier of the MACHINERY. They are not. They
are all one defect in the SPEC: `Prop`s that no single book theorem
backs, and book theorems that no `Prop` names. A frontier that only a
missing meta-theorem could cross is, in these cases, a statement the
corpus was never going to deliver.

---

## Part 1 — THE INVENTORY (the complete corpus extraction)

Every `(:DEFTHM …)` row emitted by the eleven sorting proof logs,
extracted mechanically from the real artifacts (`.tmp/reshape/local-
defthms.txt`, 75 rows over 11 books; `how-many.proof-log` and
`orderedp.proof-log` contain no `defthm` at all). Books in extraction
order:

| book | rows |
|---|---|
| `bsort` | 8 |
| `convert-perm-to-how-many` | 13 |
| `equisort` | 14 |
| `how-many` | 0 |
| `isort` | 3 |
| `msort` | 7 |
| `ordered-perms` | 6 |
| `orderedp` | 0 |
| `perm` | 8 |
| `qsort` | 13 |
| `sorts-equivalent` | 3 |
| **total** | **75** |

The 75 rows partition into five classes, and the partition is the whole
adjudication:

**RESULT TIER (16)** — what a book proves about its OWN TOP-LEVEL
function:

`ORDEREDP-ISORT`, `HOW-MANY-ISORT`, `ORDEREDP-MSORT`, `HOW-MANY-MSORT`,
`ORDEREDP-QSORT`, `HOW-MANY-QSORT`, `PERM-QSORT`, `ORDEREDP-BSORT`,
`HOW-MANY-BSORT`, `ORDERED-PERMS`, `PERM-IS-AN-EQUIVALENCE`,
`CONVERT-PERM-TO-HOW-MANY`, `MSORT-IS-ISORT`, `QSORT-IS-ISORT`,
`BSORT-IS-ISORT`, `STRONG-SSORTFN1-IS-SSORTFN2`.

**SUPPORT TIER (38)** — lemmas about HELPER functions, steps inside
those proofs: `HOW-MANY-SMALLER-BNEXT`, `HOW-MANY-BAD-PAIRS-BNEXT`,
`ORDEREDP-WHEN-BNEXT-CONSTANT`, `HOW-MANY-BNEXT` (bsort, 4);
`HOW-MANY-RM`, `NOT-MEMB-IMPLIES-RM-IS-NO-OP`,
`NOT-MEMB-IMPLIES-HOW-MANY-IS-0`, `HOW-MANY-RM-GENERAL`, `PERM-TLFIX`,
`PERM-COUNTER-EXAMPLE-TLFIX-1`, `RM-TLFIX`, `MEMB-TLFIX`,
`PERM-COUNTER-EXAMPLE-TLFIX-2`, `HOW-MANY-TLFIX` (convert-perm, 10);
`ACL2-COUNT-EVENS-STRONG`, `ACL2-COUNT-EVENS-WEAK`, `HOW-MANY-MERGE2`,
`HOW-MANY-EVENS-AND-ODDS` (msort, 4); `ORDEREDP-RM`, `ORDEREDP-MEMB`,
`EQUAL-CONS`, `CAR-RM` (ordered-perms, 4); `PERM-CONS`,
`PERM-SYMMETRIC`, `MEMB-RM`, `PERM-MEMB`, `COMM-RM`, `PERM-RM`,
`PERM-TRANSITIVE` (perm, 7); `HOW-MANY-APPEND`, `HOW-MANY-FILTER-1`,
`CAR-APPEND`, `ORDEREDP-APPEND`, `ALL-REL-FILTER-1`,
`ALL-REL-FILTER-2`, `ALL-REL-RM-1`, `ALL-REL-RM-2`,
`PERM-IMPLIES-EQUAL-ALL-REL-2` (qsort, 9).

(`PERM-SYMMETRIC` and `PERM-TRANSITIVE` are support here in the
specific sense that they are the CONJUNCTS `PERM-IS-AN-EQUIVALENCE`
bundles: the result-tier row is the bundle ACL2 exports as a
`defequiv`, and the mirror `Prop` is that bundle.)

**TYPE-ABSORBED (11)** — `TRUE-LISTP-BNEXT`, `TRUE-LISTP-BSORT`,
`TRUE-LISTP-RM` (convert-perm), `TRUE-LISTP-ISORT`, `TRUE-LISTP-MSORT`,
`TRUE-LISTP-RM` (ordered-perms), `TRUE-LISTP-QSORT`,
`TRUE-LISTP-SORTFN1`, `TRUE-LISTP-SORTFN2`, `TRUE-LISTP-SSORTFN1`,
`TRUE-LISTP-SSORTFN2`. Plus the `BOOLEANP` conjunct INSIDE
`PERM-IS-AN-EQUIVALENCE`. These say "the result is a proper list" /
"the relation is two-valued", which in Lean are the TYPES `List α` and
`Prop` the definitions already have.

**ENCAPSULATE CONSTRAINTS (8)** — `ORDEREDP-SORTFN1/2`,
`HOW-MANY-SORTFN1/2`, `ORDEREDP-SSORTFN1/2`, `HOW-MANY-SSORTFN1/2`.
These are the equisort scope's ASSUMPTIONS about its constrained
sorters, not results; in the mirror they are the capstone `Prop`'s
HYPOTHESES.

**COLLAPSED INTO A RESULT (2)** — `PERM-COUNTER-EXAMPLE-IS-COUNTER-
EXAMPLE-FOR-TRUE-LISTS` is `CONVERT-PERM-TO-HOW-MANY` under
`TRUE-LISTP` hypotheses (and is the step the book proves the general
one from); `WEAK-SORTFN1-IS-SORTFN2` is `STRONG-SSORTFN1-IS-SSORTFN2`
over sorters whose constraints carry `TRUE-LISTP` hypotheses. Once the
hypotheses are type-absorbed, each pair is ONE statement.

16 + 38 + 11 + 8 + 2 = 75.

---

## Part 2 — THE ADJUDICATION (before → after, row by row)

THIRTEEN `Prop`s became SIXTEEN. Ten rows moved.

| # | before | after | why |
|---|---|---|---|
| 1 | `isort_ordered` | KEEP, byte-identical | `ORDEREDP-ISORT` |
| 2 | `isort_perm` : `∀ xs, Permuted (isort xs) xs` | **RESHAPE** → `isort_howMany` : `∀ a xs, howMany a (isort xs) = howMany a xs` | no `PERM-ISORT` row exists; the book proves `HOW-MANY-ISORT` |
| 3 | `msort_ordered` | KEEP, byte-identical | `ORDEREDP-MSORT` |
| 4 | `msort_perm` | **RESHAPE** → `msort_howMany` | same; `HOW-MANY-MSORT` |
| 5 | `qsort_ordered` | KEEP, byte-identical | `ORDEREDP-QSORT` |
| 6 | — | **NEW** `qsort_howMany` | `HOW-MANY-QSORT` had no `Prop` |
| 7 | `qsort_perm` | KEEP, byte-identical | `PERM-QSORT` genuinely exists — qsort is the ONE sort the corpus states both ways |
| 8 | `bsort_ordered` | KEEP, byte-identical | `ORDEREDP-BSORT` |
| 9 | `bsort_perm` | **RESHAPE** → `bsort_howMany` | same; `HOW-MANY-BSORT` |
| 10 | `ordered_perm_unique` : `… → Permuted xs ys → xs = ys` | **RESHAPE** → `… → (xs = ys ↔ Permuted xs ys)` | `ORDERED-PERMS` is `(EQUAL (EQUAL A B) (PERM A B))` — an EQUIVALENCE; the implication was strictly weaker than the book |
| 11 | — | **NEW** `permuted_equivalence` | `PERM-IS-AN-EQUIVALENCE` had no `Prop` |
| 12 | `permWitness_complete` with `(xs ≠ [] ∨ ys ≠ []) →` | **RESHAPE** → the unconditional book form | `CONVERT-PERM-TO-HOW-MANY` carries no such hypothesis (part 6) |
| 13 | `sorts_agree` : one `Prop`, three conjuncts | **RESHAPE** → `msort_is_isort`, `qsort_is_isort`, `bsort_is_isort` | three separate book capstones bundled 3:1; the bundle could not land until ALL THREE natives existed, and needed a composition mechanism to land at all |
| 14 | `sorter_unique` : one `f`, compared to `isort`, hypothesis `Permuted (f xs) xs` | **RESHAPE** → two constrained sorters `f`, `g`, hypotheses `Ordered` + `howMany`-preservation on each, conclusion `f xs = g xs` | the equisort capstone relates TWO CONSTRAINED SORTERS, and its constraints are `ORDEREDP-SSORTFN…` + `HOW-MANY-SSORTFN…` — not one sorter against `ISORT`, and not `PERM` |
| 15 | `perm_iff_howMany` | **DROPPED** | no book theorem of that shape (part 5) |

---

## Part 3 — THE BIJECTION

The result of the adjudication, and the invariant the section now
carries (stated in the spec file's header, enforced by review):

| `Prop` | book theorem |
|---|---|
| `isort_ordered` | `ORDEREDP-ISORT` |
| `isort_howMany` | `HOW-MANY-ISORT` |
| `msort_ordered` | `ORDEREDP-MSORT` |
| `msort_howMany` | `HOW-MANY-MSORT` |
| `qsort_ordered` | `ORDEREDP-QSORT` |
| `qsort_howMany` | `HOW-MANY-QSORT` |
| `qsort_perm` | `PERM-QSORT` |
| `bsort_ordered` | `ORDEREDP-BSORT` |
| `bsort_howMany` | `HOW-MANY-BSORT` |
| `ordered_perm_unique` | `ORDERED-PERMS` |
| `permuted_equivalence` | `PERM-IS-AN-EQUIVALENCE` |
| `permWitness_complete` | `CONVERT-PERM-TO-HOW-MANY` |
| `msort_is_isort` | `MSORT-IS-ISORT` |
| `qsort_is_isort` | `QSORT-IS-ISORT` |
| `bsort_is_isort` | `BSORT-IS-ISORT` |
| `sorter_unique` | `STRONG-SSORTFN1-IS-SSORTFN2` |

Sixteen and sixteen, and the map is a bijection in both directions.

---

## Part 4 — THE IMPACT

What the reshape did to the buildout, measured in the same wave rather
than predicted:

| change | effect |
|---|---|
| `isort_perm` → `isort_howMany` | **LANDED as a product** (`isort_howMany_int`) — the transport had been blocked on a COMPOSITION that does not exist, and the book's own statement transports in three lines |
| `msort_perm` → `msort_howMany` | **LANDED** (`msort_howMany_int`) |
| `bsort_howMany` (new shape) | still unlanded — `HOW-MANY-BSORT` has no waypoint native and `bsortL` needs the bsort exec kit (unchanged by the reshape) |
| NEW `qsort_howMany` | **LANDED** (`qsort_howMany_int`) — the native existed all along and nothing named it |
| `ordered_perm_unique` → iff | **RE-LANDED as the iff** — cost: one decode corollary (`ordered_perms_iff_driver`) and one closer alternative through `map_inj_iff` |
| NEW `permuted_equivalence` | **LANDED** (`permuted_equivalence_int`) — needed no machinery at all |
| `permWitness_complete` unconditional | Prop now correct; the `Int` product remains structurally unavailable (part 6) |
| `sorts_agree` → three `Prop`s | the composition-mechanism blocker is GONE from the statement; all three remain unlanded on the missing `sorts-equivalent` waypoint module (a real gap, now correctly attributed) |
| `sorter_unique` reshaped | Prop now the book's; reachability recorded below |
| `perm_iff_howMany` dropped | a permanent frontier removed from the definition of done |

The pattern is the point: FIVE of the ten moved rows landed as products
IMMEDIATELY, with one closer alternative and one binder-table row
between them. What had been recorded as machinery frontiers across
three waves was, in those five cases, the spec asking for statements
the corpus does not make.

Machinery genuinely added, in full: the transport binder table's SCALAR
row (`∀ a : α` encoded by `e.enc`, hypothesis-free path only —
`isort_howMany`'s shape), `map_inj_iff` (`map_inj`'s `Iff` form, the
same injectivity plumbing as `enc_inj_iff` is to `Acl2Embed.inj`) and
two closer alternatives that use it. Three waypoint decode corollaries
(`ordered_perms_iff_driver`, `how_many_qsort_own_driver`,
`perm_equivalence_permL_driver`), each in the established decode class:
additive, no statement change to any catalogued native, no content of
its own.

---

## Part 5 — THE DROPS, AND WHERE THEIR CONTENT WENT

A `Prop` may be dropped or weakened only if nothing a user wanted is
lost. Each dropped or reshaped statement is a STEP-2 consequence of the
new set — ordinary Lean reasoning ABOVE the mirror, which is what
step 2 is for. None is added to the spec (canon line 1: no Lean-side
theorems specific to an example); the sketches exist so the record can
say the content is reachable.

* **old `ordered_perm_unique`** (the implication) — `.mpr` of the new
  `Iff`. One projection.
* **old `permWitness_complete`** (with the precondition) — the new one;
  the hypothesis is simply not used.
* **old `sorts_agree`** — `fun xs => ⟨msort_is_isort xs, qsort_is_isort
  xs, bsort_is_isort xs⟩`. The conjunction is the three `Prop`s.
* **old `sorter_unique`** (`f` against `isort`) — the new one at
  `g := isort`, whose two hypotheses are `isort_ordered` and
  `isort_howMany`, both members of the set. One instantiation.
* **old `isort_perm` / `msort_perm` / `bsort_perm`** — from the
  matching `*_howMany` and `permWitness_complete`: the latter says
  `Permuted xs ys` holds exactly when the counts agree at the ONE
  element the witness names, and `*_howMany` gives count agreement at
  EVERY element, in particular at that one. Two lines, and it is the
  book's own route (the witness is what makes the single check
  sufficient).
* **`perm_iff_howMany`** — this one is different and the record must
  say so rather than sketch around it. The `←` direction IS derivable
  (instantiate `permWitness_complete` at the witness). The `→`
  direction — "a permutation has equal counts EVERYWHERE" — is NOT in
  the corpus: the complete `(:DEFTHM …)` inventory above contains no
  `PERM-IMPLIES-EQUAL-HOW-MANY`-shaped row. It is dropped BECAUSE the
  books do not prove it, which is exactly what the bijection rule is
  for. If a user wants it, the honest answer is that the ACL2 corpus
  would have to prove it first.

---

## Part 6 — THE LINE-DRAWING RULE, AND THE `permWitness` ADJUDICATION

**The rule.** A `Prop` belongs in the section iff it mirrors a
RESULT-TIER book theorem: what a book proves about its OWN TOP-LEVEL
function, as against lemmas about helper functions (support), the
scope's assumptions (constraints), and statements the type system
already carries (type-absorbed). The rule cuts both ways and both
directions matter:

* NO MORE — a `Prop` with no book theorem behind it is a statement the
  replay can never deliver. It does not read as an open task; it reads
  as a machinery frontier, and it consumed three waves of measurement
  in that disguise.
* NO LESS — a book result with no `Prop` is a hole in the definition of
  done. `HOW-MANY-QSORT` and `PERM-IS-AN-EQUIVALENCE` had NATIVES
  ALREADY BUILT and nothing named them; both landed as products the
  moment they were named.

**The `permWitness_complete` adjudication (cites J-2e-6).** Wave 2e
ruled a precondition `(xs ≠ [] ∨ ys ≠ []) →` onto this `Prop`, to
quarantine `permWitness`'s junk arm (at `xs = ys = []` the Lean
rendering must invent a value where ACL2 has `(car nil)` = `nil`). The
ruling was implemented VERBATIM and its premise was then KERNEL-REFUTED
in the same wave (J-2e-6): the precondition does not quarantine the
junk arm, because the junk arm is reached BY RECURSION from inputs the
precondition admits. `permWitness xs ys` is the junk value on the
ENTIRE `Permuted` half — the walk reaches `permWitness [] []` exactly
when every element of `xs` was found and `ys` is exhausted — and the
disproof is at `xs = ys = [1]`, a point the precondition admits, by
`decide`.

So the precondition bought clarity and no route. Under the bijection
rule it also fails the rule itself: `CONVERT-PERM-TO-HOW-MANY` carries
no such hypothesis, so the guarded `Prop` mirrored no book theorem.
It is removed, and the `Prop` is the book's.

What that does NOT change: the `Int` PRODUCT is still structurally
unavailable, for the reason wave 2e established. The mirror rung needs
the ELEMENT-RESULT homomorphism square `permWitness (map e.enc xs)
(map e.enc ys) = e.enc (permWitness xs ys)`, which is FALSE at the junk
arm for any embedding of `Int`: `SExpr`'s default is `nil` and
`intEmbed.enc` is `.atom (.number (.int ·))`, never `nil`. The two
routes that remain are on the record and neither is an executor call —
an embedding whose `default` is in range (a spec/type question), or a
composition through a theorem the corpus does not prove. The `Prop` is
correct and the product is absent; the scoreboard says exactly that.

---

## MIKE'S RULINGS (2026-08-18, "Agree on all")

The checkpoint put five questions and all five were approved:

1. **THE 16-`Prop` BIJECTION** — adopted as stated, including every
   individual row of part 2.
2. **THE RESULT-TIER NO-LESS LINE** — the rule binds in BOTH
   directions; a book result with no `Prop` is a defect, not a
   backlog item.
3. **THE `ordered_perm_unique` IFF COST** — the `Iff` form is adopted
   even though it un-lands the existing product until a decode
   corollary and a closer alternative arrive. (Measured after the
   ruling: both were minimal and the product re-landed in the same
   wave.)
4. **`permWitness` KEPT IN BOOK FORM, WITH NO `Int` PRODUCT** — the
   precondition comes off; the missing product is recorded as an
   honest structural entry on the scoreboard rather than driving a
   spec change.
5. **`sorter_unique`'s `Prop` LANDS AS THE BOOK'S**, with the
   REACHABILITY QUESTION RECORDED: the mirror quantifies over an
   arbitrary Lean `f : List α → List α`, while a world-parametric
   constant can only be instantiated at the `evalOpt` image of a
   `World` defun, and there is no construction taking an arbitrary
   Lean function to an ACL2 world. Whether that `Prop` is reachable AS
   STATED is open, and it is a design question, not an executor call.
   The `Prop` is correct regardless, which is why it lands.

---

## What this note does not claim

The reshape is a claim about the SPEC's faithfulness to the corpus's
statements. It says nothing about the trust note in `CLAUDE.md`: a
kernel-accepted product still certifies only the replayed statement as
stated, not that the replayed statement or `evalOpt` faithfully model
ACL2. The bijection is checked by reading the extracted `(:DEFTHM …)`
rows against the `Prop`s — by review, not by a gate. That is
deliberate: a census gate over 75 rows is exactly the fragile
gate-cruft the two-standard rule says to delete rather than write.
