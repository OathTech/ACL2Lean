import ACL2Lean.Imported.Mirrors.Catalog

/-!
# THE SHOWCASE — what is proved, and what you have to trust

The demo's front door. Everything below is a RESTATEMENT of a catalog
native (`Mirrors/Catalog.lean`): every proof on this page is a direct
application of an already-proved constant, so this file adds *zero*
proof content. It exists so a Lean reader who does not speak ACL2 can
see the headline results and their axiom receipts in one place.

Reader path: `docs/DEMO.md`.

## THE TRUST MAP

**1. TRUSTED — what you must read and believe.**

* The **Lean kernel** (the sole trust anchor of the project).
* **The statements on this page.** They are ordinary Lean propositions
  about ordinary Lean functions (`isortL`, `qsortL`, `msortL`,
  `List.count`, `List.Perm`, `List.IsChain`) whose definitions live in
  `Imported/Sorting/Sims.lean`. No `evalOpt`, no `EvTrue`, no `World`,
  no `boolEnc` and no `*Exec` function appears in any of them — the
  catalog's CRITERION-1 GATE mechanizes exactly that ban on the
  constants restated here. Read them; as *Lean theorems* they are the
  whole claim, and the kernel has checked every one.
* **That those Lean functions really are ACL2's.** This is the extra
  belief the word "imported" carries, and it is a question of
  AUTHENTICITY, not of truth. `isortL` is OUR transcription of the
  `isort` in `acl2/books/sorting/isort.lisp`; believing the headline
  below is a statement *about ACL2's insertion sort* means trusting
  (a) the `defun` body constants in `Sims.lean` against the `.lisp`
  source, (b) the **semantic core** — `SExpr`, `Logic`, `evalOpt` —
  as a faithful model of ACL2, and (c) the **encoders** of
  `Imported/Lifting.lean` (`enc`/`boolEnc`/`intRep`). Those are
  separately enforced, never by the kernel: source-hash provenance on
  every proof log (`scripts/check-log-provenance.sh`), hand statement
  pins per book (`Tests/SortingPins.lean`), differential testing of
  the interpreter against real ACL2 (`just diff-test`), and audits.

**2. UNTRUSTED BUT KERNEL-CHECKED — a bug here CANNOT make a statement
here false; it makes the build fail.**

All of ACL2's proof search, our ACL2 instrumentation (the `acl2/`
fork's proof-log emission), the proof-log parser, the proof-tree
reconstruction, and the replay driver that turns a recorded ACL2
clause tree into a Lean `Expr`. Each theorem below is a kernel-checked
proof term; the pipeline only ever *proposes* one. The same holds of
tier 1's semantic core and encoders: a bug in either cannot falsify a
statement here, it can only leave a TRUE statement that is not the
ACL2 theorem it is presented as. That is exactly why tier 1 splits
truth from authenticity.

The ACL2 seam is mechanized: the catalog's SEAM GATE requires each
native's proof to consume its own `driver_replayed%` constant, so a
"mirror" cannot quietly detach from the ACL2 proof it claims to
import. Known limit, stated in the gate itself: it rules out
DETACHMENT, not MIS-PAIRING (a proof reaching a *different* book's
replayed statement would pass) — seam pairings stay an audit item.

**3. VISIBLE DEBT — what is assumed, and where it is written down.**

Exactly **20** `sorry`s exist in the whole library, all of them
statements ACL2 *did* discharge but whose replay route is not wired
yet. They are quarantined and registered, never scattered:

* 12 in `ACL2Lean/Imported/Sorting/Debt.lean` — the sorting books'
  dischargers. That file IS the list.
* 8 more in `Imported/SortingBsort.lean` (2), `Imported/EquisortWitness.lean`
  (4), `Imported/SimpleWorld.lean` (1), `Imported/Lifting.lean` (1).

By CLASS (each class names its unlock; the authoritative registry is
the DEBT REGISTRY block at the top of `TODO.md`, mechanized by the
PROVENANCE GATE in `Mirrors/Catalog.lean`):

| class | count | what it is | unlock |
| --- | --- | --- | --- |
| `tp:` type-prescription | 14 | ACL2-emitted type corollaries of a defun (e.g. "`(insert e x)` is a `consp`") | a TP-replay discharge route |
| `total:` termination | 5 | a defun's admission (`MERGE2`, `MSORT`, `O<`, `PERM-COUNTER-EXAMPLE`, `BNEXT`) | `with_termination` admission coverage (machinery exists; the rows need wiring) |
| `rule:` previously-proved | 1 | `CONVERT-PERM-TO-HOW-MANY` used as a rewrite rule | the R-lane arc (PERM-TLFIX replay) |

Every debt entry is FORCED to stay visible: the provenance gate fails
the build if a registered entry's `sorry` is replaced by a Lean-side
proof, and the axiom gate fails if a `.nativeSorried` catalog entry
stops carrying `sorryAx`. So the receipts below cannot silently
improve OR silently rot.

**Not claimed here.** The three `*-IS-ISORT` sorts-equivalence rows
(msort/qsort/bsort each equal isort at a concrete world) are NOT on
this page: they regressed to ASSUMED under the 2026-08-11 thin-Lean
purge and have no native constant today. What IS available is the
abstract uniqueness capstone, below, stated honestly with its kept
premises.
-/

namespace ACL2.Imported.Showcase

open ACL2 ACL2.Worlds.Sorting ACL2.Imported.Mirrors

/-! ## 1. Insertion sort

Imported from `acl2/books/sorting/isort.lisp`. `isortL` is plain Lean
(`Imported/Sorting/Sims.lean`); `lexorderB` is ACL2's total order on
the value universe, as a `Bool`. -/

/-- **INSERTION SORT SORTS.** ACL2's `ORDEREDP-ISORT`, restated in
    Mathlib's vocabulary: adjacent pairs of `isortL xs` are in
    lexorder, for every input list. -/
theorem isort_sorts (xs : List SExpr) : LexSorted (isortL xs) :=
  orderedp_isort_isChain_driver xs

-- The receipts below are `#guard_msgs` pins, so the axiom set of every
-- headline is checked BY THE BUILD and printed ON THE PAGE. `(whitespace
-- := lax)` only because the four-axiom list wraps in the generated
-- message; each pin is content-exact on the axiom set (the precedent is
-- the retired EquisortParametric pins, now in the catalog axiom gate).
/-- info: 'ACL2.Imported.Showcase.isort_sorts' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isort_sorts

/-- **INSERTION SORT PRESERVES MULTIPLICITY.** ACL2's `HOW-MANY-ISORT`
    — this is the book's PERMUTATION result, stated the way ACL2
    states it (multiplicity-wise, over `List.count`). -/
theorem isort_preserves_count (e : SExpr) (xs : List SExpr) :
    (isortL xs).count e = xs.count e :=
  how_many_isort_native_driver e xs

/-- info: 'ACL2.Imported.Showcase.isort_preserves_count' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isort_preserves_count

/-! ## 2. Merge sort — `acl2/books/sorting/msort.lisp` -/

/-- **MERGE SORT SORTS.** ACL2's `ORDEREDP-MSORT`. -/
theorem msort_sorts (xs : List SExpr) : LexSorted (msortL xs) :=
  orderedp_msort_isChain_driver xs

/-- info: 'ACL2.Imported.Showcase.msort_sorts' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms msort_sorts

/-- **MERGE SORT PRESERVES MULTIPLICITY.** ACL2's `HOW-MANY-MSORT`. -/
theorem msort_preserves_count (e : SExpr) (xs : List SExpr) :
    (msortL xs).count e = xs.count e :=
  how_many_msort_native_driver e xs

/-- info: 'ACL2.Imported.Showcase.msort_preserves_count' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms msort_preserves_count

/-! ## 3. Quicksort — `acl2/books/sorting/qsort.lisp` -/

/-- **QUICKSORT SORTS.** ACL2's `ORDEREDP-QSORT` — the deepest replay
    in the corpus (fourteen kept conditions, well-founded recursion
    admitted through the `acl2-count`/`O<` ordinal kit). -/
theorem qsort_sorts (xs : List SExpr) : LexSorted (qsortL xs) :=
  orderedp_qsort_isChain_driver xs

/-- info: 'ACL2.Imported.Showcase.qsort_sorts' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qsort_sorts

/-- **QUICKSORT PRESERVES MULTIPLICITY.** ACL2's `HOW-MANY-QSORT`. -/
theorem qsort_preserves_count (e : SExpr) (xs : List SExpr) :
    (qsortL xs).count e = xs.count e :=
  how_many_qsort_native_driver e xs

/-- info: 'ACL2.Imported.Showcase.qsort_preserves_count' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qsort_preserves_count

/-- **QUICKSORT PERMUTES.** ACL2's `PERM-QSORT`, in Mathlib's
    `List.Perm`. (Available here because ACL2 proves the permutation
    statement itself for qsort — for isort the book proves only the
    multiplicity form, which is why §1 stops there.) -/
theorem qsort_perm (xs : List SExpr) : (qsortL xs).Perm xs :=
  perm_qsort_perm_driver xs

/-- info: 'ACL2.Imported.Showcase.qsort_perm' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qsort_perm

/-! ## 4. The witness function works

`PERM-COUNTER-EXAMPLE` is ACL2's *witness*: given two lists it returns
the single element at which they disagree, if any. The imported
theorem says the witness is COMPLETE — testing that one element
decides permutation-hood. -/

/-- **THE COUNTEREXAMPLE WITNESS IS COMPLETE.** ACL2's
    `PERM-COUNTER-EXAMPLE-IS-COUNTEREXAMPLE-FOR-TRUE-LISTS`: two lists
    are permutations exactly when their counts agree at `pceL xs ys`.
    (A non-permutation is always caught at that one element.) -/
theorem pce_is_a_complete_witness (xs ys : List SExpr) :
    xs.isPerm ys = (xs.count (pceL xs ys) == ys.count (pceL xs ys)) :=
  pce_is_counterexample_native_driver xs ys

/-- info: 'ACL2.Imported.Showcase.pce_is_a_complete_witness' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pce_is_a_complete_witness

/-! ## 5. The sorts-equivalence capstone — HONESTLY CONDITIONAL

`acl2/books/sorting/equisort.lisp` proves that ANY two sorting
functions meeting the same constraints are equal on true lists. ACL2
proves it in a CONSTRAINED theory (the `encapsulate`'s witnesses are
local and gone), so there is no witness-level Lean statement to make:
the first-class artifact is the world-PARAMETRIC constant — the same
recorded proof tree replayed over an arbitrary `w : World`, with the
scope's constraints as explicit premises.

These are therefore presented as the CONDITIONALS they are: the
constants' types carry their premise telescopes (the constraint
theorems in stored-rule form, the signature functions' totality, the
builtin no-shadow facts). Nothing is definition-pinned and no witness
vocabulary appears — pinned separately in `Tests/ParametricPins.lean`.

`#check` them to read the telescope; the aliases below just name them
on this page. -/

/-- WEAK uniqueness: under the scope-1 constraints, `SORTFN1` and
    `SORTFN2` agree on true lists. Conditional — see the constant's
    type for the premises. -/
def sorts_equivalence_weak := weakSortfn1IsSortfn2Parametric

/-- info: 'ACL2.Imported.Showcase.sorts_equivalence_weak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sorts_equivalence_weak

/-- STRONG uniqueness: the unconditional-conclusion variant over the
    strongly-constrained scope. Conditional in the same sense. -/
def sorts_equivalence_strong := strongSsortfn1IsSsortfn2Parametric

/-- info: 'ACL2.Imported.Showcase.sorts_equivalence_strong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sorts_equivalence_strong

/-! ### The capstones at a concrete world

Phase 3 applies each parametric constant at the equisort canonical
world, discharging every premise kernel-checked EXCEPT two, which stay
as honest hypotheses: `rule:CONVERT-PERM-TO-HOW-MANY` and
`use:ORDERED-PERMS`. So these are PARTIAL non-vacuity witnesses, not
closed theorems — and they are additionally backed by the `total:`/
`tp:` debt above, which is why their receipts carry `sorryAx` while
the parametric pair above does not. -/

/-- WEAK at the equisort canonical world — two kept hypotheses. -/
def sorts_equivalence_weak_at_canonical := weakSortfn1IsSortfn2AtCanonical

/-- info: 'ACL2.Imported.Showcase.sorts_equivalence_weak_at_canonical' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sorts_equivalence_weak_at_canonical

/-- STRONG at the equisort canonical world — two kept hypotheses. -/
def sorts_equivalence_strong_at_canonical :=
  strongSsortfn1IsSsortfn2AtCanonical

/-- info: 'ACL2.Imported.Showcase.sorts_equivalence_strong_at_canonical' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sorts_equivalence_strong_at_canonical

/-! ## Where to go next

* The full scoreboard is `liftCatalog` in `Mirrors/Catalog.lean` — one
  decision per green row of the corpus sweep, kept honest by five
  build-failing gates (lift-coverage, seam, axiom-exactness,
  criterion-1 vocabulary, provenance).
* The sweep itself is `just ci`'s `driver-coverage` against
  `Tests/driver-coverage.golden`.
* The objects of study are `ACL2Lean/Imported/Sorting/Sims.lean`.
* The assumed facts are `ACL2Lean/Imported/Sorting/Debt.lean`.
* The reader path is `docs/DEMO.md`. -/

end ACL2.Imported.Showcase
