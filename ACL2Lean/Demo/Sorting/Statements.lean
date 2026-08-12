import ACL2Lean.Imported.Mirrors.Catalog

/-!
# THE STATEMENTS — what is proved, and what you have to trust

The demo's front door (`docs/demo/1-tcb.md` is the tour).

**THE TRUST BASE IS THIS FOLDER — in two tiers.**

*TIER A — you ACCEPT the assumptions as stated.* Then the trust base is
this folder plus one file: `TCB.lean` (the definitions, 204) + this
page (the statements, 405) + `Assumptions.lean` (the 18 assumed facts,
566, needed only for an entry whose receipt carries `sorryAx`) +
`ACL2Lean/Lexorder.lean` (104 — `lexorderB`, which `TCB.lean`'s
`LexSorted` bottoms out in; you may instead take it on its kernel-
checked order properties — `lexorder_refl`/`_antisymm`/`_trans`/
`_total` in `ACL2Lean/LexorderOrder.lean` — and read the
implementation no further). If you also care about the ATTRIBUTION —
which ACL2 functions these came from — add the transcripts in
`AclSource.lean` (670, pure data). **~710 lines of definitions +
statements, ~1280 with the assumptions, ~1950 with the transcripts.**

*TIER B — you want to VALIDATE the assumptions rather than accept
them.* Their statements are written over the semantic core, so reading
them for content means adding `ACL2Lean/EvalOpt.lean` (824),
`ACL2Lean/Logic.lean` (764) and `ACL2Lean/Syntax.lean` (886) — plus
`ACL2Lean/Parser.lean` (745), which rides into the import closure via
`EvalOpt.lean` (it is a reader, not part of the semantics — but it IS
in the closure, so it is named here rather than quietly excluded) — and
the `AclSource.lean` bodies each assumption mentions. **~3200 further
lines.** Note the fuel convention you will hit immediately: `evalOpt`
is fuel-bounded, and every assumption states convergence in the
`∃ N, ∀ f ≥ N, evalOpt f … = some v` form, which is well-defined
because evaluation is fuel-MONOTONE (`evalOpt_fuel_mono` /
`evalOpt_ge_fuel`, `ACL2Lean/EvalOpt.lean`) — machinery-side context
for reading the statements, NOT part of either tier's trust base.

Which assumptions a given headline actually rests on is not a guess:
the ATTRIBUTION RECEIPT at the bottom of this page lists them
per-theorem and fails the build if the list is wrong.

Everything below is a RESTATEMENT of a catalog native
(`Mirrors/Catalog.lean`): every proof on this page is a direct
application of an already-proved constant, so this file adds *zero*
proof content. It is the ONE demo file that imports machinery, and it
imports it for statements only.

## THE TRUST MAP

**1. TRUSTED — what you must read and believe.**

* The **Lean kernel** (the sole trust anchor of the project).
* **The statements on this page.** They are ordinary Lean propositions
  about ordinary Lean functions (`isortL`, `qsortL`, `msortL`,
  `List.count`, `List.Perm`, `List.IsChain`) whose definitions live in
  `Demo/Sorting/TCB.lean`. For the §1–4 NATIVE entries no `evalOpt`, no
  `EvTrue`, no `World`, no `boolEnc` and no `*Exec` function appears in
  any of them — the catalog's CRITERION-1 GATE mechanizes exactly that
  ban, and it covers exactly those constants (the `.native`/
  `.nativeSorried` catalog entries this page restates). §5's four
  capstone entries are DIFFERENT and outside that gate's scope by
  design: they are DEEP-EMBEDDED conditionals over `EvTrue`/`evalOpt`
  at an abstract or canonical `World`, labelled as such where they
  appear — `#check` them and read the telescope, do not read them as
  native statements. Read them all; as *Lean theorems* they are the
  whole claim, and the kernel has checked every one.
* **That the definitions are the ones you want.** `isortL`, `qsortL`,
  `msortL` are ordinary Lean definitions in `TCB.lean` — read them and
  satisfy yourself they are the sorting functions YOU mean, exactly as
  you would for any Lean development. That is the whole obligation.
  You do NOT need to trust — or care — what ACL2's functions do: ACL2
  is this project's untrusted proof-search oracle, and its relationship
  to these definitions is an engineering question (whether the replay
  route can construct the proofs below), never a premise of the
  theorems.

**2. UNTRUSTED BUT KERNEL-CHECKED — a bug here CANNOT make a statement
here false; it makes the build fail.**

All of ACL2's proof search, our ACL2 instrumentation (the `acl2/`
fork's proof-log emission), the proof-log parser, the proof-tree
reconstruction, the replay driver that turns a recorded ACL2 clause
tree into a Lean `Expr` — and equally the **semantic core** (`SExpr`,
`Logic`, `evalOpt`), the **encoders** (`enc`/`boolEnc`/`intRep`) the
route runs through, and our **transcriptions of the ACL2 defuns**
(`AclSource.lean`). Each theorem below is a kernel-checked proof term;
the pipeline only ever *proposes* one. A bug anywhere in it —
including our transcriptions simply being the wrong functions — can
make a proof FAIL TO EXIST; it cannot make a statement on this page
false.

The "imported" label is ATTRIBUTION, not a premise: it records how
each proof was found (ACL2 searched; we replayed; the kernel
checked). The catalog's SEAM GATE keeps the attribution honest —
each native's proof must consume its own `driver_replayed%` constant,
so a "mirror" cannot quietly detach from the ACL2 proof it credits
(known limit, stated in the gate: detachment, not mis-pairing). The
source-hash provenance, per-book statement pins, and the differential
harness likewise serve the import route's HEALTH — keeping replay
working and honestly attributed — not the truth of this page.

**3. VISIBLE DEBT — what is assumed, and where it is written down.**

Exactly **20** `sorry`s exist in the whole library, and **18 of them —
every one this demo touches — are in `Demo/Sorting/Assumptions.lean`.
That file IS the list.** (The other two belong to other books:
`drv_tp_len` in `Imported/Lifting.lean`, `drv_tp_mylen` in
`Imported/SimpleWorld.lean`.) Each is a self-contained statement about
our own semantic model, ASSUMED for now — the one place a falsehood
COULD enter a `sorryAx`-marked entry below, which is why they are
surfaced rather than hidden. (ACL2 did discharge every one; that is the
evidence they are true and the reason each has a mechanical replay
unlock — but on this page the honest word is: assumed.)

By CLASS (each class names its unlock; the authoritative registry is
the DEBT REGISTRY block at the top of `TODO.md`, mechanized by the
PROVENANCE GATE in `Mirrors/Catalog.lean`):

| class | count | what it is | unlock |
| --- | --- | --- | --- |
| `tp:` type-prescription | 12 | ACL2-emitted type corollaries of a defun (e.g. "`(insert e x)` is a `consp`") | a TP-replay discharge route |
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

-- The `ACL2.Imported.Showcase` namespace is DELIBERATE and load-bearing
-- (it predates the demo-v2 move of this file out of `Imported/`): every
-- fully-qualified name below, and therefore all 12 `#guard_msgs` axiom
-- receipts, is spelled with it. Renaming the namespace rewrites — and
-- so silently re-pins — every receipt on the page. Don't.
namespace ACL2.Imported.Showcase

open ACL2 ACL2.Worlds.Sorting ACL2.Imported.Mirrors

/-! ## 1. Insertion sort

Imported from `acl2/books/sorting/isort.lisp`. `isortL` is plain Lean
(`Demo/Sorting/TCB.lean`); `lexorderB` is ACL2's total order on
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

**These four entries are DEEP-EMBEDDED, unlike §§1–4.** Their
statements are `EvTrue w env ⟦formula⟧` over `evalOpt` — the ACL2
formula inside our semantic model, not a native Lean proposition about
`isortL`-style functions — so reading them means reading `EvalOpt.lean`
too (tier B above), and the criterion-1 vocabulary gate does not, and
is not meant to, apply to them.

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

/-! ## WHICH ASSUMPTIONS DOES EACH THEOREM USE?

The receipt below is the PER-THEOREM ATTRIBUTION: for every headline on
this page, the exact set of `Assumptions.lean` statements its proof
transitively consumes. **The expected lists are written out in the
source below — that list IS the disclosure** ("this theorem assumes
exactly these"), and the check recomputes them from the proof terms and
FAILS THE BUILD naming the delta if a headline ever acquires or sheds
one. So `isort_sorts` rests on ONE assumption (`dis_insert_tp`), not on
all eighteen; the two parametric capstones rest on NONE, and an entry
with `[]` that acquires debt fails here too.

The measurement is a transitive walk of each proof term's constants
(`Expr.getUsedConstants`), keeping those named `dis_*`/`drv_*` that
carry `sorryAx` — exactly the registered FORBIDDEN-DEBT entries (the
PROVENANCE GATE in `Mirrors/Catalog.lean` is what makes that naming
exhaustive: an unregistered `dis_*`/`drv_*` constant fails the build
there). Deterministic, no heuristics. -/

open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let attribution : List (Name × List Name) :=
    [(``isort_sorts,               [``dis_insert_tp]),
     (``isort_preserves_count,     [``dis_how_many_tp]),
     (``msort_sorts,               [``dis_merge2_total, ``dis_msort_total,
                                    ``dis_evens_tp]),
     (``msort_preserves_count,     [``dis_merge2_total, ``dis_msort_total,
                                    ``dis_how_many_tp]),
     (``qsort_sorts,               [``dis_pce_total, ``dis_o_lt_total,
                                    ``dis_how_many_tp, ``dis_all_rel_tp,
                                    ``dis_acl2_count_tp, ``dis_convert_perm,
                                    ``dis_append_tp]),
     (``qsort_preserves_count,     [``dis_o_lt_total, ``dis_how_many_tp,
                                    ``dis_acl2_count_tp]),
     (``qsort_perm,                [``dis_pce_total, ``dis_o_lt_total,
                                    ``dis_how_many_tp, ``dis_acl2_count_tp,
                                    ``dis_convert_perm]),
     (``pce_is_a_complete_witness, [``dis_pce_total, ``dis_how_many_tp]),
     (``sorts_equivalence_weak,    []),
     (``sorts_equivalence_strong,  []),
     (``sorts_equivalence_weak_at_canonical,
                                   [``dis_pce_total, ``dis_how_many_tp,
                                    ``dis_sortfn1_insert_tp,
                                    ``dis_sortfn1_tp]),
     (``sorts_equivalence_strong_at_canonical,
                                   [``dis_pce_total, ``dis_how_many_tp,
                                    ``dis_ssortfn1_insert_tp])]
  let env ← getEnv
  for (head, expected) in attribution do
    let mut frontier : List Name := [head]
    let mut visited : NameSet := {}
    let mut used : List Name := []
    while !frontier.isEmpty do
      let c := frontier.head!
      frontier := frontier.tail!
      unless visited.contains c do
        visited := visited.insert c
        let s := (c.componentsRev.headD Name.anonymous).toString
        let mut isDebt := false
        if s.startsWith "dis_" || s.startsWith "drv_" then
          isDebt := (← collectAxioms c).contains ``sorryAx
        if isDebt then
          used := used ++ [c]
        else if let some ci := env.find? c then
          if let some v := ci.value? then
            frontier := v.getUsedConstants.toList ++ frontier
    let unlisted := used.filter (!expected.contains ·)
    let stale := expected.filter (!used.contains ·)
    unless unlisted.isEmpty && stale.isEmpty do
      throwError "assumption-attribution receipt: {head}'s expected \
        assumption list is wrong. CONSUMED BUT NOT LISTED: {unlisted}; \
        LISTED BUT NOT CONSUMED: {stale}. (The list on this page is the \
        per-theorem disclosure — fix the list, or explain the change.)"

/-! ## Where to go next

* The full scoreboard is `liftCatalog` in `Mirrors/Catalog.lean` — one
  decision per green row of the corpus sweep, kept honest by five
  build-failing gates (lift-coverage, seam, axiom-exactness,
  criterion-1 vocabulary, provenance).
* The sweep itself is `just ci`'s `driver-coverage` against
  `Tests/driver-coverage.golden`.
* The objects of study are `ACL2Lean/Demo/Sorting/TCB.lean`.
* The assumed facts are `ACL2Lean/Demo/Sorting/Assumptions.lean`.
* The reader path is `docs/demo/` (index: `docs/DEMO.md`) — part 2 is
  how to replay a book yourself, part 3 is how the machinery works. -/

end ACL2.Imported.Showcase
