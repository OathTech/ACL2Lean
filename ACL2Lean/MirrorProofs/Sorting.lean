import ACL2Lean.MirrorProofs.TransportGen
import ACL2Lean.MirrorProofs.SortingSquares
import ACL2Lean.MirrorProofs.SortingPermSquares
import ACL2Lean.MirrorProofs.SortingQsortSquares
import ACL2Lean.MirrorProofs.SortingBsortSquares
import ACL2Lean.Imported.Waypoints.Isort
import ACL2Lean.Imported.Waypoints.Msort
import ACL2Lean.Imported.Waypoints.OrderedPerms
import ACL2Lean.Imported.Waypoints.PermBook
import ACL2Lean.Imported.Waypoints.Qsort
import ACL2Lean.Imported.Waypoints.BsortCap
import ACL2Lean.Imported.Waypoints.SortsEquivalent

/-! # Mirror proofs — the sorting book's PRODUCTS

The target `Prop`s of `Mirrors/Sorting.lean` as THEOREMS, each proved
by `mirror_transport%` from a catalogued waypoint native — i.e. BY
REPLAYING the ACL2 book theorem. The generated crossing is the sole
entry point of each product's content, and the mirror seam gate
(`MirrorProofs/SeamGate.lean`) checks at build time that every
product's proof term reaches a `driver_replayed%` statement.

This page carries only the PRODUCTS. The METRIC-side machinery — the
definitional-correspondence squares the transports consume, and each
definition's frontier where a square does not exist — lives in
`MirrorProofs/SortingSquares.lean` and its perm/qsort/bsort siblings.

## THE SCOREBOARD — FIFTEEN OF FIFTEEN

The spec's `Prop`s stand in a bijection with the sorting corpus's
result-tier theorems (the invariant is stated in
`Mirrors/Sorting.lean`'s header; its record is
`docs/notes/2026-08-18_sorting-spec-reshape.md`). All fifteen are
theorems on this page — fourteen at `Int`, and `permWitness_complete`
at `Option Int`, for a reason that is kernel-checked below
(`conditional_elem_square_false`):

| `Prop` | product |
|---|---|
| `isort_ordered` | `isort_ordered_int` |
| `isort_howMany` | `isort_howMany_int` |
| `msort_ordered` | `msort_ordered_int` |
| `msort_howMany` | `msort_howMany_int` |
| `qsort_ordered` | `qsort_ordered_int` |
| `qsort_howMany` | `qsort_howMany_int` |
| `qsort_perm` | `qsort_perm_int` |
| `ordered_perm_unique` | `ordered_perm_unique_int` |
| `permuted_equivalence` | `permuted_equivalence_int` |
| `bsort_ordered` | `bsort_ordered_int` |
| `bsort_howMany` | `bsort_howMany_int` |
| `msort_is_isort` | `msort_is_isort_int` |
| `qsort_is_isort` | `qsort_is_isort_int` |
| `bsort_is_isort` | `bsort_is_isort_int` |
| `permWitness_complete` | `permWitness_complete_optint` (at `Option Int`) |

The buildout history — the wave-by-wave frontiers as they stood, the
measurements behind each machinery decision, and the spec reshape that
fixed the bijection — is in the record docs, not here:
`docs/plans/2026-08-17_r4-wave2-charter.md` (ARC LOG),
`docs/plans/2026-08-18_close-out-arc-charter.md`, and the reshape note
above. -/

namespace ACL2Lean.MirrorProofs

open ACL2 ACL2Lean

/-- **`isort_ordered` at `Int`, via ACL2 replay** — INSERTION SORT
    SORTS (the book's ORDEREDP-ISORT). Content enters through the
    generated crossing `isort_ordered_sexpr`, which cites the
    catalogued ORDEREDP-ISORT native exactly, and nowhere else. -/
mirror_transport% isort_ordered_int : ACL2Lean.Sorting.isort_ordered Int
  embed intOrderedEmbed
  crossing isort_ordered_sexpr
    from ACL2.Imported.Waypoints.orderedp_isort_native_driver

/-- info: 'ACL2Lean.MirrorProofs.isort_ordered_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isort_ordered_int

/-- **`msort_ordered` at `Int`, via ACL2 replay** — MERGE SORT SORTS
    (the book's ORDEREDP-MSORT). Content enters through the generated
    crossing `msort_ordered_sexpr`, which cites the catalogued
    ORDEREDP-MSORT native exactly, and nowhere else. -/
mirror_transport% msort_ordered_int : ACL2Lean.Sorting.msort_ordered Int
  embed intOrderedEmbed
  crossing msort_ordered_sexpr
    from ACL2.Imported.Waypoints.orderedp_msort_native_driver

/-- info: 'ACL2Lean.MirrorProofs.msort_ordered_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms msort_ordered_int

/-- **`ordered_perm_unique` at `Int`, via ACL2 replay** — AN ORDERED
    PERMUTATION IS UNIQUE (the book's ORDERED-PERMS). Content enters
    through the generated crossing `ordered_perm_unique_sexpr`, which
    cites the ORDERED-PERMS native's decode corollary exactly, and
    nowhere else. -/
mirror_transport% ordered_perm_unique_int :
    ACL2Lean.Sorting.ordered_perm_unique Int
  embed intOrderedEmbed
  crossing ordered_perm_unique_sexpr
    from ACL2.Imported.Waypoints.ordered_perms_iff_driver

/-- info: 'ACL2Lean.MirrorProofs.ordered_perm_unique_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ordered_perm_unique_int

/-- **`qsort_ordered` at `Int`, via ACL2 replay** — QUICKSORT SORTS
    (the book's ORDEREDP-QSORT). Content enters through the generated
    crossing `qsort_ordered_sexpr`, which cites the catalogued
    ORDEREDP-QSORT native (at the depth-1 reading) exactly, and
    nowhere else. -/
mirror_transport% qsort_ordered_int : ACL2Lean.Sorting.qsort_ordered Int
  embed intOrderedEmbed
  crossing qsort_ordered_sexpr
    from ACL2.Imported.Waypoints.orderedp_qsort_own_driver

/-- info: 'ACL2Lean.MirrorProofs.qsort_ordered_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qsort_ordered_int

/-- **`qsort_perm` at `Int`, via ACL2 replay** — QUICKSORT PERMUTES
    (the book's PERM-QSORT). Content enters through the generated
    crossing `qsort_perm_sexpr`, which cites the catalogued PERM-QSORT
    native (at the depth-1 reading) exactly, and nowhere else. -/
mirror_transport% qsort_perm_int : ACL2Lean.Sorting.qsort_perm Int
  embed intOrderedEmbed
  crossing qsort_perm_sexpr
    from ACL2.Imported.Waypoints.perm_qsort_own_driver

/-- info: 'ACL2Lean.MirrorProofs.qsort_perm_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qsort_perm_int

/-- **`isort_howMany` at `Int`, via ACL2 replay** — INSERTION SORT
    PRESERVES MULTIPLICITY (the book's HOW-MANY-ISORT). Content enters
    through the generated crossing `isort_howMany_sexpr`, which cites
    the catalogued HOW-MANY-ISORT native exactly, and nowhere else. -/
mirror_transport% isort_howMany_int : ACL2Lean.Sorting.isort_howMany Int
  embed intOrderedEmbed
  crossing isort_howMany_sexpr
    from ACL2.Imported.Waypoints.how_many_isort_native_driver

/-- info: 'ACL2Lean.MirrorProofs.isort_howMany_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isort_howMany_int

/-- **`msort_howMany` at `Int`, via ACL2 replay** — MERGE SORT PRESERVES
    MULTIPLICITY (the book's HOW-MANY-MSORT). Content enters through the
    generated crossing `msort_howMany_sexpr`, which cites the catalogued
    HOW-MANY-MSORT native exactly, and nowhere else. -/
mirror_transport% msort_howMany_int : ACL2Lean.Sorting.msort_howMany Int
  embed intOrderedEmbed
  crossing msort_howMany_sexpr
    from ACL2.Imported.Waypoints.how_many_msort_native_driver

/-- info: 'ACL2Lean.MirrorProofs.msort_howMany_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms msort_howMany_int

/-- **`qsort_howMany` at `Int`, via ACL2 replay** — QUICKSORT PRESERVES
    MULTIPLICITY (the book's HOW-MANY-QSORT). Content enters through the
    generated crossing `qsort_howMany_sexpr`, which cites the catalogued
    HOW-MANY-QSORT native (at the depth-1 reading) exactly, and nowhere
    else. -/
mirror_transport% qsort_howMany_int : ACL2Lean.Sorting.qsort_howMany Int
  embed intOrderedEmbed
  crossing qsort_howMany_sexpr
    from ACL2.Imported.Waypoints.how_many_qsort_own_driver

/-- info: 'ACL2Lean.MirrorProofs.qsort_howMany_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qsort_howMany_int

/-- **`permuted_equivalence` at `Int`, via ACL2 replay** — PERMUTATION
    IS AN EQUIVALENCE RELATION. Content enters through the generated
    crossing `permuted_equivalence_sexpr`, which cites
    `perm_equivalence_permL_driver` — a bundle assembled from THREE
    replayed book theorems, because ACL2's `(defequiv perm)` mints the
    reflexivity conjunct only: `PERM-IS-AN-EQUIVALENCE` for
    reflexivity, and the perm book's `local` `PERM-SYMMETRIC` and
    `PERM-TRANSITIVE` for the other two conjuncts (`local` is a scope
    marker, not a weaker status — all three are ACL2-proved in the
    book, and all three replayed statements are consumed:
    `Imported/Waypoints/PermBook.lean`) — and nothing else. -/
mirror_transport% permuted_equivalence_int :
    ACL2Lean.Sorting.permuted_equivalence Int
  embed intOrderedEmbed
  crossing permuted_equivalence_sexpr
    from ACL2.Imported.Waypoints.perm_equivalence_permL_driver

/-- info: 'ACL2Lean.MirrorProofs.permuted_equivalence_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms permuted_equivalence_int

/-- **`bsort_ordered` at `Int`, via ACL2 replay** — BUBBLE SORT SORTS
    (the book's ORDEREDP-BSORT). Content enters through the generated
    crossing `bsort_ordered_sexpr`, which cites the catalogued
    ORDEREDP-BSORT native exactly, and nowhere else. -/
mirror_transport% bsort_ordered_int : ACL2Lean.Sorting.bsort_ordered Int
  embed intOrderedEmbed
  crossing bsort_ordered_sexpr
    from ACL2.Imported.Waypoints.orderedp_bsort_native_driver

/-- info: 'ACL2Lean.MirrorProofs.bsort_ordered_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bsort_ordered_int

/-- **`bsort_howMany` at `Int`, via ACL2 replay** — BUBBLE SORT PRESERVES
    MULTIPLICITY (the book's HOW-MANY-BSORT). Content enters through the
    generated crossing `bsort_howMany_sexpr`, which cites the catalogued
    HOW-MANY-BSORT native exactly, and nowhere else. -/
mirror_transport% bsort_howMany_int : ACL2Lean.Sorting.bsort_howMany Int
  embed intOrderedEmbed
  crossing bsort_howMany_sexpr
    from ACL2.Imported.Waypoints.how_many_bsort_native_driver

/-- info: 'ACL2Lean.MirrorProofs.bsort_howMany_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bsort_howMany_int

/-- **`msort_is_isort` at `Int`, via ACL2 replay** — MERGE SORT AND
    INSERTION SORT AGREE (the sorts-equivalent book's MSORT-IS-ISORT,
    a `:functional-instance` of the equisort capstone). Content enters
    through the generated crossing `msort_is_isort_sexpr`, which cites
    the catalogued MSORT-IS-ISORT native exactly, and nowhere else. -/
mirror_transport% msort_is_isort_int : ACL2Lean.Sorting.msort_is_isort Int
  embed intOrderedEmbed
  crossing msort_is_isort_sexpr
    from ACL2.Imported.Waypoints.msort_is_isort_native_driver

/-- info: 'ACL2Lean.MirrorProofs.msort_is_isort_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms msort_is_isort_int

/-- **`qsort_is_isort` at `Int`, via ACL2 replay** — QUICKSORT AND
    INSERTION SORT AGREE (the sorts-equivalent book's QSORT-IS-ISORT).
    Content enters through the generated crossing
    `qsort_is_isort_sexpr`, which cites the catalogued QSORT-IS-ISORT
    native (at the depth-1 reading) exactly, and nowhere else. -/
mirror_transport% qsort_is_isort_int : ACL2Lean.Sorting.qsort_is_isort Int
  embed intOrderedEmbed
  crossing qsort_is_isort_sexpr
    from ACL2.Imported.Waypoints.qsort_is_isort_native_driver

/-- info: 'ACL2Lean.MirrorProofs.qsort_is_isort_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qsort_is_isort_int

/-- **`bsort_is_isort` at `Int`, via ACL2 replay** — BUBBLE SORT AND
    INSERTION SORT AGREE (the sorts-equivalent book's BSORT-IS-ISORT;
    the corpus's one CONDITIONAL capstone — its `TRUE-LISTP` hypothesis
    is type-absorbed at the decode by the generic IMPLIES peel).
    Content enters through the generated crossing
    `bsort_is_isort_sexpr`, which cites the catalogued BSORT-IS-ISORT
    native exactly, and nowhere else. -/
mirror_transport% bsort_is_isort_int : ACL2Lean.Sorting.bsort_is_isort Int
  embed intOrderedEmbed
  crossing bsort_is_isort_sexpr
    from ACL2.Imported.Waypoints.bsort_is_isort_native_driver

/-- info: 'ACL2Lean.MirrorProofs.bsort_is_isort_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bsort_is_isort_int

/-- **`permWitness_complete` at `Option Int`, via ACL2 replay** — THE
    COUNTEREXAMPLE WITNESS IS COMPLETE: two lists are permutations
    exactly when their multiplicities agree at the ONE element the
    witness picks out (the book's CONVERT-PERM-TO-HOW-MANY). Content
    enters through the generated crossing `permWitness_complete_sexpr`,
    which cites the catalogued CONVERT-PERM-TO-HOW-MANY native (at its
    `Iff` decode) exactly, and nowhere else.

    **Why this product lives at `Option Int` and not `Int`.** The
    witness is a TOTAL Lean rendering of an untyped ACL2 function, so
    it has a fallback arm: at `xs = ys = []` it returns
    `Inhabited.default` where ACL2's `PERM-COUNTER-EXAMPLE` returns
    `(CAR NIL)` = `nil`. The homomorphism square that carries the
    witness across the encoding is therefore true exactly when the
    embedding can hit that fallback — `e.enc default = default` — which
    `intEmbed` PROVABLY cannot (its image is an integer atom, never
    `nil`): that is kernel-refuted by the live theorem
    `conditional_elem_square_false` below, and is the REASON for the
    element type, not an obstacle worked around. `Option Int` is the
    type at which ACL2's junk value is a VALUE of the Lean type rather
    than an invented one: `Option`'s `default` is `none`, which the
    generic `Option` row of the embedding calculus (`IsoKit.lean`'s
    `optEmbed` — Lean's `Option` as ACL2's value-or-nil idiom) sends to
    `nil`, discharging the square's hypothesis for every element type
    the row applies to. The `Prop` transported is the book's, unchanged
    and unconditional. Record:
    `docs/plans/2026-08-18_close-out-arc-charter.md`, item 2. -/
mirror_transport% permWitness_complete_optint :
    ACL2Lean.Sorting.permWitness_complete (Option Int)
  embed optIntEmbed
  crossing permWitness_complete_sexpr
    from ACL2.Imported.Waypoints.convert_perm_to_how_many_iff_driver

/-- info: 'ACL2Lean.MirrorProofs.permWitness_complete_optint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms permWitness_complete_optint

/-- **THE ELEMENT-RESULT SQUARE IS FALSE AT `Int`** — the kernel-checked
    refutation `permWitness_complete_optint`'s docstring cites, and the
    reason that product lives at `Option Int`.

    The counterexample is `xs = ys = [1]`: a permuting pair, so the
    witness walk bottoms out at `permWitness [] []` and both sides
    return their own type's junk value — `(0 : Int)` on the mirror
    side, `nil` on the encoded side — and `intOrderedEmbed.enc 0` is an
    integer ATOM, never `nil`. The failure is structural, not a
    boundary case: the walk reaches the fallback arm on the ENTIRE
    `Permuted` half, so no precondition that leaves the theorem's
    content intact can make the square true (the full record is the R4
    wave-2 charter's ARC LOG, J-2e-6). The statement carries the
    precondition `(xs ≠ [] ∨ ys ≠ [])`, which the counterexample
    satisfies, so it refutes the unconditional square a fortiori.

    (The statement mentions `intOrderedEmbed`, so the mirror seam
    gate's mechanical product criterion correctly does not count it as
    a product: it is a refutation about the encoding, not a mirror.) -/
theorem conditional_elem_square_false :
    ¬ (∀ (xs ys : List Int), (xs ≠ [] ∨ ys ≠ []) →
        Sorting.permWitness (List.map intOrderedEmbed.enc xs)
            (List.map intOrderedEmbed.enc ys)
          = intOrderedEmbed.enc (Sorting.permWitness xs ys)) := by
  intro h
  have hc := h [1] [1] (Or.inl (by simp))
  exact absurd hc (by decide)

/-- info: 'ACL2Lean.MirrorProofs.conditional_elem_square_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms conditional_elem_square_false

end ACL2Lean.MirrorProofs
