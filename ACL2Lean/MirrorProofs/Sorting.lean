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

/-! # MIRROR PROOFS — the sorting book's PRODUCTS (R4 wave 2c)

The sorting mirrors themselves. `MirrorProofs/SortingSquares.lean` — the
witness page this file was split out of when it crossed the module-size
norm — carries the METRIC's machinery (the twenty-six squares:
definitional correspondence about our own definitions, and every
definition's frontier where a square does not exist). THIS page carries
the PRODUCT: `Mirrors/Sorting.lean`'s target `Prop`s as THEOREMS, each
proved by `mirror_transport%` from a CATALOGUED waypoint native, i.e. BY
REPLAYING the ACL2 book theorem (canon line 4). The generated crossing
is the sole entry point of the content, and the mirror seam gate
(`MirrorProofs/SeamGate.lean`) checks mechanically that each product's
proof term reaches a `driver_replayed%` statement.

## THE SCOREBOARD — FIFTEEN OF FIFTEEN

The spec's target `Prop`s stand in a BIJECTION with the sorting
corpus's result-tier theorems since R4 wave 2f (the reshape's permanent
record is `docs/notes/2026-08-18_sorting-spec-reshape.md`; the
invariant itself is stated in `Mirrors/Sorting.lean`'s header; the
close-out arc's item 0 reclassified `sorter_unique` out, 16 → 15 —
reshape Part 8). Against that list of FIFTEEN, ALL FIFTEEN are theorems
on this page — fourteen at `Int`, and `permWitness_complete` at
`Option Int` (the value-or-nil element type; its section explains why
that is the honest type and why the `Int` refutation stands):

| `Prop` | product | wave |
|---|---|---|
| `isort_ordered` | `isort_ordered_int` | 2c |
| `isort_howMany` | `isort_howMany_int` | 2f |
| `msort_ordered` | `msort_ordered_int` | 2c |
| `msort_howMany` | `msort_howMany_int` | 2f |
| `qsort_ordered` | `qsort_ordered_int` | 2e |
| `qsort_howMany` | `qsort_howMany_int` | 2f |
| `qsort_perm` | `qsort_perm_int` | 2e |
| `ordered_perm_unique` | `ordered_perm_unique_int` | 2d, re-landed as the `Iff` in 2f |
| `permuted_equivalence` | `permuted_equivalence_int` | 2f |
| `bsort_ordered` | `bsort_ordered_int` | 2g |
| `bsort_howMany` | `bsort_howMany_int` | 2g |
| `msort_is_isort` | `msort_is_isort_int` | 2g |
| `qsort_is_isort` | `qsort_is_isort_int` | 2g |
| `bsort_is_isort` | `bsort_is_isort_int` | close-out arc |
| `permWitness_complete` | `permWitness_complete_optint` (at `Option Int` — the VALUE-OR-NIL element type; see the witness-product section) | close-out item 2 |

**ALL FIFTEEN `Prop`s ARE THEOREMS.** The section that stood here for
two waves ("the ones that are not, with their real distance and no
euphemism") is retired empty: `bsort_is_isort` landed when the usefi
pre-pass's cached-conds bug was fixed (close-out J-1-2 — the golden was
byte-identical throughout; the assumed-dp-fact reading was a scoreboard
misread, J-1-1), `permWitness_complete` landed at its honest element
type (the witness-product section below carries why `Option Int` and
why the `Int` refutation STANDS), and `sorter_unique` was reclassified
out of the spec (reshape Part 8 — an exported instantiation device,
represented by the three `*_is_isort` instance products).

**WHAT THE FIRST TRANSPORT COST IN MACHINERY: NOTHING.** The charter
predicted a machinery gap here — `mirror_transport%`'s binder check is
`List SExpr`-only and the deferred F3 instance THREADING was to be built
against these consumers. Measured, and reported rather than assumed:
`isort_ordered`'s only binder IS a `List`, and its `[TotalOrder α]`
binder needs no threading at all, because the generator states the
crossing at `SExpr` and the mirror at the user's type and lets ORDINARY
INSTANCE SYNTHESIS find `instTotalOrderSExpr` / `instTotalOrderInt` at
each end. So no threading was built: building it here would have been
the banned "infrastructure now, wire it later", and the honest record is
that the first real consumer did not demand it. (The binder check's
ELEMENT frontier stood until R4 wave 2f, whose multiplicity `Prop`s are
its first consumers; it cost ONE table row, and the instance threading
is STILL not built, because still nothing demands it.)

## THE FIRST SORTING PRODUCT — `isort_ordered` at `Int`

The book's ORDEREDP-ISORT. Three registered squares carry it and would
each fail closed if missing: `isort_agree_isortL` and
`ordered_agree_orderedpRec` (W5/W11 — the crossing's vocabulary), then
`isort_map_hom` backwards and `ordered_map_invariant` forwards (W5/W11 —
the transport's normalisation). The embedding is `intOrderedEmbed`
(`OrderBridge`), whose `ord` field is PROVED by `lexorderB_intEmbed`, so
the `Int` mirror carries no extra hypothesis — which is exactly what the
charter's wave-2c line predicted. -/

namespace ACL2Lean.MirrorProofs

open ACL2 ACL2Lean

/-- **`isort_ordered` at `Int`, via ACL2 replay** — the FIRST sorting
    mirror, and the first product whose content is a sorting book
    theorem. Content enters through the generated crossing
    `isort_ordered_sexpr`, which cites
    `orderedp_isort_native_driver` (the catalogued ORDEREDP-ISORT
    native, `sorting/isort`) exactly, and nowhere else. -/
mirror_transport% isort_ordered_int : ACL2Lean.Sorting.isort_ordered Int
  embed intOrderedEmbed
  crossing isort_ordered_sexpr
    from ACL2.Imported.Waypoints.orderedp_isort_native_driver

/-- info: 'ACL2Lean.MirrorProofs.isort_ordered_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isort_ordered_int

/-! ## THE SECOND SORTING PRODUCT — `msort_ordered` at `Int`

The charter's wave-2c pair was `isort_ordered` + `isort_perm`. The second
of those CANNOT LAND (the record is below: there is no PERM-ISORT
theorem in the book at all), so the second product is taken from the
long tail instead — `msort_ordered`, the book's ORDEREDP-MSORT — because
it costs exactly the three transport lines and needs no new machinery:
`msort`'s two squares are wave 2a's, `Ordered`'s two are W11's (one of
them landed above), and the waypoint is catalogued
(`sorting/msort`, `orderedp_msort_native_driver`). -/

/-- **`msort_ordered` at `Int`, via ACL2 replay** — the second sorting
    mirror. Content enters through the generated crossing
    `msort_ordered_sexpr`, which cites the catalogued ORDEREDP-MSORT
    native exactly, and nowhere else. -/
mirror_transport% msort_ordered_int : ACL2Lean.Sorting.msort_ordered Int
  embed intOrderedEmbed
  crossing msort_ordered_sexpr
    from ACL2.Imported.Waypoints.orderedp_msort_native_driver

/-- info: 'ACL2Lean.MirrorProofs.msort_ordered_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms msort_ordered_int

/-! ## THE THIRD SORTING PRODUCT — `ordered_perm_unique` at `Int`

The book's ORDERED-PERMS, and the first product whose spec `Prop`
CARRIES HYPOTHESES (`∀ xs ys, Ordered xs → Ordered ys → Permuted xs ys →
xs = ys`). Two things had to arrive for it, and both are recorded where
they live rather than summarised away:

* the `Permuted` AGREE square (`SortingPermSquares`, R4 wave 2d), which
  is what carries the third hypothesis into the reading's vocabulary. It
  needed the `rm` agree square, which needed the OWN-DEFINITION `rmL`
  reading — the compliance conversion of wave 2d item 1;
* `mirror_transport%`'s HYPOTHESIS-CARRYING rung (`TransportGen`, item
  5): the binder walk now admits DATA-THEN-HYPOTHESES, the crossing
  rewrites the hypotheses as well as the goal with the same fixed
  agreement-square set, and the mirror rung applies the normalised
  crossing instance to the mirror's own hypotheses. The hypothesis-free
  path is a separate branch and is byte-identical to what it was.

The waypoint cited is `ordered_perms_eq_driver`, a DECODE-SHAPE
corollary of the catalogued ORDERED-PERMS native
(`ordered_perms_native_driver`, `(xs == ys) = permL xs ys` under the two
sortedness hypotheses) — the same class as that native's existing
`List.Perm` corollary, carrying no content of its own: the content is
the replay's, and the seam gate checks that the product's proof term
reaches `orderedPermsCapReplayedCond`. -/

/-- **`ordered_perm_unique` at `Int`, via ACL2 replay** — an ordered
    permutation is unique. Content enters through the generated crossing
    `ordered_perm_unique_sexpr`, which cites the ORDERED-PERMS native's
    decode corollary exactly, and nowhere else. -/
mirror_transport% ordered_perm_unique_int :
    ACL2Lean.Sorting.ordered_perm_unique Int
  embed intOrderedEmbed
  crossing ordered_perm_unique_sexpr
    from ACL2.Imported.Waypoints.ordered_perms_iff_driver

/-- info: 'ACL2Lean.MirrorProofs.ordered_perm_unique_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ordered_perm_unique_int

/-! ## THE FOURTH AND FIFTH SORTING PRODUCTS — `qsort_ordered` and
`qsort_perm` at `Int` (R4 wave 2e)

The book's ORDEREDP-QSORT and PERM-QSORT. Wave 2d left BOTH one
orchestrator decision away, and named exactly what was missing: a place
for the instance-canonicalisation fact that makes the four per-mode
`filterRel` agree squares FIRE inside `qsort`'s closer (J-2b-4). O-7
(2026-08-18) ruled it — the `instances [...]` clause on a square
declaration — and the square landed on the first attempt with no other
change: the ladder is untouched this wave and no new capability was
added. The record is `MirrorProofs/SortingQsortSquares.lean`; the
reading's own validation bound is
`Imported/SortingQsortReading.lean`'s header.

The waypoints cited are the two catalogued qsort natives read at the
depth-1 reading (`orderedp_qsort_own_driver`,
`perm_qsort_own_driver` — decode-shape corollaries in the class
`ordered_perms_eq_driver` established, carrying no content of their
own), and the seam gate checks that each product's proof term reaches
`orderedpQsortReplayedCond` / `permQsortReplayedCond`. -/

/-- **`qsort_ordered` at `Int`, via ACL2 replay** — QUICKSORT SORTS.
    Content enters through the generated crossing `qsort_ordered_sexpr`,
    which cites the catalogued ORDEREDP-QSORT native (at the depth-1
    reading) exactly, and nowhere else. -/
mirror_transport% qsort_ordered_int : ACL2Lean.Sorting.qsort_ordered Int
  embed intOrderedEmbed
  crossing qsort_ordered_sexpr
    from ACL2.Imported.Waypoints.orderedp_qsort_own_driver

/-- info: 'ACL2Lean.MirrorProofs.qsort_ordered_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qsort_ordered_int

/-- **`qsort_perm` at `Int`, via ACL2 replay** — QUICKSORT PERMUTES, and
    the FIRST perm-shaped sorting product. Content enters through the
    generated crossing `qsort_perm_sexpr`, which cites the catalogued
    PERM-QSORT native (at the depth-1 reading) exactly, and nowhere
    else. -/
mirror_transport% qsort_perm_int : ACL2Lean.Sorting.qsort_perm Int
  embed intOrderedEmbed
  crossing qsort_perm_sexpr
    from ACL2.Imported.Waypoints.perm_qsort_own_driver

/-- info: 'ACL2Lean.MirrorProofs.qsort_perm_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qsort_perm_int

/-! ## THE MULTIPLICITY PRODUCTS — `isort_howMany`, `msort_howMany` and
`qsort_howMany` at `Int` (R4 wave 2f)

The books' HOW-MANY-ISORT, HOW-MANY-MSORT and HOW-MANY-QSORT: each sort
leaves the count of every element unchanged. These are the corpus's own
statement of "the sort permutes" — the form the sorting books actually
prove — and the spec `Prop`s were reshaped to it in this wave.

WHAT THEY COST IN MACHINERY: ONE ROW of the transport's binder table.
Each `Prop` binds an ELEMENT (`∀ (a : α) (xs : List α)`), which the
binder walk previously hard-errored on ("neither a `List SExpr`
argument nor a HYPOTHESIS"), and that error was the charter's predicted
element-binder frontier. The row is the smallest thing that clears it:
a scalar `SExpr` binder is encoded by `e.enc a` where a list binder is
encoded by `List.map e.enc`, and the crossing instance is taken at
`e.enc a`. Nothing else moved — `howMany_map_invariant` (a SCALAR
homomorphism square, live since wave 2a) is what deletes the encoding
again on the mirror rung, and the closers are untouched. The row is
fail-closed on the hypothesis-carrying path (a scalar binder in a spec
that also carries hypotheses is a named frontier, pinned as a negative
test in `Tests/IsoGenGateTests.lean`). -/

/-- **`isort_howMany` at `Int`, via ACL2 replay** — INSERTION SORT
    PRESERVES MULTIPLICITY. Content enters through the generated
    crossing `isort_howMany_sexpr`, which cites the catalogued
    HOW-MANY-ISORT native exactly, and nowhere else. -/
mirror_transport% isort_howMany_int : ACL2Lean.Sorting.isort_howMany Int
  embed intOrderedEmbed
  crossing isort_howMany_sexpr
    from ACL2.Imported.Waypoints.how_many_isort_native_driver

/-- info: 'ACL2Lean.MirrorProofs.isort_howMany_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isort_howMany_int

/-- **`msort_howMany` at `Int`, via ACL2 replay** — MERGE SORT PRESERVES
    MULTIPLICITY. Content enters through the generated crossing
    `msort_howMany_sexpr`, which cites the catalogued HOW-MANY-MSORT
    native exactly, and nowhere else. -/
mirror_transport% msort_howMany_int : ACL2Lean.Sorting.msort_howMany Int
  embed intOrderedEmbed
  crossing msort_howMany_sexpr
    from ACL2.Imported.Waypoints.how_many_msort_native_driver

/-- info: 'ACL2Lean.MirrorProofs.msort_howMany_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms msort_howMany_int

/-- **`qsort_howMany` at `Int`, via ACL2 replay** — QUICKSORT PRESERVES
    MULTIPLICITY. Content enters through the generated crossing
    `qsort_howMany_sexpr`, which cites the catalogued HOW-MANY-QSORT
    native (at the depth-1 reading) exactly, and nowhere else. -/
mirror_transport% qsort_howMany_int : ACL2Lean.Sorting.qsort_howMany Int
  embed intOrderedEmbed
  crossing qsort_howMany_sexpr
    from ACL2.Imported.Waypoints.how_many_qsort_own_driver

/-- info: 'ACL2Lean.MirrorProofs.qsort_howMany_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qsort_howMany_int

/-! ## `permuted_equivalence` at `Int` (R4 wave 2f)

The perm book's PERM-IS-AN-EQUIVALENCE — ACL2's `defequiv` content, and
the first product whose spec `Prop` is a CONJUNCTION rather than a
single equation or `Iff`. It needed nothing new: the binder walk already
admits three list binders, and the body check only refuses a nested
`∀`, so the conjunction passes through as the equation-position body it
is. The waypoint cited is `perm_equivalence_permL_driver`, the bundle
re-spelled in the own-definition `permL` vocabulary (the decode class
`ordered_perms_eq_driver` established), and the seam gate checks that
the product's proof term reaches `permEquivReplayed`. -/

/-- **`permuted_equivalence` at `Int`, via ACL2 replay** — permutation
    is an equivalence relation. Content enters through the generated
    crossing `permuted_equivalence_sexpr`, which cites the catalogued
    PERM-IS-AN-EQUIVALENCE native's bundle exactly, and nowhere else. -/
mirror_transport% permuted_equivalence_int :
    ACL2Lean.Sorting.permuted_equivalence Int
  embed intOrderedEmbed
  crossing permuted_equivalence_sexpr
    from ACL2.Imported.Waypoints.perm_equivalence_permL_driver

/-- info: 'ACL2Lean.MirrorProofs.permuted_equivalence_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms permuted_equivalence_int


/-! ## THE BSORT PRODUCTS — `bsort_ordered` and `bsort_howMany` at `Int`
(R4 wave 2g)

The book's ORDEREDP-BSORT and HOW-MANY-BSORT — the last two of the
sorting corpus's four sorts to arrive, and the only pair that needed
machinery on BOTH sides of the seam:

* the WAYPOINT side had no BSORT exec kit at all, because `BSORT` is the
  corpus's only `userFn`-MEASURED defun (`(BNEXT-SIZE X)`); the kit is
  now GENERATED by `derive_exec%`'s new measure row
  (`Imported/ExecGen.lean`, `Imported/SortingBsortKit.lean`);
* the MIRROR side's two squares looped the closer on the spec's own
  fixpoint equation; the FIXPOINT-GUARD capability
  (`MirrorProofs/IsoKit.lean`) closes that, and both squares are LIVE
  (`MirrorProofs/SortingBsortSquares.lean`).

Neither product needed a decode corollary or a transport-table row: the
two natives are stated in exactly the shapes `msort_ordered` and
`msort_howMany` transport through. -/

/-- **`bsort_ordered` at `Int`, via ACL2 replay** — BUBBLE SORT SORTS.
    Content enters through the generated crossing `bsort_ordered_sexpr`,
    which cites the catalogued ORDEREDP-BSORT native exactly, and
    nowhere else. -/
mirror_transport% bsort_ordered_int : ACL2Lean.Sorting.bsort_ordered Int
  embed intOrderedEmbed
  crossing bsort_ordered_sexpr
    from ACL2.Imported.Waypoints.orderedp_bsort_native_driver

/-- info: 'ACL2Lean.MirrorProofs.bsort_ordered_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bsort_ordered_int

/-- **`bsort_howMany` at `Int`, via ACL2 replay** — BUBBLE SORT PRESERVES
    MULTIPLICITY. Content enters through the generated crossing
    `bsort_howMany_sexpr`, which cites the catalogued HOW-MANY-BSORT
    native exactly, and nowhere else. -/
mirror_transport% bsort_howMany_int : ACL2Lean.Sorting.bsort_howMany Int
  embed intOrderedEmbed
  crossing bsort_howMany_sexpr
    from ACL2.Imported.Waypoints.how_many_bsort_native_driver

/-- info: 'ACL2Lean.MirrorProofs.bsort_howMany_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bsort_howMany_int


/-! ## THE AGREEMENT PRODUCTS — `msort_is_isort` and `qsort_is_isort` at
`Int` (R4 wave 2g)

The sorts-equivalent book's capstones: the corpus's own statement that
the sorts compute the same list. Wave 2f recorded these as blocked on
"`sorting/sorts-equivalent` has NO waypoint module at all". That is
true and was not the whole cause, and the correction is on the record:
`driver_replayed%` had NO ROUTE to a `:USE (:FUNCTIONAL-INSTANCE …)`
proof — the discharge existed only as a `runBook` parameter the
coverage sweep supplies — so these rows were replayable by the SWEEP
and by nothing else, and no waypoint module could have been written.
The macro's `usefi` clause (`Imported/Waypoints/Macro.lean`) is that
route at the waypoint layer.

Neither product needed anything on THIS page: the squares they consume
(`msort`/`qsort`/`isort` agree + hom) have been live since waves 2a-2e,
and `mirror_transport%`'s list-equation landing is the `map_inj_iff`
alternative wave 2f added. `bsort_is_isort` is NOT here — see the
frontier section below; its cause is not machinery. -/

/-- **`msort_is_isort` at `Int`, via ACL2 replay** — MERGE SORT AND
    INSERTION SORT AGREE. Content enters through the generated crossing
    `msort_is_isort_sexpr`, which cites the catalogued MSORT-IS-ISORT
    native exactly, and nowhere else. -/
mirror_transport% msort_is_isort_int : ACL2Lean.Sorting.msort_is_isort Int
  embed intOrderedEmbed
  crossing msort_is_isort_sexpr
    from ACL2.Imported.Waypoints.msort_is_isort_native_driver

/-- info: 'ACL2Lean.MirrorProofs.msort_is_isort_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms msort_is_isort_int

/-- **`qsort_is_isort` at `Int`, via ACL2 replay** — QUICKSORT AND
    INSERTION SORT AGREE. Content enters through the generated crossing
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
    INSERTION SORT AGREE. The corpus's one CONDITIONAL capstone (the
    book's `TRUE-LISTP` hypothesis, type-absorbed at the decode by the
    generic IMPLIES peel). Content enters through the generated crossing
    `bsort_is_isort_sexpr`, which cites the catalogued BSORT-IS-ISORT
    native exactly, and nowhere else. -/
mirror_transport% bsort_is_isort_int : ACL2Lean.Sorting.bsort_is_isort Int
  embed intOrderedEmbed
  crossing bsort_is_isort_sexpr
    from ACL2.Imported.Waypoints.bsort_is_isort_native_driver

/-- info: 'ACL2Lean.MirrorProofs.bsort_is_isort_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bsort_is_isort_int

/-! ## THE WITNESS PRODUCT — `permWitness_complete` at the VALUE-OR-NIL
element type (close-out arc item 2, 2026-08-18)

The `Prop` this page recorded as STRUCTURALLY UNAVAILABLE, and what
changed. The blocker (wave 2d item 4, wave 2e's J-2e-6, and re-measured
at wave 2f — the record is kept below, verbatim) was the ELEMENT-RESULT
homomorphism square `e.enc (permWitness xs ys) = permWitness (map e.enc
xs) (map e.enc ys)`, whose whole residual is the JUNK ARM: at
`xs = ys = []` the spec must invent a value and ACL2 has `(car nil)` =
`nil`. The page named the two routes that remained and classified the
first as "a spec/type question": **AN EMBEDDING WHOSE `default` IS IN
RANGE — the square becomes true for any embedding with
`e.enc default = default`, which no embedding of `Int` can satisfy but
a type with a nil-like default could.**

That is the route taken, and it is taken GENERICALLY rather than for
this theorem: `Option α` is Lean's rendering of ACL2's value-or-nil
return idiom (`MEMBER`, `ASSOC`, `PERM-COUNTER-EXAMPLE` — the shape
`(car nil)` exists to serve), and the `Option` ROW of the data-
refinement calculus (`IsoKit.lean`'s `optEmbed`) builds an embedding of
`Option α` from one of `α` under a single fail-closed side condition
(the underlying encoding avoids `nil`, without which the map is not
injective and the row does not construct). `Option`'s own `default` IS
`none`, which the row sends to `nil` — so `e.enc default = default`
holds BY THE ROW, and the square's hypothesis is discharged for every
element type the row applies to, not arranged for this one.

So the product below is at `Option Int` — the value-or-nil element type
— and NOT at `Int`. That is not a weakening dressed up: at `Int` the
square is REFUTED (the kernel-checked refutation is kept below), and
`Option Int` is the type at which ACL2's junk value is a value of the
Lean type rather than an invented one. The `Prop` transported is the
book's, unchanged and unconditional.

WHAT THE ROW DOES NOT REACH, on the record. The other rendering — a
spec whose WITNESS IS `Option α`-VALUED, with the junk arm and the
`[Inhabited α]` binder eliminated — does not go through, and the reason
is the row's own side condition one level up: a `mirror_transport%`
CROSSING is stated at `SExpr`, where the value-or-nil refinement
`Option SExpr → SExpr` is NOT injective (`none` and `some nil` have the
same image). An `Option`-valued mirror function therefore distinguishes
cases the ACL2 function conflates, and no book theorem can supply the
difference: the crossing's `none` arm would need "the walk names no
witness exactly when the lists are permutations", which is nowhere in
the corpus's 75 `(:DEFTHM …)` rows and would have to be a Lean-side
induction. Measured, not argued — see the arc's report. -/

/-- **`permWitness_complete` at `Option Int`, via ACL2 replay** — THE
    COUNTEREXAMPLE WITNESS IS COMPLETE: two lists are permutations
    exactly when their multiplicities agree at the ONE element the
    witness picks out. Content enters through the generated crossing
    `permWitness_complete_sexpr`, which cites the catalogued
    CONVERT-PERM-TO-HOW-MANY native (at its `Iff` decode) exactly, and
    nowhere else.

    **WHY THIS PRODUCT LIVES AT `Option Int`** (Mike's ruling of
    2026-08-18, approving it as THE product for this `Prop`). The
    witness is a TOTAL Lean rendering of an untyped ACL2 function, so it
    has a FALLBACK arm: at `xs = ys = []` it returns `Inhabited.default`
    where ACL2's `PERM-COUNTER-EXAMPLE` returns `(CAR NIL)` = `nil`. The
    element-result homomorphism square that carries the witness across
    the encoding is therefore true EXACTLY WHEN THE EMBEDDING CAN HIT
    THAT FALLBACK — when `e.enc default = default`, i.e. `nil`.

    `intEmbed` PROVABLY CANNOT: its image is `.atom (.number (.int ·))`
    and never `nil`. That is not an opinion about difficulty — it is
    kernel-refuted by the LIVE THEOREM `conditional_elem_square_false`
    below (first proved in wave 2e; elaborated on this page, with its
    axiom receipt pinned). It stands, and is the REASON for the element
    type, not an obstacle that was worked around.

    `Option Int` is the type at which ACL2's junk value is a VALUE of the
    Lean type rather than an invented one: `Option`'s own `default` is
    `none`, and the `Option` ROW (`IsoKit.lean`'s `optEmbed`) sends
    `none` to `nil`. So the square's hypothesis is discharged BY THE ROW,
    generically, for every element type the row applies to — not arranged
    for this theorem. The `Prop` transported is the book's
    `CONVERT-PERM-TO-HOW-MANY`, unchanged and unconditional. -/
mirror_transport% permWitness_complete_optint :
    ACL2Lean.Sorting.permWitness_complete (Option Int)
  embed optIntEmbed
  crossing permWitness_complete_sexpr
    from ACL2.Imported.Waypoints.convert_perm_to_how_many_iff_driver

/-- info: 'ACL2Lean.MirrorProofs.permWitness_complete_optint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms permWitness_complete_optint

/-! ## R4 WAVE 2f — THE REMAINING FRONTIERS, RE-STATED AGAINST THE
RESHAPED SPEC (each measured this wave; nothing forced)

THE RESHAPE ITSELF is recorded once, in
`docs/notes/2026-08-18_sorting-spec-reshape.md`: the spec's target
`Prop`s were put in a BIJECTION with the corpus's result-tier theorems
(13 `Prop`s → 16), and FIVE of the moved rows landed as products in the
same wave — `isort_howMany`, `msort_howMany`, `qsort_howMany`,
`permuted_equivalence`, and `ordered_perm_unique` re-landed as the
`Iff`. What had been recorded on THIS page across waves 2c–2e as
machinery frontiers (`isort_perm`, `perm_iff_howMany`, `sorts_agree`)
was in each case the spec asking for a statement the books do not make;
those subjects no longer exist, so their records leave this page and
stay in the charter's ARC LOG for waves 2c/2d/2e, which carries them
verbatim. What follows is what is actually left.

**`perm_iff_howMany` IS RETIRED FROM THE SPEC, not solved.** Wave 2e's
finding stands and is the reason: the `→` direction ("a permutation has
equal counts EVERYWHERE") appears in no `(:DEFTHM …)` row of the
corpus, and closing it in Lean would be `List.Perm.count_eq` — the
ornamental-import antipattern. The complete 75-row inventory that
establishes the absence is in the reshape note.

**`permWitness_complete` — [SUPERSEDED by the witness-product section
above; the record is kept verbatim because it is what the close-out
arc's route was chosen against, and because its central refutation
STILL STANDS: there is no `Int` product, and the `Option Int` one exists
BECAUSE the square is false at `Int`.] THE `Prop` IS THE BOOK'S NOW, AND
THE `Int` PRODUCT IS STRUCTURALLY UNAVAILABLE (J-2e-6).** The
precondition wave
2e ruled onto this `Prop` came off in the reshape: `CONVERT-PERM-TO-
HOW-MANY` carries no such hypothesis, and — measured in wave 2e — the
precondition did not do the job it was ruled for either. Both halves of
that measurement are kept here because they are the reason this row is
an honest structural entry rather than a to-do.

RE-MEASURED THIS WAVE against the UNCONDITIONAL `Prop` (wave 2e's
numbers were taken against the preconditioned one, so they are not
carried on trust). The CROSSING CLOSES with no residual, against a
two-line decode corollary of the catalogued CONVERT-PERM-TO-HOW-MANY
native (`permL xs ys = true ↔ howManyL (pceL xs ys) xs = howManyL
(pceL xs ys) ys`, the native modulo `beq_iff_eq`) — declared in the
probe and NOT landed in the tree, because a decode corollary whose only
consumer cannot close is unwired machinery. The MIRROR rung's entire
residual is verbatim, and it is unchanged by the reshape:

```
h has type
  Sorting.Permuted xs ys ↔
    Sorting.howMany (Sorting.permWitness (List.map intOrderedEmbed.enc xs)
        (List.map intOrderedEmbed.enc ys)) (List.map intOrderedEmbed.enc xs) =
      Sorting.howMany (Sorting.permWitness (List.map intOrderedEmbed.enc xs)
        (List.map intOrderedEmbed.enc ys)) (List.map intOrderedEmbed.enc ys)
but is expected to have type
  Sorting.Permuted xs ys ↔
    Sorting.howMany (Sorting.permWitness xs ys) xs =
      Sorting.howMany (Sorting.permWitness xs ys) ys
```

— `permuted_map_invariant` fired (the left side is already the
mirror's), and `howMany_map_invariant` is reported UNUSED, which is the
precise statement of the gap: it cannot fire until the WITNESS ARGUMENT
is `e.enc (permWitness xs ys)`, i.e. until the ELEMENT-RESULT
homomorphism square exists. That square is FALSE, and the refutation is
kernel-checked rather than argued: it is the LIVE THEOREM immediately
below — elaborated on this page, with its axiom receipt pinned — stated
(as in wave 2e, where it was first proved) at a point the then-ruled
precondition ADMITTED, so it refutes the square for the unconditional
`Prop` A FORTIORI. -/

/-- **THE ELEMENT-RESULT SQUARE IS FALSE AT `Int`** — the refutation the
    section above cites, kernel-checked rather than argued, and the
    REASON `permWitness_complete`'s product lives at `Option Int`.

    The counterexample is `xs = ys = [1]`: a permuting pair, so the walk
    bottoms out at `permWitness [] []` and both sides return their own
    type's junk value — `(0 : Int)` on the mirror side, `nil` on the
    encoded side — and `intOrderedEmbed.enc 0` is an integer ATOM, never
    `nil`. Nothing about the difficulty of a proof: the two values are
    distinct and `decide` says so.

    Stated with wave 2e's precondition `(xs ≠ [] ∨ ys ≠ [])` still on it,
    which the counterexample SATISFIES — so this refutes the square for
    the unconditional `Prop` the spec now carries a fortiori. (The
    statement mentions `intOrderedEmbed`, so the mirror seam gate's
    mechanical product criterion correctly does not count it as a
    product: it is a refutation about the encoding, not a mirror.) -/
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

/-! AND THE CHARACTERISATION, which is what makes it structural rather than
a boundary case: `permWitness xs ys` IS the junk value on the ENTIRE
`Permuted` half. The walk consumes `xs`, removing each element from
`ys`; it reaches `permWitness [] []` exactly when every element of `xs`
was found AND `ys` is exhausted — i.e. exactly when `Permuted xs ys`.
Measured: `permWitness [1,2] [2,1] = 0` (= `default`, a permuting pair
of NON-EMPTY lists), against `permWitness [1,2] [2,1,5] = 5` (leftover
head — a real witness) and `permWitness [9] [2] = 9` (not found — a
real witness). So no precondition that leaves the theorem's content
intact can make the square true, and the `Prop` is unharmed on the junk
half (both sides of the `Iff` hold there for ANY witness) — which is
why the theorem is true and the SQUARE is not.

THE TWO ROUTES THAT REMAIN, neither an executor call. (1) AN EMBEDDING
WHOSE `default` IS IN RANGE: the square becomes true for any
`Acl2Embed` with `e.enc default = default` (`SExpr`'s default is
`nil`), which no embedding of `Int` can satisfy but a type with a
nil-like default could — a spec/type question. (2) COMPOSITION: on the
`Permuted` half both sides of the `Iff` hold for any witness, so the
mirror follows from the crossing plus "a permutation has equal counts
everywhere" — the direction the corpus does not prove (above), so this
route is blocked behind an absent book theorem, and its glue is
REASONING besides.

**`msort_is_isort` / `qsort_is_isort` — LANDED IN R4 WAVE 2g; and what
the blocker actually was.** Wave 2f recorded it as "`sorting/sorts-
equivalent` has NO waypoint module at all — no `derive_world`, no
`driver_replayed%` row, nothing", and treated that as a cost estimate
for the corpus's largest book. The absence was real; its CAUSE was one
level down and is corrected here. Each of these theorems is proved in
ACL2 by ONE node — a `:USE (:FUNCTIONAL-INSTANCE …)` of the equisort
scope's constrained-sorter capstone — and `driver_replayed%` had NO
ROUTE to a functional-instance proof at all: the discharge existed only
as a `runBook` parameter the coverage sweep supplies, so these rows were
replayable BY THE SWEEP AND BY NOTHING ELSE, and a waypoint module could
not have been written whatever its size. The `usefi` clause is that
route at this layer (`Imported/Waypoints/Macro.lean`), and with it the
module is 140 lines. `bsort_is_isort` did NOT come with them — see the
scoreboard: its cause is an ASSUMED leaf, not this machinery.

**`bsort_ordered` / `bsort_howMany` — LANDED IN R4 WAVE 2g, and the
frontier this page recorded for them was MIS-ATTRIBUTED.** Waves 2b–2f
recorded the blocker as "the EXEC's termination: `bsortExec` recurses on
`bnextExec x` for an ARBITRARY `SExpr`, where the replayed decrease (an
`enc`-image statement, per the type-absorbed doctrine) does not reach".
The parenthetical is the error, and it is corrected on the record: the
`enc`-image bound belongs to the chosen NATIVE READING, not to the
replay. A replayed statement quantifies over EVERY environment, so
binding `X` to an arbitrary `SExpr` is exactly as available as binding it
to `enc xs` — and stated in the exec's own vocabulary the decrease holds
everywhere (`how_many_bad_pairs_bnext_exec_driver`,
`Imported/Waypoints/Bsort.lean`). With that, `BSORT`'s exec is an
ordinary generated kit and its termination proof is the book's own
admission lemma, arriving by replay.

The kit is GENERIC, not a bsort kit: `derive_exec%` gained the measure
table's `userFn` ROW (`Imported/ExecGen.lean`), which serves any defun
measured by a world function; `BSORT` is its witness. On this page's side
the two squares needed the FIXPOINT-GUARD capability
(`MirrorProofs/IsoKit.lean`) — wave 2d-prep's recorded looping closer —
and both are LIVE in `MirrorProofs/SortingBsortSquares.lean`.

**THE EQUISORT CAPSTONE IS NO LONGER A `Prop` (Mike, 2026-08-18).**
`sorter_unique` was RECLASSIFIED OUT of the spec: the equisort
capstone is an INSTANTIATION DEVICE — stated over the book's
`encapsulate`d constrained sorter symbols and consumed downstream
exclusively via `:functional-instance` — whose Lean-facing content is
fully represented by the three instance products `msort_is_isort`,
`qsort_is_isort` and `bsort_is_isort`. The spec's header carries the
class; the reshape note carries the record, including the binding
pre-check that fired and the re-ruling on the corrected facts. The
reachability question that used to live here went with it: it was a
question about a `Prop` the spec no longer states. -/

end ACL2Lean.MirrorProofs
