import ACL2Lean.MirrorProofs.TransportGen
import ACL2Lean.MirrorProofs.SortingSquares
import ACL2Lean.MirrorProofs.SortingPermSquares
import ACL2Lean.MirrorProofs.SortingQsortSquares
import ACL2Lean.Imported.Waypoints.Isort
import ACL2Lean.Imported.Waypoints.Msort
import ACL2Lean.Imported.Waypoints.OrderedPerms
import ACL2Lean.Imported.Waypoints.PermBook
import ACL2Lean.Imported.Waypoints.Qsort

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

## THE SCOREBOARD — NINE OF THE SIXTEEN, all at `Int`

The spec's target `Prop`s stand in a BIJECTION with the sorting
corpus's result-tier theorems since R4 wave 2f (the reshape's permanent
record is `docs/notes/2026-08-18_sorting-spec-reshape.md`; the
invariant itself is stated in `Mirrors/Sorting.lean`'s header). Against
that list of SIXTEEN, NINE are theorems on this page:

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

The SEVEN that are not, with their real distance and no euphemism:

* `bsort_ordered`, `bsort_howMany` — the waypoint natives do not exist
  (`ORDEREDP-BSORT`, `HOW-MANY-BSORT`) and `bsortL` needs the BSORT
  exec kit. A genuine missing-machinery frontier, measured in wave 2e.
* `msort_is_isort`, `qsort_is_isort`, `bsort_is_isort` — the
  `sorting/sorts-equivalent` book has NO waypoint module at all (no
  `derive_world`, no `driver_replayed%` row), and the third also needs
  the bsort kit. Since wave 2f these are three separate `Prop`s, one
  per book capstone, so none of them waits on the other two and none
  needs a composition mechanism.
* **`permWitness_complete` — THE `Prop` IS CORRECT AND THE PRODUCT IS
  STRUCTURALLY UNAVAILABLE (J-2e-6).** Not a to-do. The mirror rung
  needs the element-result homomorphism square, which is FALSE at the
  junk arm for ANY embedding of `Int` (`SExpr`'s default is `nil`;
  `intEmbed.enc` is never `nil`) — kernel-refuted in wave 2e, at a
  point the then-ruled precondition admitted. The two remaining routes
  are a spec/type question and a theorem the corpus does not prove;
  neither is an executor call.
* **`sorter_unique` — THE `Prop` IS CORRECT AND ITS REACHABILITY IS
  OPEN.** Recorded with the ruling of 2026-08-18: the `Prop` quantifies
  over an ARBITRARY Lean `f : List α → List α`, while a world-parametric
  constant can only be instantiated at the `evalOpt` image of a `World`
  defun, and no construction takes an arbitrary Lean function to an
  ACL2 world. Whether the statement is reachable AS STATED is a design
  question, not a machinery gap.

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

**`permWitness_complete` — THE `Prop` IS THE BOOK'S NOW, AND THE `Int`
PRODUCT IS STRUCTURALLY UNAVAILABLE (J-2e-6).** The precondition wave
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
kernel-checked rather than argued (wave 2e, at a point the then-ruled
precondition ADMITTED — so it refutes the square for the unconditional
`Prop` a fortiori):

```
theorem conditional_elem_square_false :
    ¬ (∀ (xs ys : List Int), (xs ≠ [] ∨ ys ≠ []) →
        Sorting.permWitness (List.map intOrderedEmbed.enc xs)
            (List.map intOrderedEmbed.enc ys)
          = intOrderedEmbed.enc (Sorting.permWitness xs ys)) := by
  intro h; have hc := h [1] [1] (Or.inl (by simp)); exact absurd hc (by decide)
```

AND THE CHARACTERISATION, which is what makes it structural rather than
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

**`msort_is_isort` / `qsort_is_isort` / `bsort_is_isort` — the WAYPOINT
MODULE, and what building it actually costs.** The reshape split
wave-2c's `sorts_agree` into these three, which removes one of the two
blockers outright: each is now ONE book capstone, so none waits on the
other two and none needs a composition mechanism (`mirror_transport%`
cites ONE waypoint exactly, which is exactly what a three-conjunct
`Prop` could not do). The remaining blocker is real and unchanged:

* `MSORT-IS-ISORT` / `QSORT-IS-ISORT` / `BSORT-IS-ISORT` live in
  `sorting/sorts-equivalent`, and **that book has NO waypoint module at
  all** — no `derive_world`, no `driver_replayed%` row, nothing. The
  three natives are not three decode theorems on an existing world;
  they are a new waypoint module for the corpus's largest book, whose
  coverage row already carries eight dependency books
  (`Tests/Coverage/BSsortsEquivalent.lean`).
* `BSORT-IS-ISORT` additionally needs `bsortL` — see the bsort entry
  below.

**`bsort_ordered` / `bsort_howMany` — the natives do not exist, and the
kit's real shape (one piece of J-2b-1's analysis corrected in wave 2e
and kept here).** There is no `orderedp_bsort_*` and no
`how_many_bsort_*` in the tree, and no `bsortExec`/`bsortL` at all.
J-2b-1 said the kit's Lean termination fact
(`bnextSize (bnext x) < bnextSize x`) exists only in a form "carrying
world and `hreplayed` hypotheses a definition's termination proof
cannot discharge". The DRIVER form has them discharged —
`how_many_bad_pairs_bnext_native_driver (xs) (h : xs ≠ bnextL xs) :
bnextSizeL (bnextL xs) < bnextSizeL xs` is an unconditional theorem
today — so a `bsortL` READING is an ordinary Lean definition on the
REPLAYED measure decrease, with NO hand termination proof at all. What
is NOT discharged is the EXEC's termination: `bsortExec` recurses on
`bnextExec x` for an ARBITRARY `SExpr`, where the replayed decrease (an
`enc`-image statement, per the type-absorbed doctrine) does not reach.
That, plus BSORT's stage-1 `bsort_exec_corr`, is the honest remaining
shape of the kit.

NOT BUILT, and the reason is the standing one: each piece above has no
consumer that could be wired in this wave, so building it now would be
the banned "infrastructure now, wire it later".

**`sorter_unique` — THE `Prop` IS THE BOOK'S AND ITS REACHABILITY IS
THE RECORDED OPEN QUESTION.** The reshape put the `Prop` in the
equisort capstone's own shape (TWO constrained sorters, constrained by
`ORDEREDP-SSORTFN…` and `HOW-MANY-SSORTFN…`), which removes wave 2e's
second route-A obstacle — "the book's capstone relates TWO CONSTRAINED
SORTERS, not one sorter and `ISORT`" is now what the `Prop` says. Two
things are left, and neither is an executor call.

* ROUTE A, the encapsulate/parametric lane (prototype:
  `Imported/Waypoints/EquisortParametric.lean`). (1) The transport's
  binder table hard-errors on a FUNCTION binder — `sorter_unique`'s
  `f` and `g`. (2) THE DEEP ONE, and it is not a machinery gap: the
  `Prop` quantifies over an ARBITRARY Lean `f : List α → List α`, while
  a parametric constant can only be instantiated at a function that is
  the `evalOpt` image of a `World` defun. There is no construction
  taking an arbitrary Lean function to an ACL2 world, so route A cannot
  reach the `Prop` AS STATED however much machinery is built. That is
  the REACHABILITY QUESTION recorded with the 2026-08-18 ruling: the
  `Prop` is correct, and whether it is reachable is a design decision.
* ROUTE B, COMPOSITION FROM LANDED PRODUCTS, whose shape the reshape
  changed and simplified. `ordered_perm_unique` is a THEOREM (and now
  an `Iff`, which is the direction this route needs), and the two
  sorters' hypotheses give count agreement between `f xs` and `g xs`
  directly — so what is left is `permWitness_complete`'s `←` direction
  (counts agree AT THE WITNESS → `Permuted`) plus a COMPOSITION
  mechanism. The first is the structurally-unavailable product above.
  What route B is NOT is free: the glue is logical REASONING over
  replayed facts, and whether that is "thin generic lifting" (canon
  line 1's exception) or a Lean-side theorem specific to this example
  is a RULING, not an executor call. Recorded for it. -/

end ACL2Lean.MirrorProofs
