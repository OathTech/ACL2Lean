import ACL2Lean.MirrorProofs.TransportGen
import ACL2Lean.MirrorProofs.SortingSquares
import ACL2Lean.Imported.Waypoints.Isort
import ACL2Lean.Imported.Waypoints.Msort

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

TWO OF THE THIRTEEN target `Prop`s are theorems here (`isort_ordered`,
`msort_ordered`, both at `Int`); the other eleven have their exact
remaining distance recorded below or on the witness page.

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
that the first real consumer did not demand it. (The binder check still
stands as a frontier for a Prop with an ELEMENT binder — `perm_iff_
howMany`'s `∀ a` is the first one that will hit it. Nothing in this wave
does.)

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

/-! ## THE TRANSPORT FRONTIERS — what each unlanded `Prop` actually needs
(R4 wave 2c, each MEASURED, nothing forced)

**`qsort_ordered` — ONE missing square, and it is the one held for
Mike.** The transport was declared against the catalogued ORDEREDP-QSORT
native and fails on the CROSSING, with a residual that names the gap and
nothing else (verbatim):

```
Type mismatch
  Imported.Waypoints.orderedp_qsort_native_driver xs
has type
  Worlds.Sorting.orderedpRec (Worlds.Sorting.qsortL xs) = true
but is expected to have type
  Worlds.Sorting.orderedpRec (Sorting.qsort xs) = true
```

— i.e. everything else is in place (the `Ordered` agree square carried
the mirror `Prop` into the reading's vocabulary; `qsort_map_hom` now
exists for the transport rung), and the whole remaining distance is
`qsort`'s AGREE square, whose two blockers (the reading's depth, and
`symV`'s privacy) are W13's and are held.

**`isort_perm` — NOT a machinery gap: THE BOOK DOES NOT PROVE IT.** The
mirror `Prop` is `∀ xs, Permuted (isort xs) xs`, and the transport cites
ONE waypoint theorem exactly. The isort book's catalogued natives are
ORDEREDP-ISORT, HOW-MANY-ISORT and TRUE-LISTP-ISORT (`Imported/
Waypoints/Catalog.lean`); there is no `(isortL xs).isPerm xs = true`
anywhere in the tree, and no ACL2 theorem of that shape to replay. The
book's route to it is the COMPOSITION `CONVERT-PERM-TO-HOW-MANY` (the
`perm_iff_howMany` capstone) with `HOW-MANY-ISORT` — two theorems, which
is a wave-2d meta-theorem, not a `mirror_transport%` declaration. The
only PERM-shaped sorting native that exists is `PERM-QSORT`
(`(qsortL xs).isPerm xs = true`), so `qsort_perm` is the perm mirror
that is nearest — and it needs BOTH the `qsort` agree square (above) and
the `Permuted` agree square (below).

**`Permuted` — the frontier is in the SPEC's own vocabulary, and the
reading-layer conversion is NOT the unblock (wave 2c measured it).**
Wave 2b left `Permuted`'s two squares blocked on "the library-spelled
readings", i.e. on the logged `contains`/`erase`/`isPerm` compliance
items, and this wave was to convert them. Measured first, per the
drive-off-the-real-artifact rule, and the conclusion is the opposite:

* the AGREE square against the LIBRARY reading reproduces wave 2b's
  residual UNCHANGED by O-3's new rung (the `←` direction cannot touch
  a `∈` conjunct, which is not a `Bool` equation at all):

  ```
  case case1  ⊢ (ys✝ = []) = (ys✝.isEmpty = true)
  case case2  ⊢ (a✝ ∈ ys✝ ∧ xs✝.isPerm (ys✝.erase a✝) = true) =
      ((ys✝.contains a✝ && xs✝.isPerm (ys✝.erase a✝)) = true)
  ```

* the AGREE square against OWN-DEFINITION TWINS (`membL`/`rmL`/`permL`,
  written in `.tmp` to the book's MEMB/RM/PERM body shapes purely to
  locate the blocker — deliberately NOT declared in the tree) fails at
  exactly the same two places:

  ```
  case case1  ⊢ (ys✝ = []) = ((match ys✝ with | [] => true | head :: tail => false) = true)
  case case2  ⊢ (a✝ ∈ ys✝ ∧ Worlds.Sorting.permL xs✝ (ys✝.erase a✝) = true) =
      ((Worlds.Sorting.membL a✝ ys✝ && Worlds.Sorting.permL xs✝ (Worlds.Sorting.rmL a✝ ys✝)) = true)
  ```

  Both blockers are on the MIRROR side and are untouched by the reading:
  the spec's `ys = []` against ANY `Bool`-valued reading's base arm
  (`Permuted`'s own match never destructures `ys`, and it emits no
  guarded equation, so the W7 split cannot fire), and the spec's `a ∈ ys`
  — a `Prop` membership — against any `Bool` membership test.

* the HOM SCALAR square's residual is likewise about the SPEC BODY's
  own library operations, not about a reading (verbatim):

  ```
  case case1  ⊢ (List.map e.enc ys✝ = []) = (ys✝ = [])
  case case2  ⊢ (e.enc a✝ ∈ List.map e.enc ys✝ ∧ Sorting.Permuted (List.map e.enc xs✝) ((List.map e.enc ys✝).erase (e.enc a✝))) =
      (a✝ ∈ ys✝ ∧ Sorting.Permuted xs✝ (ys✝.erase a✝))
  ```

  — `List.map_eq_nil_iff`, `List.mem_map` + injectivity, and
  `List.erase`-commutes-with-an-injective-`map`: three LIBRARY facts
  about LIBRARY operations that `Mirrors/Sorting.lean`'s `Permuted`
  spells in its own body (`∈`, `List.erase`, `= []`).

  (One incidental generator finding, recorded: `embed OrderedEmbed` does
  not elaborate on a `Permuted` square, because `Permuted` carries
  `[DecidableEq α]` and NOT `[TotalOrder α]`, which `OrderedEmbed α`
  requires. That is correct fail-closed behaviour — the richer embedding
  is only stateable where the order is in scope — and the plain
  `Acl2Embed` is the right declaration here anyway.)

SO THE READING CONVERSION WAS NOT BUILT, and the reason is the one wave
2b gave for the bsort exec kit (J-2b-1): completing it would leave BOTH
`Permuted` squares exactly where they are, which makes building it now
the banned "infrastructure now, wire it later". What the measurement
says instead is that `Permuted`'s frontier is a SPEC question — the
mirror's body mirrors the book's PERM through library `∈`/`List.erase`
where the vocabulary practice would have a book function be an
own-definition — and spec bodies are reader-facing, i.e. Mike's. The
compliance census (`Imported/SimGen.lean`'s note: `contains`/`erase`/
`isPerm`, plus `Sorting.lean`'s append reading) is unchanged and still
open; this wave adds only the finding that it is not what blocks the
perm mirrors. -/

end ACL2Lean.MirrorProofs
