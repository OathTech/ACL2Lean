import ACL2Lean.MirrorProofs.SortingSquares
import ACL2Lean.Imported.SortingBsort

/-! # MIRROR PROOFS — the sorting book's PERM and MEASURE squares

The witness page's second half. `MirrorProofs/SortingSquares.lean`
carries the SORT ALGORITHMS' squares (W1–W14); this page carries the
vocabulary the 2026-08-18 spec re-renders introduced — the book's PERM
chain (`MEMB`, `RM`, `PERM`) and its BUBBLE MEASURE chain
(`HOW-MANY-SMALLER`, `BNEXT-SIZE`). The split is the module-size norm:
the algorithm page was at 1445 of 1500 lines, and this wave's squares
do not fit in it.

## WHY THESE SQUARES EXIST NOW (Mike's rulings Q1/Q2, 2026-08-18)

Waves 2b and 2c measured `Permuted`'s two squares blocked, and wave 2c
established WHERE: not in the reading layer (own-definition twins of
the readings failed at exactly the same two places) but in the SPEC's
own body — `Mirrors/Sorting.lean`'s `Permuted` rendered the book's
`PERM` through the LIBRARY `∈` and `List.erase` and stated the base
case as `ys = []`, where the vocabulary practice would have a book
function be an OWN-DEFINITION. That was reader-facing, so it went to
Mike; the ruling (Q1) was to re-render, and the spec now reads

```
def Permuted [DecidableEq α] : List α → List α → Prop
  | [], [] => True
  | [], _ :: _ => False
  | a :: xs, ys => memb a ys = true ∧ Permuted xs (rm a ys)
```

— the book's `(IF (CONSP X) (IF (MEMB (CAR X) Y) (PERM (CDR X) (RM
(CAR X) Y)) 'NIL) (IF (CONSP Y) 'NIL 'T))` at the same access pattern,
through the own-definitions `memb` (MEMB) and `rm` (RM). Both of wave
2c's blockers are gone: the base arm now destructures `ys` (so there is
no `ys = []` to meet a `Bool` reading's `isEmpty`), and the head test is
a `Bool` equation rather than a `Prop` membership.

Ruling Q2 re-rendered `bsort` as the book's fixpoint recursion, which
brings the book's own measure into the spec (`howManySmaller`,
`howManyBadPairs`) — hence the second chain here.

## WHAT LANDED, AND WHAT DID NOT (all measured, nothing forced)

* `memb` — BOTH classes LIVE. The agree square is against `List`'s own
  `contains`, and the reading's equality test is TARGET-FIRST
  (`List.elem a b`), exactly as the book's `(EQUAL A (CAR X))` and the
  mirror's `if a = b` are.
* `rm` — the HOM square is LIVE; the AGREE square is a ONE-RESIDUAL
  frontier, recorded verbatim below. It is the same reading-vocabulary
  finding one level down, and it is now load-bearing.
* `Permuted` — the HOM (map-invariance) square is LIVE, and it is the
  square wave 2c recorded as blocked on three LIBRARY facts
  (`List.map_eq_nil_iff`, `List.mem_map` + injectivity, `List.erase`
  under an injective `map`). The re-render dissolved all three: the
  body no longer mentions any of those operations. The AGREE square's
  ENTIRE remaining distance is `rm`'s agree square (below).
* `howManySmaller`, `howManyBadPairs` — ALL FOUR squares LIVE, against
  the existing own-definition readings `howManySmallerL` / `bnextSizeL`
  (`Imported/SortingBsort.lean`).
-/

namespace ACL2Lean.MirrorProofs

open ACL2 ACL2Lean

/-! ## W17 — `memb` and `rm` (the book's MEMB and RM)

`memb`'s agree square is against `List.contains`, which is what
`List.isPerm` — the waypoint layer's PERM reading, and the vocabulary
every PERM-* native is stated in — spells its membership test as. The
`unfold` list is definitions only: `List.contains`, `List.elem` and the
`BEq`-from-`DecidableEq` instance, which is what makes the reading's
`==` and the mirror's `if a = b` the same test.

Two `decide` rungs joined the closer's fixed kit for this square and are
the LADDER's only change in this wave (`IsoGen.lean`, the criterion's
`rfl`-lemma clause, pinned there by `example … := rfl` like every other
`rfl` rung): `decide_true` and `decide_false`. They are the `decide`
twin of the already-admitted `cond`/`ite` pairs — one operation's own
two values, relating nothing — and both are stated in core over an
ARBITRARY `Decidable` instance, which is what lets them fire on a
`decide` the reading and the mirror reached by different routes. -/

mirror_iso% memb_agree_contains for ACL2Lean.Sorting.memb
  vars [a, xs]
  square agree (xs.contains a)
  unfold [List.contains, List.elem, instBEqOfDecidableEq]

/-- info: 'ACL2Lean.MirrorProofs.memb_agree_contains' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms memb_agree_contains

mirror_iso% memb_map_invariant for ACL2Lean.Sorting.memb
  vars [a, xs]
  square hom scalar

/-- info: 'ACL2Lean.MirrorProofs.memb_map_invariant' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms memb_map_invariant

mirror_iso% rm_map_hom for ACL2Lean.Sorting.rm
  vars [a, xs]
  square hom list

/-- info: 'ACL2Lean.MirrorProofs.rm_map_hom' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms rm_map_hom

/-! ### `rm`'s AGREE square — ONE residual, and it is the READING's
equality-test ORIENTATION (R4 wave 2d-prep, measured, NOT declared)

Declared as

```
  mirror_iso% rm_agree_erase for ACL2Lean.Sorting.rm
    vars [a, xs]
    square agree (xs.erase a)
    unfold [List.erase, instBEqOfDecidableEq]
```

the base case and the `e = a` case close, and case 3's residual is
verbatim:

```
h✝ : ¬a = head✝
ih1✝ : Sorting.rm a t✝ = t✝.erase a
⊢ head✝ :: t✝.erase a =
    match decide (head✝ = a) with
    | true => t✝
    | false => head✝ :: t✝.erase a
```

— the two sides are the same list; what does not meet is the ORDER of
the equality test's arguments. The book's `RM` tests `(EQUAL E (CAR X))`
and the mirror renders that faithfully (`if e = a`); `List.erase` tests
`a == b` with the LIST HEAD first. `List.erase` is one of the four
logged vocabulary-compliance items (`Imported/SimGen.lean`'s note), and
this is the first square where the compliance gap is load-bearing
rather than cosmetic.

BOTH candidate ladder rungs were MEASURED AND BOTH REGRESS LIVE
SQUARES, so neither was taken (this is a refutation, not a
"not taken pending a ruling"):

* `eq_comm` (core, permutative). It fires on the SQUARE'S OWN top-level
  equation and flips it, and FIVE live agree squares stop closing
  (`insertOrd`, `isort`, `merge2` — whose definition-directed split
  then finds zero guard hypotheses — `msort`, and the `filterRel`
  family).
* `decide_eq_comm` (`decide (a = b) = decide (b = a)`, own, narrower —
  fires only under `decide`). It COLLIDES with the already-admitted
  `Bool.decide_eq_true`: at `α := Bool` it rewrites
  `decide (lexorderB head ev = true)` to `decide (true = lexorderB head
  ev)`, which that rung can no longer see, and the FOUR `filterRel`
  agree squares stop closing. Residual verbatim:

  ```
  h✝ : (decide (true = Worlds.Sorting.lexorderB head✝ ev) && !decide (ev = head✝)) = true
  ⊢ head✝ :: Worlds.Sorting.filterLtL ev t✝ =
      bif Worlds.Sorting.lexorderB head✝ ev && !decide (ev = head✝) then …
  ```

So the remaining route is the one the compliance census has named for
months and this square now motivates: an OWN-DEFINITION `rmL` reading
written to `RM`'s own body shape. That is a WAYPOINT-LAYER change — it
moves `permExec_enc`'s proof term and every PERM-* native's statement
vocabulary — so it is out of this wave's scope and is recorded, not
attempted.

## W15 — `Permuted` (HOM LIVE; the AGREE square is exactly `rm`'s)

The map-invariance square below is what wave 2c recorded as blocked on
three LIBRARY facts about the operations the OLD spec body used; the Q1
re-render removed the operations, and the square closes on the
registered `memb`/`rm` squares plus the fixed kit.

THE AGREE SQUARE, measured with `memb`'s square registered and `rm`'s
absent — cases 1 and 2 (the two blockers wave 2c recorded) CLOSE, and
the whole residual is the missing `rm` square:

```
ih1✝ : Sorting.Permuted xs✝ (Sorting.rm a✝ ys✝) = (xs✝.isPerm (Sorting.rm a✝ ys✝) = true)
⊢ ((List.elem a✝ ys✝ && xs✝.isPerm (Sorting.rm a✝ ys✝)) = true) =
    ((List.elem a✝ ys✝ && xs✝.isPerm (ys✝.erase a✝)) = true)
```

— `memb` is already rewritten to the reading's `List.elem` on both
sides; `rm a ys` versus `ys.erase a` is all that is left. -/

mirror_iso% permuted_map_invariant for ACL2Lean.Sorting.Permuted
  vars [xs, ys]
  square hom scalar

/-- info: 'ACL2Lean.MirrorProofs.permuted_map_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms permuted_map_invariant

/-! ### W15's PRIOR RECORD — what waves 2b/2c measured against the OLD
`Permuted` body (moved here verbatim from the algorithm page when the
re-render moved the subject; it is the evidence the ruling rested on)

**`Permuted` — the `∈`/`erase` refinement.** The `hom scalar` square
(`Permuted (List.map e.enc xs) (List.map e.enc ys) = Permuted xs ys`)
elaborates and leaves both cases:

```
case case1  ⊢ (List.map e.enc ys✝ = []) = (ys✝ = [])
case case2  ⊢ (e.enc a✝ ∈ List.map e.enc ys✝ ∧ Sorting.Permuted (List.map e.enc xs✝) ((List.map e.enc ys✝).erase (e.enc a✝))) =
    (a✝ ∈ ys✝ ∧ Sorting.Permuted xs✝ (ys✝.erase a✝))
```

— three library facts, each an ELEMENT-position refinement square of a
library operation the spec body uses: `List.map_eq_nil_iff` (in the
ladder's NOT-admitted column by name), `List.mem_map` + injectivity, and
`(List.map f ys).erase (f a) = List.map f (ys.erase a)` under
injectivity. The `agree` square against `List.isPerm` leaves

```
case case1  ⊢ (ys✝ = []) = (ys✝.isEmpty = true)
case case2  ⊢ (a✝ ∈ ys✝ ∧ xs✝.isPerm (ys✝.erase a✝) = true) =
    ((ys✝.contains a✝ && xs✝.isPerm (ys✝.erase a✝)) = true)
```

— `Bool.and_eq_true` again (W11's rung) plus `List.isEmpty_iff` and
`List.contains_iff`, which are library lemmas about a LIBRARY-SPELLED
READING: `List.isPerm`/`contains`/`erase` are three of the four logged
vocabulary-compliance items (`Imported/SimGen.lean`'s note). This square
is the first consumer that would justify converting them to
own-definitions; that conversion moves `permExec_enc`'s proof term and is
out of wave 2b's regression net.

## W18 — the BUBBLE MEASURE chain (LIVE, all four)

`howManySmaller` is the book's `HOW-MANY-SMALLER` and `howManyBadPairs`
is its `BNEXT-SIZE`; together they are `BSORT`'s measure, and the Q2
re-render brought them into the spec because the book's fixpoint
recursion needs them to be a definition at all.

Both readings already existed as own-definitions in the bsort waypoint
kit (`Imported/SortingBsort.lean`: `howManySmallerL`, `bnextSizeL`), so
both agree squares are the ordinary W1-route square: the order instance
in the `unfold` list carries the mirror's `a ≤ e` to the reading's
`lexorderB a e`, and the `BEq`-from-`DecidableEq` instance carries the
mirror's `if e = a` to the reading's `e == a` (TARGET-FIRST on both
sides here — which is exactly what `rm` above lacks).

Both map-INVARIANCE squares are over `OrderedEmbed`: the count is only
invariant under an embedding that RESPECTS the order (`ord` discharges
the `≤` test, `enc_inj_iff` the equality test). -/

mirror_iso% howManySmaller_agree_howManySmallerL
    for ACL2Lean.Sorting.howManySmaller
  vars [ev, xs]
  square agree (Worlds.Sorting.howManySmallerL ev xs)
  unfold [Worlds.Sorting.howManySmallerL, instTotalOrderSExpr,
    instBEqOfDecidableEq]

/-- info: 'ACL2Lean.MirrorProofs.howManySmaller_agree_howManySmallerL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms howManySmaller_agree_howManySmallerL

mirror_iso% howManySmaller_map_invariant for ACL2Lean.Sorting.howManySmaller
  vars [ev, xs]
  square hom scalar
  embed OrderedEmbed via [ord]

/-- info: 'ACL2Lean.MirrorProofs.howManySmaller_map_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms howManySmaller_map_invariant

mirror_iso% howManyBadPairs_agree_bnextSizeL
    for ACL2Lean.Sorting.howManyBadPairs
  vars [xs]
  square agree (Worlds.Sorting.bnextSizeL xs)
  unfold [Worlds.Sorting.bnextSizeL]

/-- info: 'ACL2Lean.MirrorProofs.howManyBadPairs_agree_bnextSizeL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms howManyBadPairs_agree_bnextSizeL

mirror_iso% howManyBadPairs_map_invariant for ACL2Lean.Sorting.howManyBadPairs
  vars [xs]
  square hom scalar
  embed OrderedEmbed via [ord]

/-- info: 'ACL2Lean.MirrorProofs.howManyBadPairs_map_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms howManyBadPairs_map_invariant

end ACL2Lean.MirrorProofs
