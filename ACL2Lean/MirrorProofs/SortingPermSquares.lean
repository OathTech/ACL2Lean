import ACL2Lean.MirrorProofs.SortingSquares
import ACL2Lean.Imported.SortingBsort
import ACL2Lean.Imported.SortingConvertPerm

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

/-! ### `rm`'s AGREE square — LIVE since R4 wave 2d (the OWN-DEFINITION
`rmL` reading), and the record of what it took

The square below is the ONE the whole perm chain was waiting on:
`Permuted`'s agree square, and `permWitness`'s, were each EXACTLY this
one square away. The frontier record from wave 2d-prep is kept verbatim
underneath, because it is the evidence the reading conversion rested on.

WHAT CHANGED: the reading. `RM`'s waypoint reading was `xs.erase a`
until R4 wave 2d item 1 and is now the own-definition
`Worlds.Sorting.rmL` (`Imported/SortingReadings.lean`), written to the
book's `RM` body shape with the equality test TARGET-FIRST — which is
what the residual below was about. The reading is `derive_sim%`-
VALIDATED against the real `RM` exec (`rmExec_enc`, `Imported/
Perm.lean`), so it is admissible by the same gate every other reading
passes; the decodes that keep a `List.erase` statement do so through
`rmL_eq_erase`, a DECODE-LAYER-ONLY bridge that is barred by name from
this closer's kit (the guard at the bridge). -/

mirror_iso% rm_agree_rmL for ACL2Lean.Sorting.rm
  vars [a, xs]
  square agree (Worlds.Sorting.rmL a xs)
  unfold [Worlds.Sorting.rmL]

/-- info: 'ACL2Lean.MirrorProofs.rm_agree_rmL' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms rm_agree_rmL

/-! ### THE PRIOR RECORD — `rm`'s agree square against the LIBRARY
reading `List.erase` (R4 wave 2d-prep, measured, NOT declared). This is
the measurement that motivated the conversion above; both candidate
ladder rungs are refuted here and stay refuted.

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
attempted. [TAKEN in R4 wave 2d item 1; the square above is the result.]

## W15 — `Permuted` (BOTH CLASSES LIVE since R4 wave 2d)

The map-invariance square below is what wave 2c recorded as blocked on
three LIBRARY facts about the operations the OLD spec body used; the Q1
re-render removed the operations, and the square closes on the
registered `memb`/`rm` squares plus the fixed kit.

THE AGREE SQUARE is now LIVE too, against the own-definition reading
`Worlds.Sorting.permL`. Wave 2d-prep measured it with `memb`'s square
registered and `rm`'s absent — cases 1 and 2 (the two blockers wave 2c
recorded) CLOSED, and the whole residual was the missing `rm` square:

```
ih1✝ : Sorting.Permuted xs✝ (Sorting.rm a✝ ys✝) = (xs✝.isPerm (Sorting.rm a✝ ys✝) = true)
⊢ ((List.elem a✝ ys✝ && xs✝.isPerm (Sorting.rm a✝ ys✝)) = true) =
    ((List.elem a✝ ys✝ && xs✝.isPerm (ys✝.erase a✝)) = true)
```

— `memb` already rewritten to the reading's `List.elem` on both sides;
`rm a ys` versus `ys.erase a` all that was left. With `rm_agree_rmL`
registered above and the reading itself converted to `permL` (whose
three-arm match is the spec's own, and whose removal step is `rmL`),
the square closes with `permL` as its ONLY unfold. -/

mirror_iso% permuted_agree_permL for ACL2Lean.Sorting.Permuted
  vars [xs, ys]
  square agree (Worlds.Sorting.permL xs ys)
  unfold [Worlds.Sorting.permL]

/-- info: 'ACL2Lean.MirrorProofs.permuted_agree_permL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms permuted_agree_permL

mirror_iso% permuted_map_invariant for ACL2Lean.Sorting.Permuted
  vars [xs, ys]
  square hom scalar

/-- info: 'ACL2Lean.MirrorProofs.permuted_map_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms permuted_map_invariant

/-! ## W16 — `permWitness` (the book's PERM-COUNTER-EXAMPLE): the AGREE
square is LIVE

Wave 2b recorded this square as FALSE, and it was: the spec rendered
`PERM-COUNTER-EXAMPLE` as a `List.find?` multiplicity scan returning
`Option α`, which is a DIFFERENT ALGORITHM from the book's erase-walk
(the `some (pceL …)`-shaped square is refuted at `xs = ys = []`). Mike's
ruling Q3 (2026-08-18) re-rendered the spec as the book's own walk —
`(if (memb (car x) y) (pce (cdr x) (rm (car x) y)) (car x))`, `(car y)`
on an exhausted `x` — returning a VALUE.

The square is stated against the existing waypoint reading
`Worlds.Sorting.pceL` (`Imported/SortingConvertPerm.lean`), whose own
removal step became `rmL` in R4 wave 2d (it is a CONSUMER of the `RM`
reading conversion: `pceExec` calls the `RM` exec, so `pceExec_enc`'s
induction meets `rmL` and nothing else). It closes on the registered
`memb` and `rm` squares plus the fixed kit, with `pceL` its only
unfold; the `(CAR Y)` arm meets `List.headD ys default` because
`SExpr`'s DERIVED `Inhabited` default IS `SExpr.nil` — the same value
ACL2's `(car nil)` has. -/

mirror_iso% permWitness_agree_pceL for ACL2Lean.Sorting.permWitness
  vars [xs, ys]
  square agree (Worlds.Sorting.pceL xs ys)
  unfold [Worlds.Sorting.pceL]

/-- info: 'ACL2Lean.MirrorProofs.permWitness_agree_pceL' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms permWitness_agree_pceL

/-! ### `permWitness`'s HOM square — THE FOURTH SQUARE CLASS, LIVE
(close-out arc item 2, 2026-08-18)

`permWitness` returns an ELEMENT, which is the fourth refinement row:
`e.enc (permWitness xs ys) = permWitness (map e.enc xs) (map e.enc ys)`.
The class is `hom elem` (`IsoGen.lean`), oriented exactly like
`hom list` so the transport's reversed rewrite set carries it with no
special case, and drift-checked against the definition's own result
type like every other class.

IT IS NOT TRUE FOR AN ARBITRARY `Acl2Embed`, and the prior record below
is the measurement that says so: its whole residual was the JUNK ARM,
`e.enc default = default`. That is a fact about the EMBEDDING alone, so
it lands the way `ord` did — as a HYPOTHESIS of the square's statement,
via the richer `ValueOrNilEmbed` (`IsoKit.lean`) whose `encDefault`
field says the element type's invented value is ACL2's `nil`. The
`Option` ROW builds such an embedding for any element type whose own
encoding avoids `nil` (`optIntEmbed`, `MirrorProofs/OrderBridge.lean`),
and `Option`'s `default` IS `none`, so the field is discharged BY THE
ROW.

The other input the square needed was the SPEC's own access pattern:
`permWitness`'s `(CAR Y)` arm now DESTRUCTURES `ys` (the same re-render
`Permuted` carries for `(IF (CONSP Y) …)`), so `fun_induction` hands
the closer three cases that the fixed kit closes, instead of one case
with an undestructured `List.headD` the kit cannot reach into
(measured: with `List.headD` in the unfold list the residual is
`e.enc (match ys, default with …) = match List.map e.enc ys, default with …`,
verbatim). -/

mirror_iso% permWitness_map_hom for ACL2Lean.Sorting.permWitness
  vars [xs, ys]
  square hom elem
  embed ValueOrNilEmbed via [encDefault]

/-- info: 'ACL2Lean.MirrorProofs.permWitness_map_hom' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms permWitness_map_hom

/-! ### THE PRIOR RECORD — the square measured at wave 2d item 4, when
the class did not exist and the residual was read as fatal

(R4 wave 2d item 4, measured, NOT declared)

`permWitness` returns an ELEMENT, which is a fourth refinement row the
square table did not have: `permWitness (map e.enc xs) (map e.enc ys) =
e.enc (permWitness xs ys)`. The class was BUILT in scratch — a `hom
elem` spec whose result reading is inferred from the definition's own
result type and drift-checked exactly like `hom list`/`hom scalar` — and
it ELABORATES: every case closes but one, verbatim:

```
⊢ (List.map e.enc ys✝).headD default = e.enc (ys✝.headD default)
```

That residual is FALSE, and no machinery can repair it. It is the JUNK
ARM: at `xs = ys = []` the book's `PERM-COUNTER-EXAMPLE` returns
`(CAR NIL)` = `nil`, and the spec (Q3) returns `Inhabited.default`.
`SExpr`'s DERIVED default IS `nil` — but `intEmbed.enc` is
`.atom (.number (.int ·))` and never `nil`, so no `Acl2Embed` on `Int`
sends `default` to `default`. Every other case of the square is true,
and the `Prop` itself is unharmed (at `[] []` both sides hold for any
witness): it is the POINTWISE square that cannot be stated.

So the class was NOT LANDED — with its only consumer refuted it would be
unwired machinery, which is the banned "infrastructure now, wire it
later". The open question is a SPEC one (how a mirror declares an arm
whose value is junk), and it is reader-facing, so Mike's. The full
record, including the crossing that DOES close, is on the product page.

WHAT THE CLOSE-OUT ARC CHANGED, against exactly that residual: it is
FALSE for an embedding of `Int` and TRUE for one whose `default` is
ACL2's `nil`, so it became the square's own HYPOTHESIS
(`ValueOrNilEmbed.encDefault`) rather than a repair — and the `Option`
ROW builds such an embedding generically. The sentence "no machinery can
repair it" was right about REPAIR and wrong about the class: what was
missing was an element TYPE, not a lemma.

### W16's EARLIER PRIOR RECORD — wave 2b, against the OLD `List.find?`
body (moved here verbatim from the algorithm page, since the subject's
squares live on this page; it is the evidence ruling Q3 rested on)

**`permWitness` — a DIFFERENT ALGORITHM, and no result class.** This one
is not a lemma or a rung away, and it should be read as a spec finding.
The mirror is
`List.find? (fun a => howMany a xs != howMany a ys) (xs ++ ys)` — a
multiplicity scan. The book's `PERM-COUNTER-EXAMPLE`, whose reading is
`Worlds.Sorting.pceL` (`Imported/SortingConvertPerm.lean`), is the
erase-walk: `| [], ys => ys.headD nil | x :: xs, ys => bif ys.contains x
then pceL xs (ys.erase x) else x`. Declaring the agree square produces
ONE case whose goal is the entire equation —

```
⊢ List.find? (fun a => Worlds.Sorting.howManyL a xs != Worlds.Sorting.howManyL a ys) (xs ++ ys) =
    some (Worlds.Sorting.pceL xs ys)
```

— i.e. a THEOREM about two different algorithms agreeing, not a
definitional correspondence, and the template is right to refuse it. The
square in that shape is in fact FALSE, which is the cleanest statement of
the gap: at `xs = ys = []` the left side is `none` (nothing differs) and
the right side is `some SExpr.nil` (the book's witness function returns a
VALUE, never an option), so no `some`-wrapped reading can be the mirror's
correspondent. The `hom scalar` square does not even elaborate,
and its failure names a real gap in the square classes:

```
Type mismatch
  Sorting.permWitness xs ys
has type
  Option α
but is expected to have type
  Option SExpr
```

— the map-INVARIANCE class asserts `fn (encoded args) = fn args`, which
types only when the result type is CLOSED (`Nat`, `Bool`, `Prop`). An
`Option α` result needs a RESULT READING (`Option.map e.enc`), which is a
third result class the square table does not have — the derived-reading
frontier at the result position rather than the argument position. Both
are recorded; neither is forced.

**[SUPERSEDED, close-out arc item 2.]** Ruling Q3 (2026-08-18) replaced
the `List.find?` multiplicity scan by the book's own erase-walk, which is
what made the AGREE square a definitional correspondence. The
RESULT-position frontier the last paragraph names is the class that then
landed as `hom elem` — the ELEMENT result carried by `e.enc`, NOT an
`Option α` result carried by `Option.map e.enc`. The `Option` rendering
the paragraph gestures at is the ELEMENT-TYPE row (`optEmbed`,
`IsoKit.lean`), and the reason it is not a result class is on the product
page: at `SExpr` the value-or-nil refinement is not injective (`none` and
`some nil` share an image), so an `Option`-VALUED spec definition cannot
be crossed at all. -/

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
