import ACL2Lean.MirrorProofs.TransportGen
import ACL2Lean.MirrorProofs.SortingSquares
import ACL2Lean.MirrorProofs.SortingPermSquares
import ACL2Lean.MirrorProofs.SortingQsortSquares
import ACL2Lean.Imported.Waypoints.Isort
import ACL2Lean.Imported.Waypoints.Msort
import ACL2Lean.Imported.Waypoints.OrderedPerms
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

FIVE OF THE THIRTEEN target `Prop`s are theorems here — `isort_ordered`,
`msort_ordered` (R4 wave 2c), `ordered_perm_unique` (wave 2d), and
`qsort_ordered` + `qsort_perm` (wave 2e, via O-7's instance-facts
clause), all at `Int`. The other eight have their exact remaining
distance recorded below or on the witness pages; the current
measurements are under "R4 WAVE 2e" and "R4 WAVE 2d", and the older
wave-2c section is kept where it is still current.

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
    from ACL2.Imported.Waypoints.ordered_perms_eq_driver

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

/-! ## R4 WAVE 2e — THE REMAINING FRONTIERS, RE-MEASURED (each against the
real artifact this wave; nothing forced)

**`permWitness_complete` — THE CROSSING NOW CLOSES AGAINST A REAL CITED
WAYPOINT, and the whole remaining distance is the JUNK ARM.** Wave 2d
said the crossing closes; this wave built it and measured what is left of
the MIRROR rung, which 2d could only infer. With the crossing declared
(`intro xs ys; simp only [permuted_agree_permL, permWitness_agree_pceL,
howMany_agree_howManyL]; exact <the PCE row as an iff>`) it closes with
no residual, and the mirror rung's ENTIRE residual is verbatim:

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

— `permuted_map_invariant` fired (the left side is already the mirror's),
and `howMany_map_invariant` is reported UNUSED, which is the precise
statement of the gap: it cannot fire until the WITNESS ARGUMENT is
`e.enc (permWitness xs ys)`, i.e. until the ELEMENT-RESULT homomorphism
square exists.

**THE 2026-08-18 RULING'S ROUTE WAS TAKEN UP, MEASURED, AND IS REFUTED —
and the refutation is kernel-checked, not argued.** The ruling added
`permWitness_complete`'s precondition `(xs ≠ [] ∨ ys ≠ []) →` (LANDED
above and in `Mirrors/Sorting.lean`, verbatim as ruled) on the stated
premise that "the hom square becomes CONDITIONAL (true away from the
junk arm)". Measured against the real definition, THE PREMISE DOES NOT
HOLD: the precondition does not quarantine the junk arm, because the
junk arm is reachable BY RECURSION from inputs the precondition admits.

The conditional square was declared and `fun_induction` run on it. Case 3
closes; the two open cases are verbatim:

```
case case1
h : [] ≠ [] ∨ ys✝ ≠ []
⊢ (List.map e.enc ys✝).headD default = e.enc (ys✝.headD default)

case case2
ih1✝ : xs✝ ≠ [] ∨ Sorting.rm a✝ ys✝ ≠ [] →
    Sorting.permWitness (List.map e.enc xs✝) (Sorting.rm (e.enc a✝) (List.map e.enc ys✝)) =
      e.enc (Sorting.permWitness xs✝ (Sorting.rm a✝ ys✝))
h : a✝ :: xs✝ ≠ [] ∨ ys✝ ≠ []
⊢ Sorting.permWitness (List.map e.enc xs✝) (Sorting.rm (e.enc a✝) (List.map e.enc ys✝)) =
    e.enc (Sorting.permWitness xs✝ (Sorting.rm a✝ ys✝))
```

Case 2 is the refutation: the IH's own precondition is
`xs✝ ≠ [] ∨ rm a✝ ys✝ ≠ []`, which the case's `h` does NOT supply — and
it cannot, because the recursive call legitimately reaches `permWitness
[] []`. THE DISPROOF, kernel-checked at a point the precondition ADMITS
(`xs = ys = [1]`, `#eval` of the two sides is `NIL` and `0`):

```
theorem conditional_elem_square_false :
    ¬ (∀ (xs ys : List Int), (xs ≠ [] ∨ ys ≠ []) →
        Sorting.permWitness (List.map intOrderedEmbed.enc xs)
            (List.map intOrderedEmbed.enc ys)
          = intOrderedEmbed.enc (Sorting.permWitness xs ys)) := by
  intro h; have hc := h [1] [1] (Or.inl (by simp)); exact absurd hc (by decide)
```

AND THE CHARACTERISATION, which is the part that makes this a structural
result rather than a boundary case: `permWitness xs ys` IS the junk value
on the ENTIRE `Permuted` half. The walk consumes `xs`, removing each
element from `ys`; it reaches `permWitness [] []` exactly when every
element of `xs` was found AND `ys` is exhausted — i.e. exactly when
`Permuted xs ys`. Measured: `permWitness [1,2] [2,1] = 0` (= `default`,
a permuting pair of NON-EMPTY lists), against `permWitness [1,2] [2,1,5]
= 5` (leftover head — a real witness) and `permWitness [9] [2] = 9` (not
found — a real witness).

So NO precondition that leaves the theorem's content intact can make the
pointwise square true: the square is true exactly where
`¬ Permuted xs ys`, which is precisely the half of the `Iff` that carries
no content. The `Prop` itself is unharmed on the junk half (both sides
hold for ANY witness), which is why the theorem is true and the SQUARE is
not. The element-result class was therefore NOT LANDED — it would be
machinery whose only consumer is disproved, which is J-2d-6's situation
with a stronger disproof.

WHAT THE SPEC CHANGE IS AND IS NOT. It is LANDED exactly as ruled and it
is a strictly TIGHTER, more honest statement (it says out loud that the
`([],[])` value is invented). It does NOT unblock the transport, and
that is stated here rather than left to be discovered: whoever revisits
this should know the precondition bought clarity, not the route.

THE TWO ROUTES THAT REMAIN, neither an executor call. (1) AN EMBEDDING
WHOSE `default` IS IN RANGE: the square becomes true for any `Acl2Embed`
with `e.enc default = default` (`SExpr`'s default is `nil`), which no
embedding of `Int` can satisfy but a type with a nil-like default could —
a spec/type question. (2) COMPOSITION: on the `Permuted` half both sides
of the `Iff` hold for any witness, so the mirror follows from the
crossing plus "a permutation has equal counts everywhere" — which is
exactly `perm_iff_howMany`'s MISSING `→` direction (next section), so
this route is blocked behind the same absent book theorem, and its glue
is REASONING besides.

**`perm_iff_howMany` — THE BOOK DOES NOT PROVE THE `∀`-FORM.** The
CONVERT-PERM-TO-HOW-MANY waypoint native now EXISTS (R4 wave 2e,
`Imported/Waypoints/ConvertPerm.lean`; the catalogue row is promoted from
`.pending` to `.native`), so the transport was declared against it. The
crossing's residual is verbatim, and it is a CONTENT gap, not a
machinery one:

```
Type mismatch
  Imported.Waypoints.convert_perm_to_how_many_native_driver xs ys
has type
  Worlds.Sorting.permL xs ys =
    (Worlds.Sorting.howManyL (Worlds.Sorting.pceL xs ys) xs ==
      Worlds.Sorting.howManyL (Worlds.Sorting.pceL xs ys) ys)
but is expected to have type
  Worlds.Sorting.permL xs ys = true ↔
    ∀ (a : SExpr), Worlds.Sorting.howManyL a xs = Worlds.Sorting.howManyL a ys
```

Note what this residual proves in passing: the registered agree squares
DO carry the mirror `Prop` all the way into the reading's vocabulary —
the expected type is already in `permL`/`howManyL` terms. The gap is the
theorem itself. The book proves the WITNESS form (counts agree AT
`pceL`); the mirror `Prop` is the `∀`-form. The `←` direction follows
from the native by instantiating at `pceL xs ys`; the `→` direction —
"a permutation has equal counts EVERYWHERE" — is NOT a theorem of this
corpus: the complete `(:DEFTHM …)` inventory of
`sorting/convert-perm-to-how-many` and `sorting/sorts-equivalent`
contains no `PERM-IMPLIES-EQUAL-HOW-MANY`-shaped row. Closing it in Lean
would be `List.Perm.count_eq` — the ornamental-import antipattern, which
is exactly the route the vocabulary rule exists to shut.

A SECOND, INDEPENDENT blocker is recorded because it survives even if
that theorem arrives: the mirror quantifies `∀ a : α` and the crossing
`∀ a : SExpr`, so the crossing implies the mirror but NOT conversely —
an `Iff` needs both, and the encoded-only quantifier cannot produce the
full one (junk elements). That is the ELEMENT-BINDER frontier the charter
predicted, now with a concrete reason rather than a placeholder.

**`sorts_agree` and the two `bsort` `Prop`s — the WAYPOINT NATIVES, and
what building them actually costs.** Measured this wave against the tree,
and the brief's premise ("the catalogue's `.pending`s say the native is
the only gap") is CORRECT about the replay conditions and INCOMPLETE
about the work:

* `MSORT-IS-ISORT` / `QSORT-IS-ISORT` / `BSORT-IS-ISORT` live in
  `sorting/sorts-equivalent`, and **that book has NO waypoint module at
  all** — no `derive_world`, no `driver_replayed%` row, nothing. The
  three natives are not three decode theorems on an existing world; they
  are a new waypoint module for the corpus's largest book, whose
  coverage row already carries eight dependency books
  (`Tests/Coverage/BSsortsEquivalent.lean`).
* `BSORT-IS-ISORT` additionally needs `bsortL`, which needs the BSORT
  exec kit. ONE PIECE OF 2b's J-2b-1 ANALYSIS IS NOW WRONG AND IS
  CORRECTED HERE: it said the kit's Lean termination fact
  (`bnextSize (bnext x) < bnextSize x`) exists only as
  `how_many_bad_pairs_bnext_native_of_replayed`, "carrying world and
  `hreplayed` hypotheses a definition's termination proof cannot
  discharge". The DRIVER form has them discharged —
  `how_many_bad_pairs_bnext_native_driver (xs) (h : xs ≠ bnextL xs) :
  bnextSizeL (bnextL xs) < bnextSizeL xs` is an unconditional theorem
  today — so a `bsortL` READING is an ordinary Lean definition on the
  REPLAYED measure decrease, with NO P2 hand proof at all. What is NOT
  discharged is the EXEC's termination: `bsortExec` recurses on
  `bnextExec x` for an ARBITRARY `SExpr`, where the replayed decrease
  (an `enc`-image statement, per the type-absorbed doctrine) does not
  reach. That, plus BSORT's stage-1 `bsort_exec_corr`, is the honest
  remaining shape of the kit.
* `sorts_agree` names ALL THREE sorts in one `Prop`
  (`msort xs = isort xs ∧ qsort xs = isort xs ∧ bsort xs = isort xs`),
  so it lands only when all three natives do — the BSORT one included.
  It is additionally a COMPOSITION (`mirror_transport%` cites ONE
  waypoint exactly), i.e. a meta-theorem mechanism that does not exist.

NOT BUILT, and the reason is the standing one: each piece above has no
consumer that could be wired in this wave, so building it now would be
the banned "infrastructure now, wire it later".

**`sorter_unique` — SCOUTED ONLY (the wave's item 5), and the scout
found a SECOND route the brief did not name.** Both are recorded; the
choice is a design decision, not an executor's.

* ROUTE A, the encapsulate/parametric lane the brief names. The
  prototype is `Imported/Waypoints/EquisortParametric.lean`: the two
  equisort capstones as L3 world-parametric constants over an abstract
  `w`, with the scope's constraints as stored-rule premises, plus their
  canonical-world instantiations. Three things stand between it and this
  `Prop`, in increasing order of depth. (1) The transport's binder table
  hard-errors on a FUNCTION binder — `sorter_unique`'s `f` is already
  pinned as a tamper probe (wave 2d). (2) The book's capstone relates
  TWO CONSTRAINED SORTERS (`SORTFN1`/`SORTFN2`), not one sorter and
  `ISORT`; getting the mirror's shape needs the constrained-order
  variant through real ACL2, which is the wave's still-unraised ruling.
  (3) THE DEEP ONE, and it is not a machinery gap: the mirror `Prop`
  quantifies over an ARBITRARY Lean `f : List α → List α`, while a
  parametric constant can only be instantiated at a function that is the
  `evalOpt` image of a `World` defun. There is no construction taking an
  arbitrary Lean function to an ACL2 world, so route A cannot reach the
  `Prop` AS STATED however much machinery is built.
* ROUTE B, COMPOSITION FROM LANDED PRODUCTS, which needs no encapsulate
  lane at all. `ordered_perm_unique` is a THEOREM (product 9) and
  `isort_ordered` is a THEOREM (product 1); with `isort_perm` and the
  PERM equivalence's symmetry/transitivity (both replayed —
  `perm_transitive_native_driver`, `isPerm_equivalence_driver`,
  `Imported/Waypoints/PermBook.lean`), `sorter_unique` follows for ANY
  `f` from its own two hypotheses, with no property of `f` beyond them.
  Route B's cost is exactly `isort_perm` (the CONVERT-PERM ∘
  HOW-MANY-ISORT meta-theorem) plus a COMPOSITION mechanism, and both of
  those are ALSO what `sorts_agree` and the `*_perm` family need — so
  the composition mechanism is the single highest-leverage unbuilt
  thing in the arc. What route B is NOT is free: the glue is logical
  REASONING over replayed facts, and whether that is "thin generic
  lifting" (canon line 1's exception) or a Lean-side theorem specific to
  this example is a RULING, not an executor call. Recorded for it. -/

/-! ## R4 WAVE 2d — THE FRONTIERS RE-MEASURED (each measured against the
real artifact this wave, nothing forced; the wave-2c record follows and
is kept where it is still current)

**`qsort_ordered` / `qsort_perm` — the DEPTH blocker is SOLVED and the
`symV` blocker is REFUTED; ONE recorded stop is left, and it is
J-2b-4.** Item 3's measurement, in the order it was taken:

1. `qsortExec_eq_modes` — the exec's own equation RE-SPELLED at the
   mode VALUES `modeLT`/`modeGTE` — states and proves from OUTSIDE
   `Imported/Sorting.lean`, by `rw [qsortExec.eq_def]; rfl`. So J-2b-5's
   premise ("no lemma bridging the two can even be STATED from outside
   that module") is WRONG: `symV` never has to be NAMED, only re-spelled
   past, and de-privatising it is not on the critical path. Recorded as a
   refutation, not a fix.
2. A DEPTH-2, DISPATCH-FREE reading — `qsortOwnL | [] => [] | a :: t =>
   qsortOwnL (filterLtL a t) ++ a :: qsortOwnL (filterGteL a t)` — is a
   Lean definition (its two decrease obligations are the per-mode
   filters' own length bounds). Declared against it, `qsort`'s agree
   square's case 1 CLOSES and case 2's residual is verbatim:

   ```
   ⊢ Worlds.Sorting.qsortOwnL (Sorting.filterRel Sorting.RelMode.lt head✝ t✝) ++
         head✝ :: Worlds.Sorting.qsortOwnL (Sorting.filterRel Sorting.RelMode.gte head✝ t✝) =
       Worlds.Sorting.qsortOwnL (Worlds.Sorting.filterLtL head✝ t✝) ++
         head✝ :: Worlds.Sorting.qsortOwnL (Worlds.Sorting.filterGteL head✝ t✝)
   ```

   — the equation SHAPES now match (wave 2b's `qsortL (head :: t)` stuck
   at a variable tail is gone). What is left is EXACTLY J-2b-4: the four
   registered per-mode squares are stated at `instDecidableEqSExpr` and
   `qsort`'s body builds `decEqOfOrder`, so they do not fire.
3. The instance mismatch has a fact that dissolves it, and it is
   PROVED: `decEqOfOrder_eq_instSExpr :
   (fun a b : SExpr => Sorting.decEqOfOrder a b) = instDecidableEqSExpr`,
   by `funext; exact Subsingleton.elim _ _`. Q4 refuted the GENERAL
   instance-irrelevance form as a rewrite rule (unassignable RHS
   variable); this CONCRETE form has none, and
   `simp only [decEqOfOrder_eq_instSExpr, filterRel_lt_agree_filterLtL]`
   was measured to close the two-instance goal outright.
4. AND IT CANNOT BE PLACED, which is why nothing was taken. The
   `unfold [...]` list is DEFINITIONS ONLY and hard-errors on a lemma
   (verified: "`unfold [...]` is not a DEFINITION"). A LADDER RUNG is the
   other slot, and this fact CANNOT be one: it names
   `ACL2Lean.Sorting.decEqOfOrder`, a MIRROR SPEC constant, while
   `IsoGen.lean` imports only `ACL2Lean.Syntax` — a generic generator
   whose fixed kit mentions one spec's instance would be a category
   error.

So the remaining distance for BOTH qsort products is one decision, and
it is a RECORDED STOP (J-2b-4) plus the placement question above: either
a per-square INSTANCE-CANONICALISATION channel, or J-2b-4's restatement
of the four per-mode squares at `decEqOfOrder` (which the fact in (3)
would now repair — wave 2b's `.lt`/`.gt` regression is exactly the
`==`-vs-`decide` gap it closes). Not taken here; class 5 of the
delegation boundary returns it to the orchestrator. A THIRD item is
attached to whichever route wins: `qsortOwnL` cannot be VALIDATED where
it stands — a second general `derive_sim%` for "QSORT" is fail-closed
("already has a registered iso"), and converting `qsortL` itself needs
`filterLtL` visible from `Imported/Sorting.lean`, i.e. a split of that
grandfathered module.

**`permWitness_complete` — the ELEMENT-RESULT square class is not the
whole gap, and the rest is a SPEC question.** Item 4's measurement:

* the CROSSING closes. `permWitness_complete SExpr` reduces under the
  registered agree squares (`permuted_agree_permL`,
  `permWitness_agree_pceL`, `howMany_agree_howManyL`) to exactly
  `permL xs ys = true ↔ howManyL (pceL xs ys) xs = howManyL (pceL xs ys) ys`,
  which is the catalogued PCE native modulo `beq_iff_eq` — a decode-shape
  corollary of the class this layer already writes.
* the MIRROR rung needs a FOURTH square class, the ELEMENT-RESULT
  homomorphism `permWitness (map e.enc xs) (map e.enc ys) =
  e.enc (permWitness xs ys)`. It was BUILT in scratch (a `hom elem`
  spec, the result reading inferred from the definition's own result
  type, drift-checked like the other two) and it ELABORATES: every case
  closes except one, verbatim:

  ```
  ⊢ (List.map e.enc ys✝).headD default = e.enc (ys✝.headD default)
  ```

* and that residual is FALSE, for a reason no machinery can fix. It is
  the JUNK ARM: at `xs = ys = []` the book's `PERM-COUNTER-EXAMPLE`
  returns `(car nil)` = `nil`, and Q3's spec returns `Inhabited.default`
  — `SExpr`'s derived default IS `nil`, but `intEmbed.enc` is
  `.atom (.number (.int ·))` and NEVER `nil`, so no `Acl2Embed` on `Int`
  can send `default` to `default`. Every other case of the square is
  true.
  The `Prop` itself is unharmed (at `[] []` both sides hold for any
  witness) — it is the pointwise SQUARE that cannot be stated, and
  proving the transport by hand around the junk point would be a
  Lean-side theorem specific to this example (canon line 1). So the
  class was NOT LANDED (it would be unwired machinery), and the open
  question is a spec/design one: how a mirror declares an arm whose
  value is junk. Reader-facing, so Mike's.

**`perm_iff_howMany`, `sorts_agree`, `bsort_ordered`/`bsort_perm` — NO
WAYPOINT THEOREM EXISTS TO TRANSPORT.** Checked concretely in the tree,
not inferred from the catalogue: there is no
`convert_perm_to_how_many_*`, no `*_is_isort_*`, no `orderedp_bsort_*`
or `how_many_bsort_*`, and no `bsortExec`/`bsortL` at all. The
catalogue's `.pending` rows say the same (`CONVERT-PERM-TO-HOW-MANY`:
"UNLOCK: build the native"; `ORDEREDP-BSORT`/`HOW-MANY-BSORT`: "the
missing waypoint native and the bsort exec kit ONLY"). So the three
machinery items the brief attached to them — the element-binder
widening (`perm_iff_howMany`'s `∀ a : α` is the first `Prop` that would
hit the binder check), the composition meta-theorems, and the bsort exec
kit — each have NO consumer that could be wired now, and building any of
them would be the banned "infrastructure now, wire it later" (the
J-2b-1 finding, unchanged). Recorded, not built. The composition route
additionally carries the brief's own constraint: `sorts_agree` and the
`*_perm` family are compositions of TWO book theorems, and any step
requiring REASONING is the honest frontier, never a Lean proof.

## THE TRANSPORT FRONTIERS — what each unlanded `Prop` actually needs
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

**RULINGS Q1/Q2/Q4 (2026-08-18) MOVED THREE OF THE LINES BELOW; the
current state is on `MirrorProofs/SortingPermSquares.lean` and in W13's
Q4 postscript, and it is summarised here so this page is not stale:**

* `Permuted`'s spec body was RE-RENDERED through the own-definitions
  `memb`/`rm` (Q1). Its HOM square is now LIVE, both of the blockers
  recorded below are gone, and its AGREE square's whole remaining
  distance is ONE square — `rm a ys = ys.erase a`, blocked on the
  equality-test ORIENTATION of the library reading `List.erase` (two
  candidate ladder rungs measured, both REGRESS live squares).
* `bsort`'s spec body was re-rendered as the book's fixpoint recursion
  (Q2); its squares' blocker moved from the access pattern to a looping
  closer and a missing reading (W14's postscript).
* Q4's decide-instance-irrelevance route was MEASURED and does not
  dissolve `qsort`'s agree-square mismatch (W13's postscript), so
  `qsort_ordered` and `qsort_perm` did not land and the product count
  is unchanged at TWO sorting mirrors.
* `qsort_perm`'s remaining distance is therefore exactly TWO squares:
  `qsort`'s agree square (unchanged, held for Mike) and `Permuted`'s
  agree square (one `rm` square away).

**`Permuted` — the frontier is in the SPEC's own vocabulary, and the
reading-layer conversion is NOT the unblock (wave 2c measured it).**
[SUPERSEDED BY Q1 — kept as the record the ruling rested on.]
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
