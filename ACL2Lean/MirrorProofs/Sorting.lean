import ACL2Lean.MirrorProofs.TransportGen
import ACL2Lean.MirrorProofs.SortingSquares
import ACL2Lean.MirrorProofs.SortingPermSquares
import ACL2Lean.Imported.Waypoints.Isort
import ACL2Lean.Imported.Waypoints.Msort
import ACL2Lean.Imported.Waypoints.OrderedPerms

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
remaining distance recorded below or on the witness page. (The
2026-08-18 rulings Q1/Q2 were SPEC re-renders and Q4 a measurement:
they moved squares, not products, and the count stands at two — see the
summary under THE TRANSPORT FRONTIERS.)

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
