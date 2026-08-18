import ACL2Lean.MirrorProofs.IsoGen
import ACL2Lean.MirrorProofs.OrderBridge
import ACL2Lean.Mirrors.Sorting
import ACL2Lean.Imported.SortingOdds
import ACL2Lean.Imported.SortingModeReadings

/-! # MIRROR PROOFS — the sorting book's SQUARES (the WITNESS PAGE)

`ACL2Lean/Mirrors/Sorting.lean`'s Props are the buildout's north star.
This page exists because R1 item B widened `mirror_iso%`'s
ARGUMENT-READING table (audit finding F1) and that widening had to land
against REAL square declarations read off the sorting spec — not against
a test fixture (the anti-"infrastructure now, wire it later" rule). It
is the landing zone for the sorting squares. The PRODUCTS the squares
carry — since R4 wave 2c, `isort_ordered` and `msort_ordered` at `Int`,
the first two of the thirteen target `Prop`s to become THEOREMS — live
in `MirrorProofs/Sorting.lean`, which was split out of this file at that
wave (this one had crossed the 1500-line module-size norm, and the seam
between the METRIC's squares and the PRODUCT's transports is where the
split belongs).

The page carries TWENTY-SIX LIVE squares, each `#print axioms`-pinned,
and covers the COMPLETE definition inventory of `Mirrors/Sorting.lean` —
every one of its FIFTEEN definitions appears below in both square
classes, LIVE or with its frontier recorded verbatim. Nothing is left
undeclared and nothing is forced.

| witness | agree | hom |
| ------- | ----- | --- |
| W1 `insertOrd` | LIVE (R1-D) | LIVE (wave 1 — the order dimension) |
| W2 `howMany`   | LIVE (R1-D) | LIVE (R1-D, scalar) |
| W5 `isort`     | LIVE (wave 1) | LIVE (wave 1) |
| W6 `evens`     | LIVE (wave 1) | LIVE (wave 1) |
| W7 `merge2`    | LIVE (2a — the split) | LIVE (2a — the split) |
| W8 `msort`     | LIVE (2a) | LIVE (2a) |
| W9 `odds`      | LIVE (2a — kit + `fun_cases`) | LIVE (2a — `fun_cases`) |
| W3 `filterRel` | LIVE ×4 (2a — the per-mode family) | LIVE (2a) |
| W10 `bnext`    | **LIVE (2b)** | **LIVE (2b)** |
| W11 `Ordered`  | **LIVE (2c — the O-3 rung)** | LIVE (2b, scalar) |
| W12 `relMode`  | frontier (2b — `fun_cases` generalizes the key) | **LIVE (2b, scalar)** |
| W13 `qsort`    | frontier (2b — the reading's depth + `symV`) | **LIVE (2c — O-2's notation normalization)** |
| — `List.append` | (n/a — a library callee, no reading) | **LIVE (2c — O-2's registered square)** |
| W14 `bsort`    | frontier (2b — no exec kit is constructible) | frontier (2b — the `foldl` rendering) |
| W15 `Permuted` | frontier (2b — library-spelled reading) | frontier (2b — the `∈`/`erase` refinement) |
| W16 `permWitness` | **LIVE (2d — against `pceL`, after the `rm` reading conversion)** | **LIVE (close-out item 2 — the `hom elem` class over `ValueOrNilEmbed`)** |

Wave 1's four RECORDED frontiers (W3, W7, W8, W9) are all closed by the
four wave-2a decisions Mike endorsed on 2026-08-16 (the synthesis's R-6).
Their records are kept below, section by section, because they are what
each ruling was made on — and because the residuals they quote are the
acceptance evidence that the fix was the one the frontier named:

* **W7 `merge2`** — the DEFINITION-DIRECTED CASE SPLIT (`IsoGen`'s
  section of that name). Wave 1 measured "ONE case split on the
  undestructured argument, then the EXISTING kit"; that is exactly what
  the closer gained, and the three cases that already closed still close
  by the kit alone.
* **W8 `msort`** — nothing of its own: wave 1 measured both squares
  reducing to `merge2`'s, and W7 unblocked them at two four-line
  declarations, as predicted.
* **W9 `odds`** — the `fun_cases` FALLBACK for a NON-RECURSIVE spec
  definition (the hom square), plus the ODDS EXEC KIT and the
  own-definition reading `oddsL` (`Imported/SortingOdds.lean`) that the
  agree square needed — the second, independent gap wave 1 separated out.
* **W3 `filterRel`** — the PER-MODE assembly: four DISPATCH-FREE
  own-definition readings validated by `derive_sim%` against the real
  `FILTER` exec at their literal modes
  (`Imported/SortingModeReadings.lean`), `vars` taking a CONSTRUCTOR
  LITERAL, and the KEYED registry that lets one definition carry a
  per-constructor FAMILY of agreement squares. The hom square is wave 1's
  stage-4 measurement declared, after one more rung of the
  already-admitted Bool/decide family (`Bool.false_eq_true`).

THE LINE, as amended: the kit still grows only by LEMMA rungs meeting the
pinned criterion, and the closer has exactly ONE structural capability —
the definition-directed split, which reads the definition and never
searches. GROUND EVALUATION (W3 stage 3's other candidate) was NOT taken
and is not needed: the per-mode readings removed the dispatch it would
have had to evaluate.

## What R1-B changed

Before: `mirror_iso%` collapsed a mirror definition's binder telescope to
one `allList` boolean and hard-errored on ANY non-list explicit argument —
so every sorting definition with an ELEMENT argument (`insertOrd (a : α)`,
`howMany (a : α)`) was rejected by the SHAPE TABLE, before its statement was
ever built. After: the telescope is read into a per-binder READING VECTOR
inferred from the spec's own Lean binder types (`List α` ↦ enters under
`List.map e.enc`; `α` ↦ enters under `e.enc`), with no new user syntax.

## What the R1-D ruling batch (2026-08-14) changed

Three machinery-side items, all recorded here because their acceptance
witnesses are this page's squares:

1. **`Acl2Embed.inj` admitted to the closing ladder** (as the iff
   `enc_inj_iff`) — the FIRST of the two plumbing families the pinned
   criterion now names (the second, `Bool.decide_eq_true`, arrived with
   R4 wave 0 below). See `IsoGen.lean`'s ladder section for why both are
   plumbing (a square is definitional correspondence about OUR OWN
   definitions; content still arrives only via replay).
2. **Hypothesis-directed closing.** The closer was ALREADY
   `simp_all`-class, so the case hypotheses of a split the template
   itself created were always in scope; what W1's residual actually
   needed was for the hypothesis to SPEAK THE GOAL'S VOCABULARY. Under
   `OrderBridge`'s instance `a ≤ b` IS `lexorderB a b = true`, and the
   instance is a DEFINITION — so it goes in the invocation's
   `unfold [...]` list (definitions only, already gated), and the fixed
   kit gained `cond`'s own two cases (`Bool.cond_true/false`,
   `rfl`-lemmas, pinned in `LadderPins`). Measured: without the instance
   in the unfold list the two `bif`/`≤` residuals below survive
   verbatim; with it, W1's agree square closes.
3. **The HOW-MANY waypoint reading went OWN-DEFINITION**
   (`Worlds.Sorting.howManyL`, `Imported/Sorting.lean`), retiring the
   `xs.count e` library spelling that surfaced in W2's agree residual as
   a demand for `List.count_cons`. One of the five logged
   vocabulary-compliance readings; four remain (`SimGen.lean`'s note).

## What the R1-E FILTER re-render (2026-08-14) changed

Mike's ruling (item 3 of the R1-D batch, taken separately): a mirror is
the CLOSEST IDIOMATIC LEAN analog of the BOOK — step (1) of a two-step
use, step (2) being ordinary Lean reasoning from it to the theorem the
user actually wants — so closeness to the book beats maximal Lean-idiom
polish. `Mirrors/Sorting.lean`'s `FILTER` was therefore re-rendered to
the book's shape: `(filter fn x e)` is a MODE (`REL`'s `FN` argument,
one of the book's four quoted symbols) and a PIVOT ELEMENT, not the
predicate closure the spec carried until then. `RelMode`/`relMode` are
the new spec definitions; the 13 target `Prop`s are byte-identical
across the change (their statements do not mention `filterRel`).

The machinery consequence is the reading table's third case, `.fixed`
(`IsoGen.lean`): an explicit argument whose type is CLOSED — no free
variables, so in particular no occurrence of the element type — is one
the embedding has no action on, and it passes through both sides of a
square unchanged, at its own type. That is what lets `filterRel`'s mode
argument be read at all. A FUNCTION over the element type stays outside
the table with the same F5-style message (now naming three derived
readings instead of two).

One thing the batch did NOT rule, found on contact and reported: the
statement builder DROPPED the mirror definition's own instance binders,
so `howMany`'s `hom scalar` statement did not elaborate at all
(`failed to synthesize instance of type class DecidableEq α`) — the
ladder change could not be witnessed until the statement existed. The
builder now re-binds them (`[DecidableEq α]`, `[TotalOrder α]`, …) at the
user's element type, with a hard error for any class that is not a
one-parameter class over that type. See `mirrorFnShape`.

## The witnesses, and what each one established

**W1 `insertOrd (a : α) : List α → List α`** — the audit's executed
reject, now the batch's item-2 acceptance. Its frontier moved in three
recorded stages:

*Stage 1 (R1-B):* the first real blocker was an instance, not a shape —
`insertOrd` carries `[TotalOrder α]`, so its `agree` square at `List SExpr`
demanded a `TotalOrder SExpr` instance that did not then exist
(`error: failed to synthesize instance of type class Sorting.TotalOrder
SExpr`, then `mirror_iso%`'s hard error, candidate cause (c)).

*Stage 2 (R1-C):* `MirrorProofs/OrderBridge.lean` now provides that
instance by LEXORDER's Bool reading, backed by the CORE-LOGIC theorems of
`LexorderOrder.lean` (trio-clean — nothing here trusts ACL2), plus the
restriction lemma `lexorderB (intEmbed.enc m) (intEmbed.enc n) =
decide (m ≤ n)` (the R4 order bridge). Re-probed with the instance, the
`agree` square vs `Worlds.Sorting.insertL` ELABORATED its statement and
the CLOSER left exactly two residuals (verbatim, the two cases of the
comparison split):

```
h✝ : a ≤ head✝
⊢ a :: head✝ :: t✝ =
    bif Worlds.Sorting.lexorderB a head✝ then a :: head✝ :: t✝
    else head✝ :: Worlds.Sorting.insertL a t✝
```

(and its `¬` twin, with the `ih1✝` induction hypothesis available).

*Stage 3 (R1-D):* CLOSED, and LIVE below. `a ≤ head✝` IS
`lexorderB a head✝ = true` definitionally under the instance, so naming
the instance in the `unfold [...]` list normalises the case hypothesis to
that Bool equation; `simp_all` then rewrites the reading's `bif`
condition with it and `cond`'s own two cases finish both branches. The
`hom list` square is still NOT declared: it needs the embedding to
RESPECT the order, and `Acl2Embed` has no order field by construction
("that dimension arrives with sorting", `IsoGen`) — an honest frontier,
and a failing `mirror_iso%` leaves a `sorryAx`-carrying declaration
behind, which this tree does not accept.

**W2 `howMany (a : α) : List α → Nat`** — the positive one, and the
batch's items 1+3 acceptance. Its `agree` square elaborated from the
start (the element binder read as `.elem` and typed `SExpr`, the list
binder as `.list`, `DecidableEq SExpr` found); the closer's residual was

```
⊢ (if a = head✝ then 1 else 0) + List.count a t✝ = List.count a (head✝ :: t✝)
```

— i.e. it wanted `List.count_cons`, a LIBRARY lemma about a LIBRARY
reading, which the fixed ladder rightly cannot reach. Item 3 removed the
cause rather than the symptom: the reading is now the own-definition
`howManyL`, whose own equation the invocation unfolds, and the square
CLOSES (live below). The `hom scalar` square's residual was the
element-position `if e.enc a = e.enc head✝ …` vs `if a = head✝ …`; item
1's `enc_inj_iff` rewrites exactly that, and it CLOSES too — once the
statement builder stopped dropping `[DecidableEq α]` (above). Recorded
from R1-B and still standing: the `hom scalar` CODEC is fine for a `Nat`
result — that class asserts scalar INVARIANCE (`fn (encoded args) =
fn (args)`) and carries no result codec at all.

**W3 `filterRel`** — two recorded stages:

*Stage 1 (R1-B):* with the spec's old signature `filterRel (keep : α →
Bool)` this was the expected named frontier and was PINNED here: the
shape table hard-errored on the function-valued argument before any
declaration was produced, so the pin cost no `sorryAx`.

*Stage 2 (R1-E):* that frontier is DISSOLVED — not widened. The
function argument was the MIRROR SPEC's idiom, never the book's
(`(filter fn x e)` is a mode symbol plus a pivot element), and the
ruling above re-rendered the spec to the book. There is no
function-valued argument left to reject, so the pin is gone with it;
what stands in its place is a MEASURED state, recorded here because no
declaration can carry it.

The two statements now BUILD (verbatim `#check`, off the generator):

```
filterRel_agree_filterL : ∀ (fn : Sorting.RelMode) (ev : SExpr) (xs : List SExpr),
  Sorting.filterRel fn ev xs = Worlds.Sorting.filterL (modeSym fn) ev xs

@filterRel_map_hom : ∀ {α : Type u_1} [inst : Sorting.TotalOrder α]
  [inst_1 : DecidableEq α] (e : Acl2Embed α) (fn : Sorting.RelMode) (ev : α)
  (xs : List α),
  List.map e.enc (Sorting.filterRel fn ev xs) = Sorting.filterRel fn (e.enc ev) (List.map e.enc xs)
```

(`modeSym : RelMode → SExpr` is the four-line machinery-side decode of
the mode to the book's quoted symbol; the mode reads `.fixed` and so
appears UNCHANGED on both sides of the homomorphism square, which is
exactly what the pass-through reading claims.)

Neither CLOSES, and the two failures are different:

* `hom list` fails for W1's reason, in FILTER vocabulary — the
  embedding would have to respect the ORDER. Residual verbatim (case 2
  of the split; case 3 is its `¬` twin):

  ```
  h✝ : Sorting.relMode fn head✝ ev = true
  ih1✝ : List.map e.enc (Sorting.filterRel fn ev t✝) = Sorting.filterRel fn (e.enc ev) (List.map e.enc t✝)
  ⊢ e.enc head✝ :: Sorting.filterRel fn (e.enc ev) (List.map e.enc t✝) =
      if Sorting.relMode fn (e.enc head✝) (e.enc ev) = true then
        e.enc head✝ :: Sorting.filterRel fn (e.enc ev) (List.map e.enc t✝)
      else Sorting.filterRel fn (e.enc ev) (List.map e.enc t✝)
  ```

  i.e. it wants `relMode fn (e.enc a) (e.enc ev) = relMode fn a ev`.
  `enc_inj_iff` (ruling item 1) covers the mode's EQUALITY test; the
  `≤` test is the order dimension `Acl2Embed` has no field for. Honest
  frontier, unchanged in substance from W1's.

* `agree` fails on VOCABULARY, three separate gaps, measured one at a
  time (the whole residual is ~100 lines of stuck `match fn`/`if`
  chain; the load-bearing lines are quoted):

  1. the MODE DISPATCH. The reading's `relL` selects by comparing
     symbols (`if fv == symV "LT" then …`), so the closer must both
     case-split `fn` — `fun_induction` inducts on `filterRel`'s own
     list recursion and never touches the mode — and then EVALUATE a
     ground `Bool` comparison. `simp only` does neither: with the mode
     bound it is stuck at
     `(match fn with | RelMode.lt => SExpr.atom (Atom.symbol {name := "LT", …}) | …) == symV "LT"`,
     and even at a CONCRETE mode the ground comparison does not reduce
     (measured: `simp only []` does not fire `reduceIte` at all).
  2. `decide (b = true)` vs `b`. The spec's `relMode` is Bool-valued
     over `decide (i ≤ j)`, and under the order instance that is
     `decide (lexorderB i j = true)`, while the reading has the plain
     `lexorderB i j`:
     `h✝ : (decide (Worlds.Sorting.lexorderB head✝ ev = true) && !decide (head✝ = ev)) = true`.
     Closing that needs `Bool.decide_eq_true` — NOT a `rfl`-lemma (it
     is `cases b <;> rfl`), so it is outside the ladder's pinned
     admission criterion.
  3. `==` vs `decide (· = ·)`. This one is already reachable under the
     current rules: `instBEqOfDecidableEq` is a DEFINITION, so naming
     it in the invocation's `unfold [...]` list turns the reading's
     `!a == e` into the spec's `!decide (a = e)`.

  The obvious repair — give `relMode` its own `agree` square, which the
  closer would then pick up automatically as a REGISTERED CALLEE square
  of `filterRel` — is not available: `relMode` is NOT RECURSIVE, and
  Lean generates no functional induction principle for a non-recursive
  definition, so the template's `fun_induction` fails outright
  (`No functional induction theorem for 'relMode'`). That bound is
  general, not a `relMode` quirk: `odds` and `permWitness` are
  non-recursive spec definitions too.

  MEASURED CLOSING CONDITION (against the real spec definitions, in
  `.tmp`, not declared): with a MODE-SPECIALIZED reading — the one the
  waypoint theorems actually speak, e.g. `xs.filter (fun a =>
  lexLtB a ev)` for `'LT` and `xs.filter (fun a => lexorderB ev a)` for
  `'GTE`, which have no symbol dispatch — gap 1 disappears, gap 3 is an
  unfold-list entry, and the square closes IFF the fixed kit gains gap
  2's single rung. Removing that rung alone re-opens it. So the whole
  distance between here and a live `agree` square is: (i) one ladder
  rung (`decide (b = true) = b`), plus (ii) a way to declare a square
  at a SPECIFIC mode — `vars` takes identifiers, and `registerSquare`
  is fail-closed at one `agree` square per mirror definition, so four
  per-mode squares cannot be registered as things stand. Both are
  design changes to the square classes, i.e. rulings, not edits — and
  per the thin-Lean ruling the escape is never a hand square.

*Stage 3 (R4 wave 0, 2026-08-14):* rung (i) LANDED — `Bool.decide_eq_true`
is in the fixed kit and the ladder's criterion now reads "`rfl`-lemmas +
two named plumbing families" (`IsoGen.lean`). Route (ii) — the ruled
ENUM-REFINEMENT registry, a once-per-datatype constructor↦ACL2-value
table off which the generator would emit one square per constructor with
the mapped LITERAL on the waypoint side — was NOT built, because its
acceptance witness does not close. What was measured, four modes each
(`.tmp`, not declared; `filterRel <ctor> ev xs = filterL <literal> ev xs`,
the registry's own statement shape):

* THE RULED LADDER (fixed kit incl. the new rung): FAILS, all four.
* the ruled ladder + GROUND EVALUATION (`simp_all (config :=
  { decide := true })`) + `ite`'s own two cases (`ite_true`/`ite_false`):
  CLOSES, all four.
* R1-E's stage-2 measurement REPRODUCES unchanged: against the
  dispatch-free mode-specialized reading the square closes with the rung
  and re-opens without it.

The finding that separates them: R1-E's "mode specialization" was at the
READING level — a reading with no symbol dispatch, which is also the
vocabulary the REAL waypoint drivers speak (`Imported/Waypoints/
Qsort.lean`: `all_rel_filter_1_native_driver`,
`how_many_filter_1_native_driver` state `xs.filter (fun a => lexLtB a
ev)`, never `filterL '<mode>`). The registry as ruled specializes the
ARGUMENT VALUE instead, and hands that literal to `filterL`, whose
`relL` still dispatches at runtime (`fv == symV "LT"`). The fixed closer
cannot evaluate that ground comparison: `simp only`'s simprocs do not
decide `SExpr` equality, and `Worlds.Sorting.symV` is PRIVATE — so it
can neither be named in the invocation's `unfold [...]` list nor matched
by the reading's own dispatch `rfl`-lemmas `relL_LT`/`relL_LTE`/
`relL_GTE` (simp matches up to REDUCIBLE defeq, and `symV` is neither
reducible nor nameable here). Gap 1 of stage 2 is therefore NOT removed
by instantiating the mode; it is removed only by a dispatch-free reading.

So the remaining distance is THREE ladder ingredients, not one:
`Bool.decide_eq_true` (landed), `ite_true`/`ite_false` (`rfl`-lemmas —
`ite`'s own two cases, the exact analogue of the already-admitted `cond`
pair), and GROUND EVALUATION in rung 2, which is NEW IN KIND: not a
lemma but a closer CAPABILITY, outside the pinned criterion as written.
(The argument for it: rung 1 is bare `rfl`, which already computes
without limit, so deciding CLOSED propositions inside rung 2 is no
stronger, and a square over variables cannot be closed by ground
evaluation. The argument against: the criterion says "nothing else", and
every previous kit change here was a ruling.) That is a ruling, not an
executor call — and per the thin-Lean ruling the escape is never a hand
square.

The `hom list` square was RE-PROBED at R4 wave 0 for the record: its
residual was byte-identical to stage 2's (same two cases, same wanted
fact `relMode fn (e.enc a) (e.enc ev) = relMode fn a ev`); frontier
unchanged at that point — `enc_inj_iff` covers the mode's EQUALITY test,
the `≤` test is the order dimension `Acl2Embed` has no field for.

*Stage 4 (R4 wave 1, 2026-08-14) — the ORDER half of W3's `hom list`
frontier is GONE; only a `Bool` coercion is left.* `filterRel` was out of
wave 1's declared scope, so nothing is declared here, but the wave's
`OrderedEmbed` bears directly on the residual above and the measurement
belongs on the record. Measured (`.tmp`, not declared) with the square
stated over `OrderedEmbed` and closed by the wave-1 kit plus `e.ord`:

* the `≤` test is DISCHARGED — `ord` is a `Prop`-level iff, so it
  rewrites under `decide` and the whole `relMode` dispatch follows; the
  positive case CLOSES;
* what survives is one case, and it is not about order at all:

  ```
  ⊢ Sorting.filterRel fn (e.enc ev) (List.map e.enc t✝) =
      if false = true then e.enc head✝ :: Sorting.filterRel fn (e.enc ev) (List.map e.enc t✝)
      else Sorting.filterRel fn (e.enc ev) (List.map e.enc t✝)
  ```

* with `Bool.false_eq_true` added to the fixed kit — the same Bool/decide
  coercion family as the already-admitted `Bool.decide_eq_true` — the
  square CLOSES, all cases.

So W3's `hom list` distance is now ONE rung of an already-admitted
family, plus the declaration itself; the `agree` square's three gaps
(stage 2/3) are untouched by this wave and stand as recorded.
-/

namespace ACL2Lean.MirrorProofs

open ACL2 ACL2Lean

/-! ## W1 — `insertOrd` agrees with the INSERT reading (LIVE)

The mirror definition at `List SExpr` IS `insertL`'s recursion. The
`unfold` list is DEFINITIONS ONLY: the waypoint reading itself, and the
order instance whose `le` field is the reading's own `lexorderB`
comparison (which is what lets the split's case hypothesis close the
`bif`). -/

mirror_iso% insertOrd_agree_insertL for ACL2Lean.Sorting.insertOrd
  vars [a, xs]
  square agree (Worlds.Sorting.insertL a xs)
  unfold [Worlds.Sorting.insertL, instTotalOrderSExpr]

/-- info: 'ACL2Lean.MirrorProofs.insertOrd_agree_insertL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms insertOrd_agree_insertL

/-! ## W2 — `howMany` (LIVE, both classes)

The AGREEMENT square is against the OWN-DEFINITION reading `howManyL`
(ruling batch item 3); the MAP-INVARIANCE square is the element-position
homomorphism the embedding's injectivity closes (item 1). -/

mirror_iso% howMany_agree_howManyL for ACL2Lean.Sorting.howMany
  vars [a, xs]
  square agree (Worlds.Sorting.howManyL a xs)
  unfold [Worlds.Sorting.howManyL]

/-- info: 'ACL2Lean.MirrorProofs.howMany_agree_howManyL' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms howMany_agree_howManyL

mirror_iso% howMany_map_invariant for ACL2Lean.Sorting.howMany
  vars [a, xs]
  square hom scalar

/-- info: 'ACL2Lean.MirrorProofs.howMany_map_invariant' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms howMany_map_invariant

/-! ## W4 — `insertOrd`'s HOMOMORPHISM square (LIVE — the order dimension)

The square W1 stage 3 recorded as an honest frontier ("it needs the
embedding to RESPECT the order, and `Acl2Embed` has no order field by
construction"). R4 wave 1 closes it the way the frontier said it had to
be closed — by giving the embedding the field, not by giving the closer
a rung: `OrderedEmbed` (`MirrorProofs/OrderBridge.lean`) extends
`Acl2Embed` with `ord : (enc a ≤ enc b) ↔ (a ≤ b)`, and the
`embed … via [...]` clause binds it in THIS square's statement and hands
that one field to THIS square's closer (`IsoGen`'s "the order-respect
route" carries the criterion text; `intOrderedEmbed` is the witness, its
field proved by `lexorderB_intEmbed`).

The square is not merely easier this way — it is only TRUE this way: for
an embedding that does not respect the order the encoded insertion takes
the other branch. Measured residual WITHOUT `ite`'s own two cases in the
fixed kit (the ladder's other wave-1 addition), both cases verbatim:

```
h✝ : a ≤ head✝
⊢ e.enc a :: e.enc head✝ :: List.map e.enc t✝ =
    if True then e.enc a :: e.enc head✝ :: List.map e.enc t✝
    else e.enc head✝ :: Sorting.insertOrd (e.enc a) (List.map e.enc t✝)
```

— i.e. the order field had already done its whole job; what was left was
`ite`'s own two cases. -/

mirror_iso% insertOrd_map_hom for ACL2Lean.Sorting.insertOrd
  vars [a, xs]
  square hom list
  embed OrderedEmbed via [ord]

/-- info: 'ACL2Lean.MirrorProofs.insertOrd_map_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms insertOrd_map_hom

/-! ## W5 — `isort` (LIVE, both classes) — the first sorting chain

Both squares resolve `insertOrd`'s REGISTERED squares out of the
registry and would fail closed without them (the `rev`→`app` pattern of
THE LIST item 9, one book up). The homomorphism square inherits the
order dimension from its callee: it is declared over `OrderedEmbed` too,
because `insertOrd_map_hom` — the rewrite its step case needs — is. -/

mirror_iso% isort_agree_isortL for ACL2Lean.Sorting.isort
  vars [xs]
  square agree (Worlds.Sorting.isortL xs)
  unfold [Worlds.Sorting.isortL]

/-- info: 'ACL2Lean.MirrorProofs.isort_agree_isortL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isort_agree_isortL

mirror_iso% isort_map_hom for ACL2Lean.Sorting.isort
  vars [xs]
  square hom list
  embed OrderedEmbed via [ord]

/-- info: 'ACL2Lean.MirrorProofs.isort_map_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isort_map_hom

/-! ## W6 — `evens` (LIVE, both classes)

The msort chain's structural half. `evens` uses no order at all, so its
homomorphism square is over the PLAIN `Acl2Embed` — which is also the
demonstration that the wave-1 `embed` clause is opt-in per square and
changes nothing where it is not declared.

The `agree` square carries ONE extra unfolding, `List.tail`, and it is
worth saying why: the two sides destructure at different DEPTHS. The
mirror `evens` matches three patterns (`[]`, `[a]`, `a :: _ :: t`,
mirroring the book's `(cons (car l) (evens (cdr (cdr l))))`), while the
waypoint reading `evensL` matches two and reaches the second element
through `List.tail`. `List.tail` is a DEFINITION, so it is admissible in
the `unfold [...]` list on the same terms as any other (a definitional
unfolding cannot introduce content), and unfolding it is exactly what
lets the reading's `evensL t.tail` meet the mirror's `evens t`. It is
also a FINDING about the reading, recorded rather than fixed here:
`evensL`'s body is spelled with a library function, which is the
vocabulary-compliance class `Imported/SortingReadings.lean` tracks —
re-spelling it would move `evensExec_enc`'s proof term and is out of
wave 1's regression net. -/

mirror_iso% evens_agree_evensL for ACL2Lean.Sorting.evens
  vars [xs]
  square agree (Worlds.Sorting.evensL xs)
  unfold [Worlds.Sorting.evensL, List.tail]

/-- info: 'ACL2Lean.MirrorProofs.evens_agree_evensL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evens_agree_evensL

mirror_iso% evens_map_hom for ACL2Lean.Sorting.evens
  vars [xs]
  square hom list

/-- info: 'ACL2Lean.MirrorProofs.evens_map_hom' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms evens_map_hom

/-! ## W7 — `merge2` (LIVE, both classes) — the undestructured arm

Wave 1 measured this frontier and did not take it; ruling R-6/W7
(2026-08-16) took it. The distance was ONE definition-directed case
split, and that is exactly what the closer now has (`IsoGen`'s "the
definition-directed case split"): the argument is read off `merge2`'s own
GUARDED equation `merge2.eq_2`, not off the goal, and the split fires
only in the case the ladder alone did not CLOSE. The three cases that
closed under the wave-1 kit still close by the kit, unsplit.

The historical record of the frontier — both residuals verbatim, and the
four measured closing conditions in order of how much they ask for — is
kept below under "W7's record", because it is what the ruling was made
on. -/

mirror_iso% merge2_agree_merge2L for ACL2Lean.Sorting.merge2
  vars [xs, ys]
  square agree (Worlds.Sorting.merge2L xs ys)
  unfold [Worlds.Sorting.merge2L, instTotalOrderSExpr]

/-- info: 'ACL2Lean.MirrorProofs.merge2_agree_merge2L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms merge2_agree_merge2L

mirror_iso% merge2_map_hom for ACL2Lean.Sorting.merge2
  vars [xs, ys]
  square hom list
  embed OrderedEmbed via [ord]

/-- info: 'ACL2Lean.MirrorProofs.merge2_map_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms merge2_map_hom

/-! ## W7's record — the frontier as wave 1 measured it (the UNDESTRUCTURED-ARM bound)

THREE of the four cases of BOTH squares close with the wave-1 kit.
Case 2 does not, in either, and it is the same cause in both — the one
new frontier this wave found.

CAUSE. The mirror `merge2` renders the book's `(if (consp x) (if (consp
y) … x) y)` faithfully, so its second arm does NOT destructure the first
list (`| xs, [] => xs`). Lean therefore generates that equation GUARDED:

```
Sorting.merge2.eq_2 : ∀ {α} [TotalOrder α] (x : List α),
  (x = [] → False) → Sorting.merge2 x [] = x
```

and `fun_induction` hands the template a case whose scrutinee is a bare
variable plus that guard. Neither square can get past it:

* AGREE (residual verbatim; cases 1/3/4 close):

  ```
  xs✝ : List SExpr
  x✝ : xs✝ = [] → False
  ⊢ xs✝ = Worlds.Sorting.merge2L xs✝ []
  ```

  The waypoint reading DOES destructure (`| x :: xs, [] => x :: xs`), so
  neither of `merge2L`'s equations applies to a variable — the goal is
  stuck, and `simp_all` reports "made no progress".

* HOM (residual verbatim; cases 1/3/4 close, the order field doing its
  work in 3/4 exactly as in W4):

  ```
  xs✝ : List α
  x✝ : xs✝ = [] → False
  ⊢ List.map e.enc xs✝ = Sorting.merge2 (List.map e.enc xs✝) (List.map e.enc [])
  ```

  Here both sides are the MIRROR definition, so there is no reading to
  blame: to fire `eq_2` on the right the closer must discharge
  `List.map e.enc xs✝ = [] → False` from `xs✝ = [] → False`, i.e.
  transport the guard through `List.map`.

MEASURED CLOSING CONDITIONS (`.tmp`, not declared), in order of how much
they ask for:

1. ONE CASE SPLIT on the undestructured argument, then the EXISTING kit:
   both squares close, all four cases, nothing else added — the `nil`
   branch by the guard (`absurd rfl`), the `cons` branch by the kit.
   Measured verbatim.
2. `List.map_eq_nil_iff` in the fixed kit: does NOT close the hom square
   (case 2 survives unchanged) and cannot touch the agree square at all.
3. `merge2L.eq_def` in the `unfold` list: LOOPS (`Possibly looping simp
   theorem: merge2L.eq_3`, then max recursion depth) — recorded so the
   next reader does not re-try it.
4. A `split` rung after the kit: no effect — there is no `match`/`ite`
   in either residual to split.

So the distance is ONE ingredient, and it is a CLOSER CAPABILITY, not a
lemma: the template would have to case-split an argument the mirror
definition's own recursion left alone. That is new in kind — the same
class as W3 stage 3's GROUND EVALUATION, and outside the ladder's pinned
criterion, which admits `rfl`-lemmas and the two plumbing families and
nothing else. Wave 1 held that line (see `IsoGen`'s ladder section) and
recorded the measurement instead of taking it; the shape of a ruling
would be "when the mirror definition's equation leaves an argument
undestructured, the closer may refine that case by the argument's own
constructors". Per the thin-Lean ruling the escape is never a hand
square.

## W8 — `msort`'s record (it was blocked ONLY on W7; now LIVE below)

Both `msort` squares reduce, under the wave-1 kit plus the REGISTERED
`evens` squares and `unfold [ACL2Lean.Sorting.odds]`, to exactly
`merge2`'s corresponding square — nothing else is missing. Cases 1 and 2
close in both; case 3's residual, after the closer has run, is verbatim:

* AGREE — literally `merge2 A B = merge2L A B` at the two recursive
  results (i.e. `merge2_agree_merge2L` instantiated):

  ```
  ⊢ Sorting.merge2 (Worlds.Sorting.msortL (Worlds.Sorting.evensL (a✝ :: head✝ :: t✝)))
        (Worlds.Sorting.msortL (Worlds.Sorting.evensL (head✝ :: t✝))) =
      Worlds.Sorting.merge2L (Worlds.Sorting.msortL (Worlds.Sorting.evensL (a✝ :: head✝ :: t✝)))
        (Worlds.Sorting.msortL (Worlds.Sorting.evensL (head✝ :: t✝)))
  ```

* HOM — `merge2`'s homomorphism square at the two recursive results,
  with the two IHs in scope to finish it:

  ```
  ⊢ List.map e.enc
        (Sorting.merge2 (Sorting.msort (Sorting.evens (a✝ :: head✝ :: t✝)))
          (Sorting.msort (Sorting.evens (head✝ :: t✝)))) =
      Sorting.merge2 (Sorting.msort (Sorting.evens (e.enc a✝ :: e.enc head✝ :: List.map e.enc t✝)))
        (Sorting.msort (Sorting.evens (e.enc head✝ :: List.map e.enc t✝)))
  ```

Both are the registry doing its job: a missing callee square fails
closed, and the failure names exactly the square that is missing. W7's
ruling unblocks W8 with no further work — the `msort` invocations are
two four-line declarations.

(Recorded for the record: `msort`'s ODDS callee needs no square of its
own on either route — `unfold [ACL2Lean.Sorting.odds]` carries
`odds (a :: t)` to `evens t`, which is exactly where `msortL`'s own
recursion goes. The `odds` SQUARES are a separate frontier, W9.)

ORDER MATTERS HERE, and it is deliberate: the two `msort` declarations
below stand BEFORE W9's `odds` squares, which is the route wave 1
measured — `unfold [ACL2Lean.Sorting.odds]`, with no `odds` square
registered yet. Registering `odds_agree_oddsL` first would put a second
`odds`-shaped rewrite (`odds xs = oddsL xs`) into `msort`'s closer
alongside `odds`'s own equations. -/

mirror_iso% msort_agree_msortL for ACL2Lean.Sorting.msort
  vars [xs]
  square agree (Worlds.Sorting.msortL xs)
  unfold [Worlds.Sorting.msortL, ACL2Lean.Sorting.odds]

/-- info: 'ACL2Lean.MirrorProofs.msort_agree_msortL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms msort_agree_msortL

mirror_iso% msort_map_hom for ACL2Lean.Sorting.msort
  vars [xs]
  square hom list
  embed OrderedEmbed via [ord]
  unfold [ACL2Lean.Sorting.odds]

/-- info: 'ACL2Lean.MirrorProofs.msort_map_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms msort_map_hom

/-! ## W9 — `odds`'s record (a NON-RECURSIVE spec definition; now LIVE below)

`odds` is `| [] => [] | _ :: t => evens t` — the book's `(EVENS (CDR
L))`, and not recursive. The template inducts with `fun_induction`, and
Lean generates no functional induction principle for a non-recursive
definition, so BOTH classes fail before any goal exists. Verbatim, off
the real generator (the hard error fires correctly, and its lemma-set
line confirms `evens_map_hom` was resolved from the registry):

```
mirror_iso%: the square template did not close odds_map_hom.
OBSERVED: the declaration was produced but carries `sorryAx` …
```

with Lean's own underlying error:

```
No functional induction theorem for `Sorting.odds`, or function is mutually recursive
```

This is the bound W3 stage 2 already named as GENERAL rather than a
`relMode` quirk ("`odds` and `permWitness` are non-recursive spec
definitions too"), now executed on a second member of the family. The
shape of the fix is a template FALLBACK from `fun_induction` to
`fun_cases` (which does exist for a non-recursive definition and
supplies exactly the definition's own case analysis, with no induction
hypotheses and no inference) — a template capability, so a ruling, and
one that would unblock `relMode` and `permWitness` at the same time.

A SECOND, independent gap sits behind the same frontier and is worth
separating: there is no ODDS waypoint READING at all. `Imported/
Sorting.lean` carries `insertL`/`isortL`/`merge2L`/`evensL`/`msortL` but
no `oddsL`, and no waypoint driver speaks one (`how_many_evens_and_odds
_native_driver` states the odds side as `evensL t`). Writing one is not
wave-1 work: a reading is validated through `derive_sim%` against the
book function's exec, and there is no ODDS EXEC KIT — `oddsBody` exists
but there is no `oddsExec` and no `register_exec_kit% "ODDS"` (the
`msort` correctness proof walks the ODDS body inline, as
`evensExec (Logic.cdr xv)`). So the `odds` AGREE square needs an exec
kit first; the `odds` HOM square needs only the `fun_cases` fallback.

BOTH are now closed, exactly as that reading of the frontier said they
had to be. The `fun_cases` fallback is ruled and in the template
(`IsoGen`'s "the `fun_cases` fallback"); the ODDS EXEC KIT + the
own-definition reading `oddsL` are `Imported/SortingOdds.lean`
(`derive_exec% oddsExec corr odds_exec_corr` + `derive_sim% oddsExec_enc`
— the reading is validated against the real exec by the same template
gate every other reading passes, so it is not a hand correspondence).
`oddsL` is spelled `| [] => [] | _ :: t => evensL t` — its own match, NOT
`evensL xs.tail`: `evensL`'s own `List.tail` spelling is the logged
vocabulary-compliance item (W6), and this reading deliberately does not
copy it. -/

mirror_iso% odds_agree_oddsL for ACL2Lean.Sorting.odds
  vars [xs]
  square agree (Worlds.Sorting.oddsL xs)
  unfold [Worlds.Sorting.oddsL]

/-- info: 'ACL2Lean.MirrorProofs.odds_agree_oddsL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms odds_agree_oddsL

mirror_iso% odds_map_hom for ACL2Lean.Sorting.odds
  vars [xs]
  square hom list

/-- info: 'ACL2Lean.MirrorProofs.odds_map_hom' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms odds_map_hom

/-! ## W3 — `filterRel`'s record, and the PER-MODE FAMILY (now LIVE below)

The four stages above are the record; this is what closed them, and it
is the standing `(b)` ruling implemented (R-6, 2026-08-16).

THE AGREE SQUARES — a PER-CONSTRUCTOR FAMILY, one per `RelMode`. Two
machinery pieces, both in `IsoGen`:

1. **`vars` takes a CONSTRUCTOR LITERAL.** A `vars` entry that is not an
   atomic identifier is a literal, admitted only at a `.fixed`
   (closed-type, pass-through) position and only as a NULLARY
   constructor; it enters the statement as itself and binds nothing.
2. **The registry is KEYED.** That literal is the square's key, and
   several agreement squares may exist for one definition ONLY as such a
   family: a duplicate key is refused, a keyed square cannot join an
   unkeyed one, and an unkeyed one cannot join a family. The closer of a
   CALLER gets the whole family, which cannot redirect a rewrite the way
   a second GENERAL square would — each member's statement is at a
   distinct literal, so each matches only its own occurrences.

THE READINGS are `Imported/SortingModeReadings.lean`: four
DISPATCH-FREE own-definitions (`filterLtL`/`filterLteL`/`filterGtL`/
`filterGteL`), each VALIDATED by `derive_sim%` against the real `FILTER`
exec at its own literal mode. That is the piece stage 3 said was
missing — not a way to evaluate `relL`'s ground symbol comparison, but a
reading that never dispatches. The `symV` privacy blocker stands
unchanged and is simply routed around: the mode literals are re-spelled
as values in that module (same values), and three of the four dispatch
bridges cite the existing `relL_LT`/`relL_LTE`/`relL_GTE` rows directly.

THE HOM SQUARE is stage 4's measurement, declared: `OrderedEmbed`
discharges the `≤` test, and the one surviving `if false = true then …`
residual needed one more rung of the ALREADY-ADMITTED Bool/decide
plumbing family (`Bool.false_eq_true`; see `IsoGen`'s ladder table). The
mode stays a VARIABLE here — the hom square is UNKEYED, since the
homomorphism is the same statement at every mode. -/

mirror_iso% filterRel_lt_agree_filterLtL for ACL2Lean.Sorting.filterRel
  vars [.lt, ev, xs]
  square agree (Worlds.Sorting.filterLtL ev xs)
  unfold [Worlds.Sorting.filterLtL, Worlds.Sorting.lexLtB,
    ACL2Lean.Sorting.relMode, instTotalOrderSExpr, instBEqOfDecidableEq]

/-- info: 'ACL2Lean.MirrorProofs.filterRel_lt_agree_filterLtL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms filterRel_lt_agree_filterLtL

mirror_iso% filterRel_lte_agree_filterLteL for ACL2Lean.Sorting.filterRel
  vars [.lte, ev, xs]
  square agree (Worlds.Sorting.filterLteL ev xs)
  unfold [Worlds.Sorting.filterLteL, ACL2Lean.Sorting.relMode,
    instTotalOrderSExpr]

/-- info: 'ACL2Lean.MirrorProofs.filterRel_lte_agree_filterLteL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms filterRel_lte_agree_filterLteL

mirror_iso% filterRel_gt_agree_filterGtL for ACL2Lean.Sorting.filterRel
  vars [.gt, ev, xs]
  square agree (Worlds.Sorting.filterGtL ev xs)
  unfold [Worlds.Sorting.filterGtL, ACL2Lean.Sorting.relMode,
    instTotalOrderSExpr, instBEqOfDecidableEq]

/-- info: 'ACL2Lean.MirrorProofs.filterRel_gt_agree_filterGtL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms filterRel_gt_agree_filterGtL

mirror_iso% filterRel_gte_agree_filterGteL for ACL2Lean.Sorting.filterRel
  vars [.gte, ev, xs]
  square agree (Worlds.Sorting.filterGteL ev xs)
  unfold [Worlds.Sorting.filterGteL, ACL2Lean.Sorting.relMode,
    instTotalOrderSExpr]

/-- info: 'ACL2Lean.MirrorProofs.filterRel_gte_agree_filterGteL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms filterRel_gte_agree_filterGteL

section
/- THE HOM SQUARE IS STATED AT THE CALLER'S `DecidableEq` INSTANCE (R4
   wave 2c). Its ENCODED side is `filterRel` at `SExpr`, and which
   `DecidableEq SExpr` that side carries is decided by whatever instance
   is ambient where the generator elaborates the statement. Ambient here
   is `ACL2.instDecidableEqSExpr`; `qsort`'s BODY builds its `filterRel`
   applications at the spec's own `decEqOfOrder` (W3's postscript). The
   two are propositionally equal and print identically, and the square
   stated at the former does NOT fire inside `qsort`'s closer — which is
   the ONLY consumer this square has.

   So it is stated at `decEqOfOrder`, by naming that instance locally for
   this ONE declaration. Measured, and the reason this is not W3's
   postscript all over again: the postscript's tradeoff is about the four
   AGREE squares, which test EQUALITY against a `==`-spelled reading and
   stop closing at the other instance (`.lt`, `.gt`). The HOM square has
   no reading on either side — both sides are mirror vocabulary — so it
   closes at either instance (measured both ways) and there is no
   tradeoff to rule on. J-2b-4 is untouched: the four agree squares are
   NOT restated, and the fire-vs-close choice they face is still Mike's.
   `W13`'s section below carries the measurement that this is what
   `qsort_map_hom` needed. -/
attribute [local instance 5000] ACL2Lean.Sorting.decEqOfOrder

mirror_iso% filterRel_map_hom for ACL2Lean.Sorting.filterRel
  vars [fn, ev, xs]
  square hom list
  embed OrderedEmbed via [ord]
  unfold [ACL2Lean.Sorting.relMode]

/-- info: 'ACL2Lean.MirrorProofs.filterRel_map_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms filterRel_map_hom

end

/-! ## W3's POSTSCRIPT — the per-mode family does NOT fire at its only
CALL SITE (R4 wave 2b, measured; recorded, not fixed)

The four squares above are true and trio-clean, and each one is
independently useful as a statement. What wave 2b measured, and what has
to be on the record before anyone builds on them: **they cannot be
resolved as CALLEE squares inside `qsort`'s closer**, because the two
sides speak DIFFERENT `DecidableEq SExpr` instances.

`Mirrors/Sorting.lean` derives `decEqOfOrder` from the order and declares
it `local instance (priority := low)` on purpose — its docstring says
why: so that `qsort` does not acquire a `[DecidableEq α]` binder. The
mirror definitions therefore build their `filterRel` applications at
`decEqOfOrder`; `qsort.eq_2` shows it verbatim (`pp.explicit`):

```
@ACL2Lean.Sorting.filterRel α inst
  (fun a b => @ACL2Lean.Sorting.decEqOfOrder α inst a b)
  ACL2Lean.Sorting.RelMode.lt head t
```

The squares' statements are built by the generator and elaborated HERE,
where `decEqOfOrder`'s instance attribute is not in scope, so instance
synthesis finds `ACL2.instDecidableEqSExpr`:

```
@ACL2Lean.Sorting.filterRel ACL2.SExpr instTotalOrderSExpr
  ACL2.instDecidableEqSExpr ACL2Lean.Sorting.RelMode.lt ev xs
```

The two are propositionally equal (`Subsingleton`) but NOT definitionally
equal, and they PRINT IDENTICALLY without `pp.explicit` — which is why
the mismatch is worth a section. Measured, verbatim, on the caller's own
spelling:

```
example (ev : SExpr) (t : List SExpr) :
    @ACL2Lean.Sorting.filterRel SExpr instTotalOrderSExpr
        (fun a b => @ACL2Lean.Sorting.decEqOfOrder SExpr instTotalOrderSExpr a b)
        .lt ev t
      = Worlds.Sorting.filterLtL ev t := by
  simp only [filterRel_lt_agree_filterLtL]
-- error: `simp` made no progress
```

THE OBVIOUS REPAIR WAS MEASURED AND DOES NOT WORK: putting
`attribute [local instance 5000] ACL2Lean.Sorting.decEqOfOrder` above the
four declarations restates them at the caller's instance, and then the
TWO EQUALITY-TESTING modes STOP CLOSING (`.lt` and `.gt`; `.lte`/`.gte`
still close, since they never test equality). The residual is the
tell — the goal's `decide (head✝ = ev)` and the hypothesis's
`decide (head✝ = ev)` print the same and are at different instances,
so `simp_all` cannot use one on the other:

```
h✝ : (Worlds.Sorting.lexorderB ev head✝ && !decide (head✝ = ev)) = true
⊢ head✝ :: Worlds.Sorting.filterGtL ev t✝ =
    bif Worlds.Sorting.lexorderB ev head✝ && !decide (head✝ = ev) then
      head✝ :: Worlds.Sorting.filterGtL ev t✝
    else Worlds.Sorting.filterGtL ev t✝
```

(The reading's `==` comes from `instBEqOfDecidableEq ACL2.instDecidableEqSExpr`;
the goal's `decide` from `decEqOfOrder`.) So the choice is between a
square that FIRES at the call site and a square that CLOSES against the
`==`-spelled reading, and the current machinery cannot have both. That is
a SPEC-SIDE interaction (`decEqOfOrder`'s deliberate `local`/low-priority
declaration is reader-facing), so it is recorded here and left for
ruling rather than worked around. Nothing on this page depends on it —
W13's `qsort` agree square is blocked on a second, independent thing
(below), so no live square regresses.

(R4 WAVE 2c FOOTNOTE, so a reader does not read the section above as
contradicted: the HOM square `filterRel_map_hom` IS now stated at
`decEqOfOrder`, by exactly the `attribute [local instance]` this section
says does not work — because for the HOM square it DOES. The tradeoff
above is specific to the four AGREE squares, which test EQUALITY against
a `==`-spelled reading; the hom square has no reading on either side and
closes at either instance, measured both ways. The four AGREE squares
are untouched and the choice they face is still open.)

## W10 — `bnext` (LIVE, both classes) — the bubble pass

The bsort chain's one clean square pair. `Mirrors/Sorting.lean`'s `bnext`
renders the book's `BNEXT` (`(IF (CONSP X) (IF (CONSP (CDR X)) (IF
(LEXORDER (CAR X) (CAR (CDR X))) …) X) X)`) at the same access pattern as
the waypoint reading `Worlds.Sorting.bnextL`, three patterns each, so both
squares close with the wave-1/2a kit and no new ingredient at all: the
`agree` square by the order instance in the `unfold` list (W1's route,
`bif` + `cond`'s own two cases), the `hom` square by `OrderedEmbed`'s
`ord` field + `ite`'s own two cases (W4's route).

Tamper-probed, both hard-error: `bnext`'s agree square declared against
`evensL` (a misaligned reading), and the `hom` square declared over the
PLAIN `Acl2Embed` — the order-respect hypothesis is load-bearing here
exactly as it is for `insertOrd`/`merge2`. -/

mirror_iso% bnext_agree_bnextL for ACL2Lean.Sorting.bnext
  vars [xs]
  square agree (Worlds.Sorting.bnextL xs)
  unfold [Worlds.Sorting.bnextL, instTotalOrderSExpr]

/-- info: 'ACL2Lean.MirrorProofs.bnext_agree_bnextL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bnext_agree_bnextL

mirror_iso% bnext_map_hom for ACL2Lean.Sorting.bnext
  vars [xs]
  square hom list
  embed OrderedEmbed via [ord]

/-- info: 'ACL2Lean.MirrorProofs.bnext_map_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bnext_map_hom

/-! ## W11 — `Ordered` (hom LIVE; agree is ONE `Bool`/`Prop` rung away)

`Ordered` is the first PROP-VALUED mirror definition to get a square, and
the scalar (map-INVARIANCE) class states exactly the right thing for it:
`Ordered (List.map e.enc xs) = Ordered xs`, an equality of `Prop`s. It
CLOSES over `OrderedEmbed` — the `ord` field is the whole content, as
the tamper probe over the plain `Acl2Embed` confirms (hard error) — and
it is the square the first sorting transport (`isort_ordered` at `Int`,
wave 2c) consumes.

THE AGREE SQUARE IS A RECORDED FRONTIER, one rung wide. The waypoint
reading is `Worlds.Sorting.orderedpRec` (the `chain2Rec lexorderB` fold
every ORDEREDP row speaks), and the square must be stated as the `Prop`
`orderedpRec xs = true`. Declared and measured (`.tmp`, not declared
here) as

```
  mirror_iso% ordered_agree_orderedpRec for ACL2Lean.Sorting.Ordered
    vars [xs]
    square agree (Worlds.Sorting.orderedpRec xs = true)
    unfold [ACL2.Lifting.chain2Rec, instTotalOrderSExpr]
```

cases 1 and 2 close; case 3's residual is verbatim:

```
ih1✝ : Sorting.Ordered (head✝ :: t✝) = (Worlds.Sorting.orderedpRec (head✝ :: t✝) = true)
⊢ (Worlds.Sorting.lexorderB a✝ head✝ = true ∧ Worlds.Sorting.orderedpRec (head✝ :: t✝) = true) =
    ((Worlds.Sorting.lexorderB a✝ head✝ && Lifting.chain2Rec Worlds.Sorting.lexorderB (head✝ :: t✝)) = true)
```

— i.e. the two sides are the same statement modulo ONE rung,
`Bool.and_eq_true` (`(a && b) = true ↔ a = true ∧ b = true`): the mirror
spells the adjacent-pair chain as a `Prop` conjunction and the reading
spells it as a `Bool` `&&`. That rung is the SAME Bool/`Prop` coercion
family as the already-admitted `Bool.decide_eq_true` and
`Bool.false_eq_true` — but the ladder's table lists it BY NAME in the
deliberately-NOT-admitted column (`IsoGen.lean`), so taking it is a
RULING and wave 2b does not take it. Recorded, with the measurement, so
the ruling can be made on evidence.

**WAVE 2c (DECISION O-3): the rung joined the family and the agree
square is LIVE below.** The rung is admitted BACKWARDS (`←`) — the
direction that merges the mirror's `Prop` conjunction into the
reading's single `Bool` equation. Adding it forwards was measured and
REGRESSES two live squares (the `filterRel` `.lt`/`.gt` agree squares,
whose own case hypothesis is a `(a && b) = true` the forward rung
splits apart); the full measurement is in `IsoGen`'s ladder section.
The unfold list gains `Worlds.Sorting.orderedpRec` — the reading is an
`abbrev` for `chain2Rec lexorderB`, and unfolding it is what makes the
induction hypothesis's `orderedpRec (head✝ :: t✝)` meet the goal's
`chain2Rec` spelling. -/

mirror_iso% ordered_agree_orderedpRec for ACL2Lean.Sorting.Ordered
  vars [xs]
  square agree (Worlds.Sorting.orderedpRec xs = true)
  unfold [Worlds.Sorting.orderedpRec, ACL2.Lifting.chain2Rec,
    instTotalOrderSExpr]

/-- info: 'ACL2Lean.MirrorProofs.ordered_agree_orderedpRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ordered_agree_orderedpRec

mirror_iso% ordered_map_invariant for ACL2Lean.Sorting.Ordered
  vars [xs]
  square hom scalar
  embed OrderedEmbed via [ord]

/-- info: 'ACL2Lean.MirrorProofs.ordered_map_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ordered_map_invariant

/-! ## W12 — `relMode` (hom LIVE; the agree FAMILY is a template frontier)

The book's `REL`. Its map-INVARIANCE square — `relMode fn (e.enc i)
(e.enc j) = relMode fn i j` — is the four-mode statement that the
comparison verdict does not change under an order-respecting embedding,
and it CLOSES: `ord` discharges the two `≤` tests, `enc_inj_iff` the two
equality tests, and `fun_cases` (W9's fallback — `relMode` is
NON-RECURSIVE) supplies the mode analysis. Over the plain `Acl2Embed` it
fails closed (tamper-probed).

THE PER-MODE AGREE FAMILY IS A RECORDED FRONTIER, and it is a NEW finding
about the interaction of wave 2a's two mechanisms rather than a missing
lemma. `vars [.lt, i, j]` keys the square at a constructor literal, and
for `filterRel` that works because the induction runs on the LIST and the
mode is only carried. For `relMode` the definition's OWN MATCH IS ON THE
KEYED POSITION, and the `fun_cases` fallback GENERALIZES it: from the
statement `relMode .lt i j = lexLtB i j` it produces FOUR cases, one per
`RelMode` constructor, with the right-hand side left at `lexLtB`.
Measured, verbatim — case 1 (`.lt`) closes, the other three are the other
modes compared against `'LT`'s reading:

```
case case2  ⊢ Worlds.Sorting.lexorderB i j = (Worlds.Sorting.lexorderB i j && !decide (i = j))
case case3  ⊢ (Worlds.Sorting.lexorderB j i && !decide (i = j)) = (Worlds.Sorting.lexorderB i j && !decide (i = j))
case case4  ⊢ Worlds.Sorting.lexorderB j i = (Worlds.Sorting.lexorderB i j && !decide (i = j))
```

Those goals are FALSE, and the template is right to refuse them: the
declaration as written asks for a statement about all four modes. Closing
the family would need the template to REFINE the case analysis at the
keyed literal instead of generalizing it — a template capability, i.e. a
ruling, and the exact mirror image of the split ruled at W7. Nothing
depends on it: `filterRel`'s own per-mode agree family already exists, so
`relMode`'s would be a second route to the same place. -/

mirror_iso% relMode_map_invariant for ACL2Lean.Sorting.relMode
  vars [fn, i, j]
  square hom scalar
  embed OrderedEmbed via [ord]
  unfold [ACL2Lean.Sorting.relMode]

/-- info: 'ACL2Lean.MirrorProofs.relMode_map_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relMode_map_invariant

/-! ## W13 — `qsort`'s record: the hom square is ONE RUNG away; the agree
square is blocked on the READING (R4 wave 2b, measured, nothing declared)

**THE HOM SQUARE — one ingredient, and it is a LEMMA rung, not a
capability.** Declared as

```
  mirror_iso% qsort_map_hom for ACL2Lean.Sorting.qsort
    vars [xs]
    square hom list
    embed OrderedEmbed via [ord]
```

case 1 closes and case 2's residual is verbatim (the two IHs are exactly
the two halves of the goal):

```
ih2✝ : List.map e.enc (Sorting.qsort (Sorting.filterRel Sorting.RelMode.lt head✝ t✝)) =
    Sorting.qsort (Sorting.filterRel Sorting.RelMode.lt (e.enc head✝) (List.map e.enc t✝))
ih1✝ : List.map e.enc (Sorting.qsort (Sorting.filterRel Sorting.RelMode.gte head✝ t✝)) =
    Sorting.qsort (Sorting.filterRel Sorting.RelMode.gte (e.enc head✝) (List.map e.enc t✝))
⊢ List.map e.enc
      (Sorting.qsort (Sorting.filterRel Sorting.RelMode.lt head✝ t✝) ++
        head✝ :: Sorting.qsort (Sorting.filterRel Sorting.RelMode.gte head✝ t✝)) =
    Sorting.qsort (Sorting.filterRel Sorting.RelMode.lt (e.enc head✝) (List.map e.enc t✝)) ++
      e.enc head✝ :: Sorting.qsort (Sorting.filterRel Sorting.RelMode.gte (e.enc head✝) (List.map e.enc t✝))
```

The whole distance is `List.map_append` — `List.map_cons` (already in the
kit) handles the `head✝ ::`, the two IHs handle the recursive calls, and
what is left is pushing `List.map e.enc` through the `++`. That is the
MAP-HOMOMORPHISM SQUARE OF `++` itself, structurally identical to the
generated `app_map_hom` one book up (`MirrorProofs/Basics.lean`) — but
`Mirrors/Sorting.lean` writes the append as the LIBRARY `++` (permitted
by the vocabulary practice as unambiguous operator notation), so its
square is a library lemma and not something the registry can hold.

Both repairs were measured and BOTH are rulings, so wave 2b took
neither:

1. `List.map_append` as a fixed-kit rung. It is named BY EXAMPLE in the
   ladder's deliberately-NOT-admitted column (`IsoGen.lean`, the
   `List.map_nil/cons` row) because it RELATES TWO OPERATIONS, which is
   the criterion's content test. The counter-argument on the record: it
   is precisely the refinement square of `++`, i.e. the same character as
   a REGISTERED CALLEE SQUARE rather than a content lemma.
2. A generated square FOR `List.append`. `mirror_iso% listAppend_map_hom
   for List.append vars [xs, ys] square hom list` ELABORATES AND CLOSES
   by the fixed template (receipt `[propext]`) — the template has no
   trouble with a library definition. It does not help as things stand,
   for two separate reasons, both measured: (a) `qsort`'s value does not
   mention `List.append` at all (its used constants carry
   `HAppend.hAppend` and `List.instAppend`), so callee resolution never
   finds it; and (b) the generated statement is spelled `xs.append ys`
   while the goal is spelled `xs ++ ys`, and `simp only` with it reports
   "made no progress" on the `++` form. Making that route work is a
   callee-resolution widening PLUS a notation decision — more machinery
   than route 1, for the same square.

**WAVE 2c TOOK ROUTE 2 (DECISION O-2), and the hom square is LIVE
below.** Route 1 was declined on the record: admitting `List.map_append`
as a RUNG would put a content-shaped library lemma — one that relates
two operations — permanently in EVERY square's closer, which is the
exact channel the criterion exists to keep shut. Route 2 keeps the
content in a SQUARE, where it is generated and gated like every other.
Both of route 2's measured blockers are gone:

* (a) is the NOTATION NORMALIZATION (`IsoGen`'s section of that name):
  callee resolution reads a fixed table keyed on the notation's INSTANCE
  CONSTANT as it appears in this definition's own value
  (`List.instAppend`), resolves `List.append`'s registered square, and
  adds the notation's own PROJECTIONS (`HAppend.hAppend`,
  `Append.append` — structure projections, definitional unfoldings) so
  the goal's spelling meets the square's. It fires only when a square is
  actually registered, so nothing else on this page moved.
* (b) dissolves with it: once the goal's `++` is `List.append`, the
  square matches.

THE THIRD THING, found on contact and NOT anticipated by either wave:
with (a) and (b) fixed the residual became `X = X` — the two sides
IDENTICAL under `pp.implicit`, differing only in one instance argument.
Verbatim, the load-bearing lines (`pp.explicit`, `.tmp`):

```
⊢ @List.append SExpr
    (@Sorting.qsort SExpr instTotalOrderSExpr
      (@Sorting.filterRel SExpr instTotalOrderSExpr instDecidableEqSExpr …))
    … =
  @List.append SExpr
    (@Sorting.qsort SExpr instTotalOrderSExpr
      (@Sorting.filterRel SExpr instTotalOrderSExpr
        (fun a b => @Sorting.decEqOfOrder SExpr instTotalOrderSExpr a b) …))
    …
```

— W3's postscript exactly, now for the HOM square: the rewritten
induction hypotheses speak `instDecidableEqSExpr` (the instance ambient
where `filterRel_map_hom`'s statement was elaborated) and `qsort`'s
unfolded body speaks `decEqOfOrder`. The repair is at the SQUARE, not
the closer: `filterRel_map_hom` is now stated at the caller's instance
(see the `attribute [local instance]` and its comment at that
declaration). That does NOT reopen J-2b-4 — the four AGREE squares are
untouched and their fire-vs-close tradeoff is still Mike's; the HOM
square has no reading on either side, so it closes at either instance
and there is nothing to trade.

**THE AGREE SQUARE — blocked on the READING, twice over.** Declared
against the existing waypoint reading `Worlds.Sorting.qsortL`, case 1
closes and case 2's residual is verbatim:

```
ih2✝ : Sorting.qsort (Sorting.filterRel Sorting.RelMode.lt head✝ t✝) =
    Worlds.Sorting.qsortL (Sorting.filterRel Sorting.RelMode.lt head✝ t✝)
ih1✝ : Sorting.qsort (Sorting.filterRel Sorting.RelMode.gte head✝ t✝) =
    Worlds.Sorting.qsortL (Sorting.filterRel Sorting.RelMode.gte head✝ t✝)
⊢ Worlds.Sorting.qsortL (Sorting.filterRel Sorting.RelMode.lt head✝ t✝) ++
      head✝ :: Worlds.Sorting.qsortL (Sorting.filterRel Sorting.RelMode.gte head✝ t✝) =
    Worlds.Sorting.qsortL (head✝ :: t✝)
```

Note what is NOT missing: no `List.map_append` here, because the `++` is
on both sides. Two things are:

* **DEPTH.** The mirror `qsort` matches TWO patterns (`[]`, `p :: t`);
  `qsortL` matches THREE (`[]`, `[a]`, `a :: b :: t`, mirroring the
  book's `(if (consp x) (if (consp (cdr x)) … ) …)`). So `qsortL (head✝
  :: t✝)` is STUCK at a variable tail — the W6 (`evens`) mismatch again,
  but in the direction the `unfold [List.tail]` trick cannot repair, and
  with no guarded equation for the W7 split to fire on.
* **THE PER-MODE FAMILY DOES NOT FIRE** (W3's postscript above): the four
  `filterRel` agree squares are stated at `ACL2.instDecidableEqSExpr`
  while `qsort`'s body builds `decEqOfOrder`, which is why `filterRel`
  still appears un-rewritten in the residual above.

A DISPATCH-FREE, depth-2 reading (`qsortRL | [] => [] | a :: t =>
qsortRL (filterLtL a t) ++ a :: qsortRL (filterGteL a t)`) would fix the
depth, and its agree square would close — but it cannot be VALIDATED,
which is the gate that makes a reading admissible at all. `derive_sim%`
proves a reading against the real exec, and `qsortExec`'s body passes its
mode literals as `symV "LT"` / `symV "GTE"`, where `symV` is `private` to
`Imported/Sorting.lean`. Wave 2a's per-mode FILTER isos are keyed on
`modeLT`/`modeGTE` — the same VALUES, re-spelled in a new module, but not
the same TERMS — so they cannot meet `qsortExec`'s literals, and no
lemma bridging the two can even be STATED from outside that module.
Wave 0 recorded the `symV` privacy blocker and wave 2a routed around it;
`qsort` is where the route-around runs out. De-privatising `symV` renames
the constant and moves every proof term that mentions it, which is a
regression-net decision, not an executor edit. (Wave 2c did NOT attempt
the agree square: it is held for Mike, and nothing above changes either
of its two blockers.)

**Q4's MEASUREMENT (2026-08-18) — the decide-instance-irrelevance route
does NOT dissolve the mismatch, and the square would not close even if
it did.** Mike asked for a measurement, not a fix, and here it is.

1. THE MISMATCH IS NOT AT A `decide`. Re-measured with `pp.explicit`,
   `qsort`'s own body carries `filterRel` at

   ```
   @Sorting.filterRel SExpr instTotalOrderSExpr
     (fun a b => @Sorting.decEqOfOrder SExpr instTotalOrderSExpr a b)
     Sorting.RelMode.lt head✝ t✝
   ```

   — the difference from the registered squares is `filterRel`'s own
   `DecidableEq` INSTANCE ARGUMENT (an eta-expanded `decEqOfOrder`
   against `ACL2.instDecidableEqSExpr`), one level ABOVE any `decide`
   application. A `decide`-level fact cannot reach an instance argument
   of `filterRel`.
2. THE FACT AS STATED IS NOT A REWRITE RULE. `∀ p i₁ i₂, @decide p i₁ =
   @decide p i₂` has an RHS variable the LHS does not determine; on a
   goal that IS a two-instance `decide` mismatch
   (`@decide (a = b) (decEqOfOrder a b) = @decide (a = b)
   (instDecidableEqSExpr a b)`) `simp only` reports "made no progress".
3. NOR IS THE CANONICALIZING VARIANT. `@decide p i = @decide p inst`
   with the RHS instance INSTANCE-IMPLICIT is well-formed, but simp
   solves that binder by SYNTHESIS rather than by matching, so its LHS
   only ever matches the canonical spelling — "made no progress" on the
   same goal. Applying either alongside
   `filterRel_lt_agree_filterLtL` to the real term likewise makes no
   progress.
4. AND THE SQUARE WOULD STILL NOT CLOSE. The DEPTH blocker is
   independent and untouched: the residual's right-hand side is
   `Worlds.Sorting.qsortL (head✝ :: t✝)`, which has no applicable
   equation at a variable tail (the reading matches three patterns, the
   mirror two) and survives the closer's own `unfold` of `qsortL`.

So no new product landed from this route. The two recorded routes
(J-2b-4's restatement at the caller's instance, which breaks the
`.lt`/`.gt` squares; J-2b-5's `symV` de-privatisation) are unchanged
and remain Mike's.

**R4 WAVE 2d POSTSCRIPT — the DEPTH blocker is solved, J-2b-5 is
REFUTED, and J-2b-4 is now the ONLY thing left.** The full measurement
(the depth-2 dispatch-free reading, the `symV` re-spelling that proves
by `rfl` from outside this module, the instance-irrelevance fact that
dissolves J-2b-4 and the reason it cannot be PLACED) is on the product
page, `MirrorProofs/Sorting.lean`, under "R4 WAVE 2d — THE FRONTIERS
RE-MEASURED". Nothing here changed. -/

/-- The APPEND homomorphism square (decision O-2). `List.append` is a
    LIBRARY FUNCTION, and its square is legal machinery — the collision
    rule governs mirror SPEC names, and this is not one. The square
    itself is the same artifact `mirror_iso%` generates for any callee:
    the statement is built from `List.append`'s own type, the proof is
    the fixed template, and its receipt is the plain `[propext]`. It is
    registered so `qsort`'s closer can resolve it (through the notation
    normalization — `qsort` spells the call `++`). -/
mirror_iso% listAppend_map_hom for List.append
  vars [xs, ys]
  square hom list

/-- info: 'ACL2Lean.MirrorProofs.listAppend_map_hom' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms listAppend_map_hom

mirror_iso% qsort_map_hom for ACL2Lean.Sorting.qsort
  vars [xs]
  square hom list
  embed OrderedEmbed via [ord]

/-- info: 'ACL2Lean.MirrorProofs.qsort_map_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qsort_map_hom

/-! ## W14 — `bsort`'s record: BOTH squares blocked, and NOT on the exec
kit (R4 wave 2b, measured, nothing declared)

**SUPERSEDED IN PART BY THE Q2 RE-RENDER (2026-08-18) — read the
postscript at the end of this section first.** The access-pattern
diagnosis below was correct and was escalated as a SPEC question; Mike
ruled the re-render, the spec now recurses to the fixpoint on the
book's own measure, and the blocker MOVED. Everything below is kept as
the record of what was measured when.

The wave-0/A5 inventory said `bsort` "needs the bsort exec kit and the
bnext-size measure row, the M3-class ExecGen widening or a hand kit".
Wave 2b measured the chain and reports a different conclusion: **the exec
kit is not on the critical path, and building it now would be the banned
"infrastructure now, wire it later"** — because BOTH `bsort` squares fail
for a reason the kit cannot touch.

WHAT THE SPEC RENDERS. `Mirrors/Sorting.lean`'s `bsort` is
`(List.range xs.length).foldl (fun acc _ => bnext acc) xs` — `length`-many
bubble passes, a total definition needing no termination argument. The
book's `BSORT` is the FIXPOINT recursion, verbatim from the log
(`acl2_samples/sorting/bsort.proof-log`):

```
(:DEFUN BSORT :FORMALS (X) :BODY (IF (EQUAL (BNEXT X) X) X (BSORT (BNEXT X)))
        :MEASURE (BNEXT-SIZE X) :WFREL O< :MEASURED (X)
        :TERMINATION-RUNES (… (:LINEAR HOW-MANY-BAD-PAIRS-BNEXT) …))
```

Those are DIFFERENT ACCESS PATTERNS, and under the data-refinement frame
(`IsoGen.lean`) that is exactly when there is no commuting square to
state. The `hom` square shows it directly — `fun_cases` gives one case
and the residual is the whole equation:

```
⊢ List.map e.enc (List.foldl (fun acc x => Sorting.bnext acc) xs (List.range xs.length)) =
    List.foldl (fun acc x => Sorting.bnext acc) (List.map e.enc xs) (List.range (List.map e.enc xs).length)
```

— which needs `List.length_map` plus a `map`/`foldl` fusion lemma, i.e.
library content about `foldl` and `range`, not a refinement square of
anything the book defines. The `agree` square has no reading to be stated
against at all: there is no `bsortL`, and the catalogue has said so for
months (`Imported/Waypoints/Catalog.lean`, `BSORT-IS-ISORT` and
`ORDEREDP-BSORT`: "the waypoint native … is NOT BUILT — queued behind the
mirror buildout AND the bsort exec kit").

WHY THE KIT IS NOT THE UNLOCK, measured against `Imported/ExecGen.lean`
and `Replay/MeasureTable.lean`: `BNEXT-SIZE` is the `userFn` row's corpus
witness, and `derive_exec%`'s M3 frontier is named for exactly this shape
("a measure shape outside v1 (M3: decrease through a defined function)").
But the M3 widening is not what is missing. A Lean `bsortExec` recursing
on `bnextExec x` needs its OWN Lean termination proof, and the fact it
needs is `bnextSizeExec (bnextExec x) < bnextSizeExec x` under the guard —
which IS the book's `HOW-MANY-BAD-PAIRS-BNEXT`, and whose only Lean form
in this tree is `how_many_bad_pairs_bnext_native_of_replayed`
(`Imported/SortingBsort.lean`), carrying world and `hreplayed`
hypotheses that a definition's termination proof cannot discharge. So the
kit is a HAND kit under the P2 (Lean-termination-necessity) exception —
a real, self-contained piece of work — and completing it would still
leave BOTH squares above exactly where they are, because the blocker is
the spec's rendering, not the kit.

RECORDED AS A SPEC QUESTION, deliberately not touched: rendering the
mirror `bsort` as the book's fixpoint recursion would make the squares
stateable, and `Mirrors/Sorting.lean`'s own header permits the
termination proof Lean's kernel would demand ("the only proofs here are
the termination measures Lean's kernel demands for the definitions to
exist"). That is reader-facing, so it is Mike's call, not this wave's.

**POSTSCRIPT — THE RE-RENDER LANDED (ruling Q2, 2026-08-18), AND THE
BLOCKER MOVED (R4 wave 2d-prep, measured, still nothing declared).**
The spec's `bsort` is now
`if bnext xs = xs then xs else bsort (bnext xs)`, `termination_by
howManyBadPairs xs`, with the decrease proved in the spec from the
book's own measure (`howManySmaller`/`howManyBadPairs` — the same
obligation ACL2 discharges at `BSORT`'s admission via
`HOW-MANY-BAD-PAIRS-BNEXT`). The access-pattern objection above is
therefore GONE: the mirror and the book now recurse the same way, so a
commuting square IS stateable. Neither square landed, for two NEW
reasons, both measured:

* the HOM square hits a LOOPING CLOSER. `fun_induction` unfolds the
  LEFT occurrence, but the right-hand `bsort (List.map e.enc xs)` stays
  folded, and the closer's `simp_all only [… bsort …]` unfolds a
  fixpoint recursion forever. Lean says so directly — `Possibly looping
  simp theorem: Sorting.bsort.eq_1`, then `(deterministic) timeout at
  whnf`. Controlling that would need the closer to use the case
  hypothesis BEFORE the definition's own equation, i.e. a template
  capability (a ruling), not a rung.
* the AGREE square still has NO READING to be stated against: there is
  no `bsortL` in the tree, and the catalogue still records the BSORT
  waypoint native as not built.

## W15/W16 — `Permuted` and `permWitness`: the two remaining definitions

**BOTH ARE NOW LIVE, AND BOTH RECORDS BELOW ARE SUPERSEDED.** Kept
verbatim because they are the measurements the rulings were made on —
Q1's `Permuted` re-render, and the close-out arc's `hom elem` class —
and because each names a shape that is still refused. The live squares
are on `MirrorProofs/SortingPermSquares.lean` (W15 both classes since
wave 2d; W16 agree since wave 2d, hom since the close-out arc's
`ValueOrNilEmbed` route).

**W15 AND W16 BOTH MOVED (2026-08-18 / close-out arc item 2).**
`Permuted` was RE-RENDERED (ruling Q1) and `permWitness`'s `(CAR Y)` arm
after it; each definition's whole record — waves 2b/2c's measurements
against the OLD bodies, the live squares, the `memb`/`rm` squares the
re-render introduced, and W16's wave-2b `List.find?` measurement with
its two verbatim residuals — is on
`MirrorProofs/SortingPermSquares.lean`, next to the squares it is
about. Nothing is left here but the wave-2c parenthetical below.

(R4 WAVE 2c re-measured `Permuted`'s two squares — including against
own-definition TWINS of the `contains`/`erase`/`isPerm` readings — and
found the blocker is NOT the reading layer at all but the SPEC's own
`∈`/`List.erase`/`= []` vocabulary. The residuals and the conclusion are
on the products page, `MirrorProofs/Sorting.lean`, under "THE TRANSPORT
FRONTIERS", because that is where the perm mirrors they block are
recorded.)
-/

end ACL2Lean.MirrorProofs
