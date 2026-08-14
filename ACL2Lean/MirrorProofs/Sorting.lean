import ACL2Lean.MirrorProofs.IsoGen
import ACL2Lean.MirrorProofs.OrderBridge
import ACL2Lean.Mirrors.Sorting

/-! # MIRROR PROOFS — the sorting book (the WITNESS PAGE, not yet a proof page)

`ACL2Lean/Mirrors/Sorting.lean`'s Props are the buildout's north star; NONE
of them is proved yet (R4's scope). This page exists because R1 item B
widened `mirror_iso%`'s ARGUMENT-READING table (audit finding F1) and that
widening had to land against REAL square declarations read off the sorting
spec — not against a test fixture (the anti-"infrastructure now, wire it
later" rule). It is therefore the landing zone for the sorting squares.

After R4 WAVE 1 (2026-08-14) it carries EIGHT declarations — all LIVE
squares, each `#print axioms`-pinned:

| witness | agree | hom |
| ------- | ----- | --- |
| W1 `insertOrd` | LIVE (R1-D) | **LIVE (wave 1 — the order dimension)** |
| W2 `howMany`   | LIVE (R1-D) | LIVE (R1-D, scalar) |
| W5 `isort`     | **LIVE**    | **LIVE** |
| W6 `evens`     | **LIVE**    | **LIVE** |

and FOUR RECORDED frontiers with no declaration — W3 `filterRel`, W7
`merge2`, W8 `msort`, W9 `odds`. Nothing is emitted for a frontier on
purpose: a closer failure leaves a `sorryAx`-carrying declaration
behind, which this tree does not accept, so the state lives in this
docstring (statements verbatim, residuals verbatim, the measured closing
condition) rather than in a `#guard_msgs` pin.

The wave-1 machinery both new squares rest on is in `IsoGen`'s "the
order-respect route" (the `embed S via [...]` clause — an order-using
definition's homomorphism square is only TRUE for an order-respecting
embedding, so that hypothesis belongs in its statement) and in
`OrderBridge`'s `OrderedEmbed`/`intOrderedEmbed`. The ladder also gained
`ite`'s own two cases, the `rfl` twin of the already-admitted `cond`
pair; the line wave 1 held is that the closer grows LEMMA rungs that
meet the pinned criterion and never a CAPABILITY (W7 and W3 record the
two capabilities that were measured and not taken).

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

/-! ## W7 — `merge2`: RECORDED, not declared (the UNDESTRUCTURED-ARM bound)

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

## W8 — `msort`: RECORDED, not declared (blocked ONLY on W7)

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

## W9 — `odds`: RECORDED, not declared (a NON-RECURSIVE spec definition)

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

## W3 — `filterRel`: RECORDED, not declared

Nothing is emitted here on purpose. Both of `filterRel`'s squares now
build their STATEMENTS (the mode reads `.fixed`) and neither closes, and
a closer failure leaves a `sorryAx`-carrying declaration behind — so the
state lives in the module docstring above (statements verbatim,
residuals verbatim, the measured closing condition) rather than in a
`#guard_msgs` pin. The stage-1 pin that stood here guarded the
function-argument message; the re-render deleted the function argument,
so the pin went with it. -/

end ACL2Lean.MirrorProofs
