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
After the R1-E FILTER re-render (2026-08-14) it carries THREE
declarations — all LIVE squares, each `#print axioms`-pinned — plus W3,
a RECORDED frontier with no declaration (its statements now build; the
closer does not close them, and a closer failure would leave a
`sorryAx`-carrying declaration behind, which this tree does not
accept).

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
   `enc_inj_iff`). The ladder's pinned criterion is now "`rfl`-lemmas +
   the embedding's `inj` iff" — see `IsoGen.lean`'s ladder section for
   why that is plumbing (a square is definitional correspondence about
   OUR OWN definitions; content still arrives only via replay).
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

/-! ## W3 — `filterRel`: RECORDED, not declared

Nothing is emitted here on purpose. Both of `filterRel`'s squares now
build their STATEMENTS (the mode reads `.fixed`) and neither closes, and
a closer failure leaves a `sorryAx`-carrying declaration behind — so the
state lives in the module docstring above (statements verbatim,
residuals verbatim, the measured closing condition) rather than in a
`#guard_msgs` pin. The stage-1 pin that stood here guarded the
function-argument message; the re-render deleted the function argument,
so the pin went with it. -/

end ACL2Lean.MirrorProofs
