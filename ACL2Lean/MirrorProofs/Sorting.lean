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
After the R1-D ruling batch (2026-08-14) it carries FOUR declarations:
three LIVE squares (each `#print axioms`-pinned) and the
function-argument frontier, pinned as the honest bound.

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

**W3 `filterRel (keep : α → Bool)`** — the expected named frontier,
pinned below (it hard-errors in the shape table, before any declaration
is produced, so pinning it adds no `sorryAx`). The pin is the
deliverable: the honest statement of the reading table's bound.

The charter-note finding that goes WITH it: the function argument is the
MIRROR SPEC's idiom, not the book's. The sorting book's FILTER is
`(filter fn x e)` — a SYMBOL-valued comparison mode plus a PIVOT ELEMENT
(`ACL2Lean/Imported/Sorting.lean`'s `filterL (fv ev : SExpr)`), and the
mirror spec renders those two as one closure (`filterRel (fun x => decide
(x < p))` in `qsort`). So "extend the reading table to function arguments"
is not the only way to reach `filterRel`, and choosing between that and
re-rendering the spec closer to the book is a PRODUCT-LAYER decision
(ruling batch item 3, deliberately NOT taken here). Left open.
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

/-! ## W3 — the function-argument frontier (pinned)

The `hom list` class is the sharp form of the question: the homomorphism
square is what an embedding has to commute with, and there is no derived
action of an element embedding on a `α → Bool` position. The receipt below
is the frontier message itself; it fires the day the reading table changes,
which is exactly when this page's owner must revisit the decision above. -/

/--
error: mirror_iso%: ACL2Lean.Sorting.filterRel's explicit argument `keep : α → Bool` is outside the ARGUMENT-READING table.
OBSERVED: binder type `α → Bool`; the definition's element type is `α`. The two derived readings are `List α` (the argument enters the homomorphism statement under `List.map e.enc`) and `α` itself (it enters under `e.enc`).
CANDIDATE CAUSES (none asserted, not ranked): (a) a FUNCTION-VALUED argument (e.g. `α → Bool`) — an `Acl2Embed` is an injection on ELEMENTS and has no action on a function position, so reading one is a design question, not something this generator may guess; (b) a NON-EMBEDDED scalar (`Nat`, `Int`, …) — the embedding does not act on it either, and whether the square should hold it fixed is the same design question; (c) a list over some OTHER type than `α`.
What this failure is NOT: a statement that the declared correspondence is wrong. The declaration never reached the statement builder — this is the reading table's own bound, and widening it is a design change to the square classes, never a hand square (thin-Lean ruling 2026-08-11).
-/
#guard_msgs (whitespace := lax) in
mirror_iso% filterRel_map_hom for ACL2Lean.Sorting.filterRel
  vars [keep, xs]
  square hom list

end ACL2Lean.MirrorProofs
