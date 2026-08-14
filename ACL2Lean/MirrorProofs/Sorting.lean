import ACL2Lean.MirrorProofs.IsoGen
import ACL2Lean.Mirrors.Sorting

/-! # MIRROR PROOFS — the sorting book (the WITNESS PAGE, not yet a proof page)

`ACL2Lean/Mirrors/Sorting.lean`'s Props are the buildout's north star; NONE
of them is proved yet (R4's scope). This page exists because R1 item B
widened `mirror_iso%`'s ARGUMENT-READING table (audit finding F1) and that
widening had to land against REAL square declarations read off the sorting
spec — not against a test fixture (the anti-"infrastructure now, wire it
later" rule). It is therefore the landing zone for the sorting squares, and
today it carries exactly one LIVE declaration: the function-argument
frontier, pinned.

## What R1-B changed

Before: `mirror_iso%` collapsed a mirror definition's binder telescope to
one `allList` boolean and hard-errored on ANY non-list explicit argument —
so every sorting definition with an ELEMENT argument (`insertOrd (a : α)`,
`howMany (a : α)`) was rejected by the SHAPE TABLE, before its statement was
ever built. After: the telescope is read into a per-binder READING VECTOR
inferred from the spec's own Lean binder types (`List α` ↦ enters under
`List.map e.enc`; `α` ↦ enters under `e.enc`), with no new user syntax.

## The three witnesses, and what each one established

**W1 `insertOrd (a : α) : List α → List α`** — the audit's executed reject.
It passes the shape table (`.elem`, `.list`) and the statement builder. Its
frontier MOVED during this arc, in two recorded stages:

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
`agree` square vs `Worlds.Sorting.insertL` ELABORATES its statement and
the CLOSER leaves exactly two residuals (verbatim, the two cases of the
comparison split):

```
h✝ : a ≤ head✝
⊢ a :: head✝ :: t✝ =
    bif Worlds.Sorting.lexorderB a head✝ then a :: head✝ :: t✝
    else head✝ :: Worlds.Sorting.insertL a t✝
```

(and its `¬` twin, with the `ih1✝` induction hypothesis available).
Under the instance, `a ≤ head✝` IS `lexorderB a head✝ = true`
definitionally — the residual needs the CASE HYPOTHESIS used as a rewrite
to collapse the `bif`, and the fixed ladder is `rfl`-lemmas only,
hypothesis-blind by its stated criterion. That is a LADDER-DESIGN
question (does the closer gain a hypothesis-directed Bool-reading rung?),
sanctioned in principle by the 2026-08-13 ruling ("widening seems fine" —
a design-quality speedbump; trust is the kernel's), with its concrete
shape left for the ruling batch this page's report carries. The `hom
list` square additionally needs the embedding to RESPECT the order —
`Acl2Embed` has no order field by construction ("that dimension arrives
with sorting", `IsoGen`). NOT declared live: a failing `mirror_iso%`
leaves a `sorryAx`-carrying declaration behind, which this tree does not
accept.

**W2 `howMany (a : α) : List α → Nat`** — the positive one. Its `agree`
square ELABORATES: the element binder is read as `.elem` and typed `SExpr`,
the list binder as `.list` and typed `List SExpr`, `DecidableEq SExpr` is
found, and the closer reaches a real residual goal,

```
⊢ (if a = head✝ then 1 else 0) + List.count a t✝ = List.count a (head✝ :: t✝)
```

i.e. the widening delivered a well-formed statement and the remaining
distance is the CLOSER's, not the shape table's. Two findings recorded from
it, neither actioned here:
1. The `hom scalar` CODEC is fine for a `Nat` result — that class asserts
   scalar INVARIANCE (`fn (encoded args) = fn (args)`) and carries no
   result codec at all, so `Nat` needs nothing new (`len_map_invariant` is
   already `Nat`-valued). The result-class question the charter flagged
   adjudicates CLEAN.
2. The residual goals show what element arguments cost the CLOSER, in both
   classes: the `agree` goal wants `List.count_cons` (the HOW-MANY waypoint
   reading is spelled in LIBRARY vocabulary — `xs.count e`, one of the five
   readings on the logged compliance pass), and the `hom scalar` goal wants
   the embedding's INJECTIVITY to turn `e.enc a = e.enc b` into `a = b`.
   Neither is a `rfl`-lemma, so neither is admissible to the fixed ladder
   under its stated criterion. Both are design questions for a ruling, not
   for this arc.

**W3 `filterRel (keep : α → Bool)`** — the expected named frontier, LIVE
below as the only pinned declaration on this page (it hard-errors in the
shape table, before any declaration is produced, so pinning it adds no
`sorryAx`). The pin is the deliverable: the honest statement of the reading
table's bound.

The charter-note finding that goes WITH it: the function argument is the
MIRROR SPEC's idiom, not the book's. The sorting book's FILTER is
`(filter fn x e)` — a SYMBOL-valued comparison mode plus a PIVOT ELEMENT
(`ACL2Lean/Imported/Sorting.lean`'s `filterL (fv ev : SExpr)`), and the
mirror spec renders those two as one closure (`filterRel (fun x => decide
(x < p))` in `qsort`). So "extend the reading table to function arguments"
is not the only way to reach `filterRel`, and choosing between that and
re-rendering the spec closer to the book is a PRODUCT-LAYER decision. Left
open, deliberately.
-/

namespace ACL2Lean.MirrorProofs

open ACL2 ACL2Lean

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
