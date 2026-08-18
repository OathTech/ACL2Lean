import ACL2Lean.MirrorProofs.SortingSquares
import ACL2Lean.Imported.SortingQsortReading

/-! # MIRROR PROOFS — `qsort`'s AGREE square (R4 wave 2e)

The witness page's third file. `MirrorProofs/SortingSquares.lean` carries
the sort algorithms' squares (W1–W14) and is AT the 1500-line module-size
norm; `MirrorProofs/SortingPermSquares.lean` carries the perm/measure
chain. This page carries the ONE square W13 recorded as blocked through
four waves, and the ONE fact that unblocks it.

## THE HISTORY, in one paragraph (the full record is W13, unchanged)

`qsort`'s AGREE square had TWO blockers. **DEPTH**: the mirror `qsort`
matches `[] | p :: t` while the validated reading `qsortL` matches
`[] | [a] | a :: b :: t` (the book's `(if (consp x) (if (consp (cdr x))
…))`), so the closer met `qsortL (p :: t)` at a variable tail with no
applicable equation. **THE INSTANCE ARGUMENT** (W3's postscript,
J-2b-4): the four per-mode `filterRel` agree squares are stated at
`ACL2.instDecidableEqSExpr` and `qsort`'s body builds `filterRel` at the
spec's `local` `decEqOfOrder`, so the squares are TRUE and DO NOT FIRE.

Wave 2d solved the first (a depth-1 dispatch-free reading closes case 1
and matches case 2's shapes) and PROVED the fact that dissolves the
second — but could not PLACE it: `unfold [...]` is definitions-only and
hard-errors on a lemma, and a ladder rung is impossible because the fact
names a MIRROR SPEC constant while `IsoGen.lean` imports only
`ACL2Lean.Syntax`. That placement question returned to the orchestrator
and was ruled as **O-7 (2026-08-18): the INSTANCE-FACTS CLAUSE**, an
`instances [...]` scope on the square declaration modelled exactly on
`embed … via [fields]` — shape-validated as an equality between two
INSTANCE terms of a proof-irrelevant class, reaching THAT square's closer
and nothing else. The criterion, its rationale and its honest bound are
at "the instance-facts clause" in `MirrorProofs/IsoGen.lean`.

The reading is `Worlds.Sorting.qsortOwnL`
(`Imported/SortingQsortReading.lean`), validated by composition against
the real `QSORT` exec (`qsortExec_enc_own`) — its own header states the
bound plainly, since `derive_sim%` admits one general iso per exec kit
and could not be handed a second.
-/

namespace ACL2Lean.MirrorProofs

open ACL2 ACL2Lean

/-! ## THE INSTANCE FACT

Two spellings of ONE `DecidableEq SExpr`. `Mirrors/Sorting.lean` declares
`decEqOfOrder` `local` and low-priority ON PURPOSE (so `qsort` carries no
`[DecidableEq α]` binder — its docstring says so), which is exactly why a
definition elaborated inside that file and a square elaborated outside it
disagree on an INSTANCE ARGUMENT while printing identically.

It is content-free by construction: `Decidable` is proof-irrelevant, so
the two instances were equal before this file existed and the proof is
`Subsingleton.elim`. It relates no two operations, mentions no recursion,
and cannot supply a definitional correspondence that is not there — it
can only make the two spellings meet. It is proved HERE, per invocation,
and reaches exactly the one square that names it. -/

/-- `Mirrors/Sorting.lean`'s order-derived `DecidableEq SExpr` IS the
    ambient one — proof irrelevance, nothing more. The eta-expanded
    left-hand side is the form `qsort`'s own equations carry
    (`pp.explicit`, W3's postscript). -/
theorem decEqOfOrder_eq_instSExpr :
    ((fun a b : SExpr => ACL2Lean.Sorting.decEqOfOrder a b) :
      DecidableEq SExpr) = ACL2.instDecidableEqSExpr := by
  funext a b
  exact Subsingleton.elim _ _

/-! ## W13's AGREE SQUARE — LIVE

Everything the closer uses is machinery: `qsort`'s own equations,
`qsortOwnL`'s own equations (the `unfold` list), the four REGISTERED
per-mode `filterRel` agree squares (resolved as callee squares, exactly
as they are for any other caller), and the instance fact above. No
ladder rung was added; the ladder is unchanged this wave. -/

mirror_iso% qsort_agree_qsortOwnL for ACL2Lean.Sorting.qsort
  vars [xs]
  square agree (Worlds.Sorting.qsortOwnL xs)
  unfold [Worlds.Sorting.qsortOwnL]
  instances [decEqOfOrder_eq_instSExpr]

/-- info: 'ACL2Lean.MirrorProofs.qsort_agree_qsortOwnL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qsort_agree_qsortOwnL

end ACL2Lean.MirrorProofs
