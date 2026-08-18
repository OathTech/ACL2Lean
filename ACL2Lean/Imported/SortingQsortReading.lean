import ACL2Lean.Imported.SortingModeReadings

/-! # THE DISPATCH-FREE, DEPTH-1 `QSORT` READING (R4 wave 2e)

`Imported/Sorting.lean`'s `qsortL` is the reading `derive_sim%`
VALIDATED against the real `QSORT` exec, and it has two properties that
the exec forces on it and that a MIRROR square cannot live with:

* it destructures at DEPTH 2 (`[] | [a] | a :: b :: t`), because
  `qsortExec` tests `(consp x)` and then `(consp (cdr x))` — exactly the
  book's body. The mirror `Mirrors/Sorting.lean`'s `qsort` destructures
  at DEPTH 1 (`[] | p :: t`), so `fun_induction` hands the square's
  closer `qsortL (p :: t)` at a VARIABLE tail, where no equation of
  `qsortL` applies (R4 wave 2b's recorded blocker);
* it spells its two filters as `List.filter (fun c => relL (symV "LT") c
  a)` — a runtime MODE DISPATCH inside `relL`, the same one wave 2a's
  four per-mode readings exist to remove.

This module carries the reading that has neither: `qsortOwnL`, at the
MIRROR's depth and through the four dispatch-free per-mode filters
(`Imported/SortingModeReadings.lean`).

**HOW IT IS VALIDATED, and the honest bound.** `derive_sim%` admits ONE
general iso per exec kit (a second registration for `"QSORT"` is
fail-closed by design), so this reading cannot be handed to the template
directly. It is validated instead by COMPOSITION, and the composition is
kernel-checked end to end: `qsortOwnL_eq_qsortL` below is a HAND proof by
the reading's own recursion, and `qsortExec_enc_own` restates the
template's own conclusion for it. The bound stated plainly: that one
equation is a hand correspondence where the generated one is
unavailable — the same class as the decode-kit bridges in
`Imported/SortingReadings.lean`, and in the SAFER direction, since both
sides are OWN-DEFINITIONS and no library lemma speaks about either.

**THE GUARD (the O-6 rule, applied here).** `qsortOwnL_eq_qsortL` and the
two `*_eq_filter` bridges below must NEVER join the mirror square
closer's fixed kit (`MirrorProofs/IsoGen.lean`'s ladder) nor any
square's `unfold` list: the mirror `qsort` square closes against
`qsortOwnL` and the per-mode filter squares, and a bridge in the closer
would rewrite the dispatch-free reading straight back to the dispatching
one. Checkable by
`grep -rn "qsortOwnL_eq_qsortL\|_eq_filter" ACL2Lean/MirrorProofs`
returning no code.
-/

open ACL2 ACL2.Replay ACL2.Lifting ACL2.ExecGen

namespace ACL2.Worlds.Sorting

/-! ## `qsortL`'s own equations, RE-SPELLED at the mode VALUES

`symV` is `private` to `Imported/Sorting.lean`, so `qsortL`'s equations
cannot be NAMED from here — but they can be re-STATED, because `modeLT`
and `symV "LT"` are the same value (`.atom (.symbol { name := "LT" })`)
and the two statements are therefore definitionally equal. This is
wave 2d's `qsortExec_eq_modes` finding (J-2b-5 REFUTED: `symV` never has
to be named, only re-spelled past), used one level up. -/

/-- `qsortL`'s recursive equation at the mode VALUES. -/
theorem qsortL_cons_cons (a b : SExpr) (t : List SExpr) :
    qsortL (a :: b :: t)
      = qsortL ((b :: t).filter (fun c => relL modeLT c a))
          ++ a :: qsortL ((b :: t).filter (fun c => relL modeGTE c a)) := by
  rw [qsortL.eq_def]; rfl

/-- `qsortL`'s singleton equation. -/
theorem qsortL_single (a : SExpr) : qsortL [a] = [a] := by
  rw [qsortL.eq_def]

/-- `qsortL`'s base equation. -/
theorem qsortL_nil : qsortL [] = [] := by
  rw [qsortL.eq_def]

/-! ## The per-mode filters against `List.filter` at the same mode

Bridges, DECODE-LAYER ONLY (see THE GUARD in the header). They exist to
prove `qsortOwnL_eq_qsortL` and for nothing else. -/

/-- `filterLtL` IS `List.filter` at `'LT` (the dispatch, evaluated). -/
theorem filterLtL_eq_filter (ev : SExpr) (xs : List SExpr) :
    filterLtL ev xs = xs.filter (fun c => relL modeLT c ev) := by
  induction xs with
  | nil => rfl
  | cons a t ih =>
    rw [filterLtL, List.filter_cons, relL_modeLT, ih]
    cases lexLtB a ev <;> simp

/-- `filterGteL` IS `List.filter` at `'GTE`. -/
theorem filterGteL_eq_filter (ev : SExpr) (xs : List SExpr) :
    filterGteL ev xs = xs.filter (fun c => relL modeGTE c ev) := by
  induction xs with
  | nil => rfl
  | cons a t ih =>
    rw [filterGteL, List.filter_cons, relL_modeGTE, ih]
    cases lexorderB ev a <;> simp

theorem filterLtL_length_le (ev : SExpr) (xs : List SExpr) :
    (filterLtL ev xs).length ≤ xs.length := by
  rw [filterLtL_eq_filter]; exact List.length_filter_le _ _

theorem filterGteL_length_le (ev : SExpr) (xs : List SExpr) :
    (filterGteL ev xs).length ≤ xs.length := by
  rw [filterGteL_eq_filter]; exact List.length_filter_le _ _

/-! ## The reading -/

/-- The native quicksort at the MIRROR's access pattern: pivot on the
    head, partition the TAIL with the two dispatch-free filters. Same
    function as `qsortL` (`qsortOwnL_eq_qsortL`), different — and here
    load-bearing — recursion shape. -/
def qsortOwnL : List SExpr → List SExpr
  | [] => []
  | a :: t => qsortOwnL (filterLtL a t) ++ a :: qsortOwnL (filterGteL a t)
termination_by xs => xs.length
decreasing_by
  · exact Nat.lt_succ_of_le (filterLtL_length_le _ _)
  · exact Nat.lt_succ_of_le (filterGteL_length_le _ _)

/-- THE VALIDATION, half one: the depth-1 reading IS `qsortL`.

    DECODE-LAYER ONLY — see THE GUARD in the header: this must never
    enter the mirror square closer's kit or a square's `unfold` list. -/
theorem qsortOwnL_eq_qsortL (xs : List SExpr) : qsortOwnL xs = qsortL xs := by
  fun_induction qsortOwnL xs with
  | case1 => rw [qsortL_nil]
  | case2 a t ih1 ih2 =>
    rw [ih1, ih2]
    cases t with
    | nil =>
      rw [show filterLtL a [] = [] from rfl, show filterGteL a [] = [] from rfl,
        qsortL_nil, qsortL_single]
      rfl
    | cons b t' =>
      rw [qsortL_cons_cons, filterLtL_eq_filter, filterGteL_eq_filter]

/-- THE VALIDATION, half two: the template's own conclusion, restated
    for this reading — `qsortExec` on an encoded list computes
    `qsortOwnL`. The content is `qsortExec_enc`'s (GENERATED, template
    failure = hard error); this is that theorem read through the
    equation above. -/
theorem qsortExec_enc_own (xs : List SExpr) :
    qsortExec (enc xs) = enc (qsortOwnL xs) := by
  rw [qsortOwnL_eq_qsortL]; exact qsortExec_enc xs

end ACL2.Worlds.Sorting
