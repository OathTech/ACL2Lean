import ACL2Lean.Imported.Waypoints.Isort
import ACL2Lean.Imported.Waypoints.OrderedPerms

namespace ACL2.Imported.Waypoints

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! ## The idiomatic `List.IsChain` corollaries (waypoint criterion 1):
sortedness in Mathlib vocabulary — `IsChain (lexorderB · · = true)`,
adjacent-pairs order over the imported total order (LexorderOrder.lean
proves it reflexive/antisymmetric/transitive/total). -/

/-- Sortedness, idiomatically. -/
abbrev LexSorted (xs : List SExpr) : Prop :=
  xs.IsChain (fun a b => Worlds.Sorting.lexorderB a b = true)

/-- ORDEREDP-ISORT, Mathlib form: insertion sort always sorts. -/
theorem orderedp_isort_isChain_driver (xs : List SExpr) :
    LexSorted (Worlds.Sorting.isortL xs) :=
  (Worlds.Sorting.chain2Rec_iff_isChain _ _).mp
    (orderedp_isort_native_driver xs)

/-- ORDEREDP-RM, Mathlib form: erasing an element preserves
    sortedness. -/
theorem orderedp_rm_isChain_driver (ev : SExpr) (xs : List SExpr)
    (h : LexSorted xs) : LexSorted (xs.erase ev) :=
  (Worlds.Sorting.chain2Rec_iff_isChain _ _).mp
    (orderedp_rm_native_driver ev xs
      ((Worlds.Sorting.chain2Rec_iff_isChain _ _).mpr h))

/-- ORDEREDP-MEMB, Mathlib form: an element strictly below the head of a
    sorted list is not in it. -/
theorem orderedp_memb_isChain_driver (ev a : SExpr) (t : List SExpr)
    (hord : LexSorted (a :: t)) (hne : (ev == a) = false)
    (hlex : Worlds.Sorting.lexorderB ev a = true) :
    (a :: t).contains ev = false :=
  orderedp_memb_native_driver ev a t
    ((Worlds.Sorting.chain2Rec_iff_isChain _ _).mpr hord) hne hlex

#print axioms orderedp_isort_isChain_driver

end ACL2.Imported.Waypoints
