import ACL2Lean.Imported.Waypoints.Macro
import ACL2Lean.Imported.Waypoints.PermBook
import ACL2Lean.DevLoad

namespace ACL2.Imported.Waypoints

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! ## The ordered-perms book — the SORTING WAYPOINT PROGRAM's first tranche
(sorting-completion-2 amended criteria). The `Imported/Sorting.lean`
support: the LEXORDER Bool kit + the ORDEREDP chain2 instance; `rm`'s
simulation is the perm book's, reused verbatim. -/

private def orderedPermsLog : String :=
  include_str "../../../acl2_samples/sorting/ordered-perms.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def orderedPermsDev : Development :=
  load_development% orderedPermsLog

derive_world orderedPermsWorldD from orderedPermsDev

/-- The UNCONDITIONAL driver replayed statement (zero hypotheses — see the
    coverage row). -/
replayed_theorem orderedpRmReplayed := driver_replayed% orderedPermsDev orderedPermsWorldD
  "orderedp-rm"

/-- ENTRY, PROVED — ORDEREDP-RM natively: erasing an element preserves
    adjacent-pair lexorder-sortedness (`chain2Rec lexorderB`, the ORDEREDP
    reading over encoded lists). -/
theorem orderedp_rm_native_driver (ev : SExpr) (xs : List SExpr)
    (h : Worlds.Sorting.orderedpRec xs = true) :
    Worlds.Sorting.orderedpRec (xs.erase ev) = true :=
  Worlds.Sorting.orderedp_rm_native_of_replayed orderedPermsWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) orderedpRmReplayed ev xs h

#print axioms orderedp_rm_native_driver

/-- The UNCONDITIONAL driver replayed statement for CAR-RM. -/
replayed_theorem carRmReplayed := driver_replayed% orderedPermsDev orderedPermsWorldD
  "car-rm"

/-- ENTRY, PROVED — CAR-RM natively: the head of `xs.erase ev` — nil on
    the empty list, the tail's head if the head was erased, else the
    head (`carRmSpec`). -/
theorem car_rm_native_driver (ev : SExpr) (xs : List SExpr) :
    (xs.erase ev).headD SExpr.nil = Worlds.Sorting.carRmSpec ev xs :=
  Worlds.Sorting.car_rm_native_of_replayed orderedPermsWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    carRmReplayed ev xs

#print axioms car_rm_native_driver

/-- The driver's CONDITIONAL replayed statement for EQUAL-CONS (one
    hypothesis: `rule:CONS-CAR-CDR`, the stored ground-zero rule). -/
replayed_theorem equalConsReplayedCond := driver_replayed% orderedPermsDev
  orderedPermsWorldD "equal-cons"

/-- The unconditional form — the ground-zero rule now discharged inside
    the driver via its D5 prelude constant (`gz_rule_cons_car_cdr`). -/
theorem equalConsReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f orderedPermsWorldD env
      Worlds.Sorting.equal_consFormula = some v ∧ v ≠ SExpr.nil :=
  equalConsReplayedCond env

/-- ENTRY, PROVED — EQUAL-CONS natively: equality with a cons decomposes
    componentwise (`==` over SExpr). -/
theorem equal_cons_native_driver (av bv xv : SExpr) :
    (SExpr.cons av bv == xv) = Worlds.Sorting.equalConsSpec av bv xv :=
  Worlds.Sorting.equal_cons_native_of_replayed orderedPermsWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide)
    equalConsReplayed_uncond av bv xv

#print axioms equal_cons_native_driver

-- v4.33 (4.31 #13030): the heartbeat counter now also counts allocations
-- (the release notes' own guidance is a 20–50% budget bump); this replay sat
-- just under the 200000 default and now trips it at an `isDefEq`.
-- hb guard (2026-08-19 sweep): measured 19k units, bound 400k — 21x margin.
-- UNRESOLVED, recorded not smoothed over: 19k is 10x UNDER the 200 000
-- default, so the measured per-command cost does NOT explain the trip this
-- raise was added for, and a standalone `lake env lean` run of this module
-- with the raise deleted elaborates clean. The trip is reproducible only
-- under the full `lake build`, i.e. it is an accounting effect (async
-- elaboration / compilation-phase heartbeats) rather than a cost. Kept
-- because it fixes an observed real-build failure; see TODO
-- "heartbeat/recursion-limit raises" for the narrowed residue.
set_option maxHeartbeats 400000 in
/-- TRUE-LISTP-RM's replayed statement (unconditional) — registered so the
    capstone's `rule:TRUE-LISTP-RM` discharge takes the registry route
    (its re-replay inside the consumer telescope frontiers). -/
replayed_theorem trueListpRmReplayed := driver_replayed% orderedPermsDev
  orderedPermsWorldD "true-listp-rm"

-- hb guard (2026-08-19 sweep): measured 628k units, bound 3.2M — 5x margin
set_option maxHeartbeats 3200000 in
/-- The driver's CONDITIONAL replayed statement for ORDERED-PERMS — the
    book's capstone (deps: the perm book, riding the 2a trees + P3
    cross-rules channels; the equivrefl and ORDEREDP-MEMB conditions
    discharge there; TRUE-LISTP-RM via the macro registry — leaving the
    two ground-zero rules). -/
replayed_theorem orderedPermsCapReplayedCond := driver_replayed% orderedPermsDev
  orderedPermsWorldD "ordered-perms" deps [permDev]

/-- The unconditional form — the two ground-zero rules now discharged
    inside the driver via their D5 prelude constants. -/
theorem orderedPermsCapReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f orderedPermsWorldD env
      Worlds.Sorting.ordered_permsFormula = some v ∧ v ≠ SExpr.nil :=
  orderedPermsCapReplayedCond env

/-- ENTRY, PROVED — ORDERED-PERMS natively: for lexorder-sorted lists,
    equality IS permutation-equivalence (the Bool identity).

    Stated in the OWN-DEFINITION `permL` vocabulary since R4 wave 2d
    (O-6): this is the native the `ordered_perm_unique` mirror meets,
    and a mirror agree square must face an own-definition reading. -/
theorem ordered_perms_native_driver (xs ys : List SExpr)
    (hx : Worlds.Sorting.orderedpRec xs = true)
    (hy : Worlds.Sorting.orderedpRec ys = true) :
    (xs == ys) = Worlds.Sorting.permL xs ys := by
  rw [Worlds.Sorting.permL_eq_isPerm]
  exact Worlds.Sorting.ordered_perms_native_of_replayed orderedPermsWorldD
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    orderedPermsCapReplayed_uncond xs ys hx hy

/-- The same fact as the IMPLICATION, in the book's own `PERM`
    vocabulary — a DECODE-SHAPE corollary of the native above (the Bool
    identity read as "sorted permutations are equal"), in the same class
    as the `List.Perm` corollary below and carrying no content of its
    own. It exists because that is the shape `ordered_perm_unique`'s
    crossing meets. -/
theorem ordered_perms_eq_driver (xs ys : List SExpr)
    (hx : Worlds.Sorting.orderedpRec xs = true)
    (hy : Worlds.Sorting.orderedpRec ys = true)
    (hp : Worlds.Sorting.permL xs ys = true) : xs = ys := by
  have h := ordered_perms_native_driver xs ys hx hy
  rw [hp] at h
  exact beq_iff_eq.mp h

/-- The same fact as the EQUIVALENCE, in the book's own `PERM`
    vocabulary — the Bool identity `(xs == ys) = permL xs ys` read as
    the `Iff` it is, which is what ORDERED-PERMS literally says
    (`(EQUAL (EQUAL A B) (PERM A B))`). Another DECODE-SHAPE corollary
    of the native above, in the class of the two below and carrying no
    content of its own; it exists because that is the shape
    `ordered_perm_unique`'s crossing meets. -/
theorem ordered_perms_iff_driver (xs ys : List SExpr)
    (hx : Worlds.Sorting.orderedpRec xs = true)
    (hy : Worlds.Sorting.orderedpRec ys = true) :
    xs = ys ↔ Worlds.Sorting.permL xs ys = true := by
  have h := ordered_perms_native_driver xs ys hx hy
  constructor
  · intro he; rw [← h, he, beq_self_eq_true]
  · intro hp; rw [hp] at h; exact beq_iff_eq.mp h

/-- The idiomatic corollary over `List.Perm`: sorted permutations are
    EQUAL. -/
theorem ordered_perms_native_perm_driver (xs ys : List SExpr)
    (hx : Worlds.Sorting.orderedpRec xs = true)
    (hy : Worlds.Sorting.orderedpRec ys = true)
    (hp : xs.Perm ys) : xs = ys := by
  have h := ordered_perms_native_driver xs ys hx hy
  rw [Worlds.Sorting.permL_eq_isPerm, List.isPerm_iff.mpr hp] at h
  exact beq_iff_eq.mp h

#print axioms ordered_perms_native_driver
#print axioms ordered_perms_native_perm_driver

-- hb guard (2026-08-19 sweep): measured 430k units, bound 1.6M — 4x margin
set_option maxHeartbeats 1600000 in
/-- The driver's CONDITIONAL replayed statement for ORDEREDP-MEMB (one
    hypothesis: `rule:DEFAULT-CAR`). The raised heartbeat budget covers
    the replay-time `isDefEq` pinning over this row's larger tree. -/
replayed_theorem orderedpMembReplayedCond := driver_replayed% orderedPermsDev
  orderedPermsWorldD "orderedp-memb"

/-- The unconditional form — `rule:DEFAULT-CAR` now discharged inside
    the driver via its D5 prelude constant. -/
theorem orderedpMembReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f orderedPermsWorldD env
      Worlds.Sorting.orderedp_membFormula = some v ∧ v ≠ SExpr.nil :=
  orderedpMembReplayedCond env

/-- ENTRY, PROVED — ORDEREDP-MEMB natively: an element strictly below the
    head of a lexorder-sorted list is not in the list. -/
theorem orderedp_memb_native_driver (ev a : SExpr) (t : List SExpr)
    (hord : Worlds.Sorting.orderedpRec (a :: t) = true)
    (hne : (ev == a) = false)
    (hlex : Worlds.Sorting.lexorderB ev a = true) :
    (a :: t).contains ev = false :=
  Worlds.Sorting.orderedp_memb_native_of_replayed orderedPermsWorldD
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) orderedpMembReplayed_uncond
    ev a t hord hne hlex

#print axioms orderedp_memb_native_driver

end ACL2.Imported.Waypoints
