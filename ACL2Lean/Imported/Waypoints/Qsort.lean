import ACL2Lean.Imported.Waypoints.Macro
import ACL2Lean.Imported.Waypoints.ConvertPerm
import ACL2Lean.Imported.Waypoints.OrderedPerms
import ACL2Lean.Imported.SortingQsortReading
import ACL2Lean.DevLoad

namespace ACL2.Imported.Waypoints

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-! ## The qsort book — first tranche: the append rows. -/

private def qsortLog : String :=
  include_str "../../../acl2_samples/sorting/qsort.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def qsortDev : Development :=
  load_development% qsortLog

derive_world qsortWorldD from qsortDev

set_option maxHeartbeats 1600000 in
/-- The driver's CONDITIONAL replayed statement for HOW-MANY-APPEND
    (hypotheses: `tp:HOW-MANY`, `rule:NOT-MEMB-IMPLIES-HOW-MANY-IS-0`). -/
def howManyAppendReplayedCond := driver_replayed% qsortDev qsortWorldD
  "how-many-append" deps [convertPermDev]

/-- The unconditional form. -/
theorem howManyAppendReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f qsortWorldD env
      Worlds.Sorting.how_many_appendFormula = some v ∧ v ≠ SExpr.nil :=
  howManyAppendReplayedCond env


/-- ENTRY, PROVED — HOW-MANY-APPEND natively: `howManyL` distributes
    over `++`. -/
theorem how_many_append_native_driver (ev : SExpr) (xs ys : List SExpr) :
    Worlds.Sorting.howManyL ev (xs ++ ys)
      = Worlds.Sorting.howManyL ev xs + Worlds.Sorting.howManyL ev ys :=
  Worlds.Sorting.how_many_append_native_of_replayed qsortWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) howManyAppendReplayed_uncond ev xs ys

#print axioms how_many_append_native_driver

set_option maxHeartbeats 1600000 in
/-- The driver's replayed statement for CAR-APPEND — now
    UNCONDITIONAL (its one hypothesis, the if-lifting rule
    `(equal (if a b c) x)`, is discharged by the D5 registry, P4b). -/
def carAppendReplayedCond := driver_replayed% qsortDev qsortWorldD
  "car-append"

/-- The unconditional form. -/
theorem carAppendReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f qsortWorldD env
      Worlds.Sorting.car_appendFormula = some v ∧ v ≠ SExpr.nil :=
  carAppendReplayedCond env
    -- (the five arithmetic-3 runes rule:(+ y x) / (+ y (+ x z)) /
    -- (+ (+ x y) z) / (+ x (if a b c)) / (equal (if a b c) x) RETIRED,
    -- T1+2 sprint P4b 2026-08-15 — the D5 registry discharges each at its
    -- CITED rune from the prelude constant, so the hypotheses left the
    -- telescope and the hand-applied `dis_*` arguments went with them.)

/-- ENTRY, PROVED — CAR-APPEND natively: the head of an append. -/
theorem car_append_native_driver (xs ys : List SExpr) :
    (xs ++ ys).headD SExpr.nil = Worlds.Sorting.carAppendSpec xs ys :=
  Worlds.Sorting.car_append_native_of_replayed qsortWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    carAppendReplayed_uncond xs ys

#print axioms car_append_native_driver

set_option maxHeartbeats 1600000 in
/-- The UNCONDITIONAL driver replayed statement for
    PERM-IMPLIES-EQUAL-ALL-REL-2 (ACL2's defcong). -/
def permImpliesAllRel2Replayed := driver_replayed% qsortDev qsortWorldD
  "perm-implies-equal-all-rel-2"

/-- ENTRY, PROVED — PERM-IMPLIES-EQUAL-ALL-REL-2 natively: `allRelL` is
    invariant under permutation (the defcong, over `isPerm`). -/
theorem perm_implies_equal_all_rel_2_native_driver (fv ev : SExpr)
    (xs ys : List SExpr) (hp : xs.isPerm ys = true) :
    Worlds.Sorting.allRelL fv ev xs = Worlds.Sorting.allRelL fv ev ys :=
  Worlds.Sorting.perm_implies_equal_all_rel_2_native_of_replayed qsortWorldD
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    permImpliesAllRel2Replayed fv ev xs ys hp

#print axioms perm_implies_equal_all_rel_2_native_driver

set_option maxHeartbeats 1600000 in
/-- The driver's replayed statement for ALL-REL-RM-1, now
    UNCONDITIONAL (its sole `tp:ALL-REL` hypothesis is supplied by the
    driver's TP prover — TP-replay arc increment 4, 2026-08-13). -/
def allRelRm1ReplayedCond := driver_replayed% qsortDev qsortWorldD
  "all-rel-rm-1"

/-- The unconditional form. -/
theorem allRelRm1Replayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f qsortWorldD env
      Worlds.Sorting.all_rel_rm_1Formula = some v ∧ v ≠ SExpr.nil :=
  allRelRm1ReplayedCond env

/-- ENTRY, PROVED — ALL-REL-RM-1 natively: a universally `relL`-related
    list stays so after erasing an element. -/
theorem all_rel_rm_1_native_driver (fv ev dv : SExpr) (xs : List SExpr)
    (h : Worlds.Sorting.allRelL fv ev xs = true) :
    Worlds.Sorting.allRelL fv ev (xs.erase dv) = true :=
  Worlds.Sorting.all_rel_rm_1_native_of_replayed qsortWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) allRelRm1Replayed_uncond
    fv ev dv xs h

#print axioms all_rel_rm_1_native_driver

set_option maxHeartbeats 1600000 in
/-- The driver's replayed statement for ALL-REL-RM-2, now
    UNCONDITIONAL (`tp:ALL-REL` supplied by the driver's TP prover). -/
def allRelRm2ReplayedCond := driver_replayed% qsortDev qsortWorldD
  "all-rel-rm-2"

/-- The unconditional form. -/
theorem allRelRm2Replayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f qsortWorldD env
      Worlds.Sorting.all_rel_rm_2Formula = some v ∧ v ≠ SExpr.nil :=
  allRelRm2ReplayedCond env

/-- ENTRY, PROVED — ALL-REL-RM-2 natively: restoring an erased
    `relL`-related element keeps the list universally related. -/
theorem all_rel_rm_2_native_driver (fv ev dv : SExpr) (xs : List SExpr)
    (h1 : Worlds.Sorting.allRelL fv ev (xs.erase dv) = true)
    (h2 : Worlds.Sorting.relL fv dv ev = true) :
    Worlds.Sorting.allRelL fv ev xs = true :=
  Worlds.Sorting.all_rel_rm_2_native_of_replayed qsortWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) allRelRm2Replayed_uncond
    fv ev dv xs h1 h2

#print axioms all_rel_rm_2_native_driver

set_option maxHeartbeats 1600000 in
/-- The driver's replayed statement for ALL-REL-FILTER-1, now
    UNCONDITIONAL (`tp:ALL-REL` supplied by the driver's TP prover). -/
def allRelFilter1ReplayedCond := driver_replayed% qsortDev qsortWorldD
  "all-rel-filter-1"

theorem allRelFilter1Replayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f qsortWorldD env
      Worlds.Sorting.all_rel_filter_1Formula = some v ∧ v ≠ SExpr.nil :=
  allRelFilter1ReplayedCond env

/-- ENTRY, PROVED — ALL-REL-FILTER-1 natively: everything the
    strict-lexorder filter keeps is lexorder-below the pivot. -/
theorem all_rel_filter_1_native_driver (ev : SExpr) (xs : List SExpr) :
    (xs.filter (fun a => Worlds.Sorting.lexLtB a ev)).all
      (fun a => Worlds.Sorting.lexorderB a ev) = true :=
  Worlds.Sorting.all_rel_filter_1_native_of_replayed qsortWorldD
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) allRelFilter1Replayed_uncond ev xs

#print axioms all_rel_filter_1_native_driver

set_option maxHeartbeats 1600000 in
/-- The driver's replayed statement for ALL-REL-FILTER-2, now
    UNCONDITIONAL (`tp:ALL-REL` supplied by the driver's TP prover). -/
def allRelFilter2ReplayedCond := driver_replayed% qsortDev qsortWorldD
  "all-rel-filter-2"

theorem allRelFilter2Replayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f qsortWorldD env
      Worlds.Sorting.all_rel_filter_2Formula = some v ∧ v ≠ SExpr.nil :=
  allRelFilter2ReplayedCond env

/-- ENTRY, PROVED — ALL-REL-FILTER-2 natively: everything the
    reverse-lexorder filter keeps is lexorder-above the pivot. -/
theorem all_rel_filter_2_native_driver (ev : SExpr) (xs : List SExpr) :
    (xs.filter (fun a => Worlds.Sorting.lexorderB ev a)).all
      (fun a => Worlds.Sorting.lexorderB ev a) = true :=
  Worlds.Sorting.all_rel_filter_2_native_of_replayed qsortWorldD
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) allRelFilter2Replayed_uncond ev xs

#print axioms all_rel_filter_2_native_driver

set_option maxHeartbeats 1600000 in
/-- The driver's replayed statement for HOW-MANY-FILTER-1 — now
    UNCONDITIONAL (`tp:HOW-MANY` and
    `rule:NOT-MEMB-IMPLIES-HOW-MANY-IS-0` by the TP prover and the
    dependency transfer; the three arithmetic-3 comm/assoc rules by the
    D5 registry, P4b). -/
def howManyFilter1ReplayedCond := driver_replayed% qsortDev qsortWorldD
  "how-many-filter-1" deps [convertPermDev]

theorem howManyFilter1Replayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f qsortWorldD env
      Worlds.Sorting.how_many_filter_1Formula = some v ∧ v ≠ SExpr.nil :=
  howManyFilter1ReplayedCond env

    -- (the five arithmetic-3 runes rule:(+ y x) / (+ y (+ x z)) /
    -- (+ (+ x y) z) / (+ x (if a b c)) / (equal (if a b c) x) RETIRED,
    -- T1+2 sprint P4b 2026-08-15 — the D5 registry discharges each at its
    -- CITED rune from the prelude constant, so the hypotheses left the
    -- telescope and the hand-applied `dis_*` arguments went with them.)

/-- ENTRY, PROVED — HOW-MANY-FILTER-1 natively: the LT/GTE filters
    PARTITION every element's multiplicity. -/
theorem how_many_filter_1_native_driver (ev dv : SExpr)
    (xs : List SExpr) :
    Worlds.Sorting.howManyL ev (xs.filter (fun a => Worlds.Sorting.lexLtB a dv))
      + Worlds.Sorting.howManyL ev
          (xs.filter (fun a => Worlds.Sorting.lexorderB dv a))
      = Worlds.Sorting.howManyL ev xs :=
  Worlds.Sorting.how_many_filter_1_native_of_replayed qsortWorldD
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    howManyFilter1Replayed_uncond ev dv xs

#print axioms how_many_filter_1_native_driver

set_option maxHeartbeats 4000000 in
/-- The driver's replayed statement for ORDEREDP-APPEND — now
    UNCONDITIONAL: both TP conditions (`tp:ALL-REL`, and
    `tp:BINARY-APPEND` in its ARGS-VALUED shape) come from the driver's
    TP prover (TP-replay arc increments 4 and 5, 2026-08-13), and the
    last one left, the if-lifting rule `(equal (if a b c) x)`, from the
    D5 registry (P4b). -/
def orderedpAppendReplayedCond := driver_replayed% qsortDev qsortWorldD
  "orderedp-append"

/-- The unconditional form. -/
theorem orderedpAppendReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f qsortWorldD env
      Worlds.Sorting.orderedp_appendFormula = some v ∧ v ≠ SExpr.nil :=
  orderedpAppendReplayedCond env
    -- (the five arithmetic-3 runes rule:(+ y x) / (+ y (+ x z)) /
    -- (+ (+ x y) z) / (+ x (if a b c)) / (equal (if a b c) x) RETIRED,
    -- T1+2 sprint P4b 2026-08-15 — the D5 registry discharges each at its
    -- CITED rune from the prelude constant, so the hypotheses left the
    -- telescope and the hand-applied `dis_*` arguments went with them.)

/-- ENTRY, PROVED — ORDEREDP-APPEND natively: for sorted `as`, the
    append `as ++ ev :: bs` is sorted EXACTLY when `bs` is sorted,
    everything in `as` is lexorder-below `ev`, and everything in `bs`
    is lexorder-above it — quicksort's assembly step. -/
theorem orderedp_append_native_driver (ev : SExpr) (as bs : List SExpr)
    (hord : Worlds.Sorting.orderedpRec as = true) :
    Worlds.Sorting.orderedpRec (as ++ ev :: bs)
      = (Worlds.Sorting.orderedpRec bs
          && ((as.all fun a => Worlds.Sorting.lexorderB a ev)
              && (bs.all fun b => Worlds.Sorting.lexorderB ev b))) :=
  Worlds.Sorting.orderedp_append_native_of_replayed qsortWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    orderedpAppendReplayed_uncond ev as bs hord

#print axioms orderedp_append_native_driver

set_option maxHeartbeats 4000000 in
/-- HOW-MANY-QSORT's conditional replayed statement (ten hypotheses:
    `total:O<`, `tp:HOW-MANY`, `tp:ACL2-COUNT`, and the seven rule
    conditions). -/
def howManyQsortReplayedCond := driver_replayed% qsortDev qsortWorldD
  "how-many-qsort" with_termination deps [convertPermDev]

set_option maxHeartbeats 1600000 in
theorem howManyQsortReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f qsortWorldD env
      Worlds.Sorting.how_many_qsortFormula = some v ∧ v ≠ SExpr.nil :=
  howManyQsortReplayedCond env
    -- (total:O< / total:O-P RETIRED, T1+2 sprint P3b 2026-08-15 — the
    -- ordinal registry row (Replay/OrdinalSim) + the O-FINP recognizer
    -- duality make the driver PROVE both admissions from ACL2's own
    -- emitted ground-zero termination clauses, so the hypotheses left
    -- the telescope and `dis_o_lt_total` was deleted.)
    -- (the five arithmetic-3 runes rule:(+ y x) / (+ y (+ x z)) /
    -- (+ (+ x y) z) / (+ x (if a b c)) / (equal (if a b c) x) RETIRED,
    -- T1+2 sprint P4b 2026-08-15 — the D5 registry discharges each at its
    -- CITED rune from the prelude constant, so the hypotheses left the
    -- telescope and the hand-applied `dis_*` arguments went with them.)

set_option maxHeartbeats 1600000 in
/-- ENTRY, PROVED — HOW-MANY-QSORT natively: QUICKSORT PRESERVES
    MULTIPLICITY. -/
theorem how_many_qsort_native_driver (ev : SExpr) (xs : List SExpr) :
    Worlds.Sorting.howManyL ev (Worlds.Sorting.qsortL xs)
      = Worlds.Sorting.howManyL ev xs :=
  Worlds.Sorting.how_many_qsort_native_of_replayed qsortWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    howManyQsortReplayed_uncond ev xs

#print axioms how_many_qsort_native_driver

set_option maxHeartbeats 4000000 in
/-- PERM-QSORT's conditional replayed statement (THE FLAGSHIP — twelve
    hypotheses: PCE/O< totality, the HOW-MANY/ACL2-COUNT TP corollaries,
    and the seven rule conditions incl. CONVERT-PERM-TO-HOW-MANY). -/
def permQsortReplayedCond := driver_replayed% qsortDev qsortWorldD
  "perm-qsort" with_termination
  deps [permDev, convertPermDev, orderedPermsDev]

set_option maxHeartbeats 1600000 in
theorem permQsortReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f qsortWorldD env
      Worlds.Sorting.perm_qsortFormula = some v ∧ v ≠ SExpr.nil :=
  permQsortReplayedCond env
    -- (total:PERM-COUNTER-EXAMPLE RETIRED 2026-08-13 — the ATOM leg
    -- covers PCE's emitted `(ATOM X)`-ruled decrease, so the hypothesis
    -- left the telescope and `dis_pce_total` was deleted.)
    -- (total:O< / total:O-P RETIRED, T1+2 sprint P3b 2026-08-15 — the
    -- ordinal registry row (Replay/OrdinalSim) + the O-FINP recognizer
    -- duality make the driver PROVE both admissions from ACL2's own
    -- emitted ground-zero termination clauses, so the hypotheses left
    -- the telescope and `dis_o_lt_total` was deleted.)
    -- (rule:CONVERT-PERM-TO-HOW-MANY RETIRED, T1+2 sprint P3c
    -- 2026-08-15 — the cross-book D1 transfer replays the dependency
    -- at this world, so the hypothesis left the telescope and
    -- `dis_convert_perm` was deleted.)
    -- (the five arithmetic-3 runes rule:(+ y x) / (+ y (+ x z)) /
    -- (+ (+ x y) z) / (+ x (if a b c)) / (equal (if a b c) x) RETIRED,
    -- T1+2 sprint P4b 2026-08-15 — the D5 registry discharges each at its
    -- CITED rune from the prelude constant, so the hypotheses left the
    -- telescope and the hand-applied `dis_*` arguments went with them.)

set_option maxHeartbeats 1600000 in
/-- ENTRY, PROVED — PERM-QSORT natively: QUICKSORT PERMUTES —
    `qsortL xs` is a permutation of `xs` (the book's own `PERM`, read as
    `permL`).

    Stated in the OWN-DEFINITION `permL` vocabulary since R4 wave 2d
    (O-6): this is the native the `qsort_perm` mirror meets, and a
    mirror agree square must face an own-definition reading. -/
theorem perm_qsort_native_driver (xs : List SExpr) :
    Worlds.Sorting.permL (Worlds.Sorting.qsortL xs) xs = true := by
  rw [Worlds.Sorting.permL_eq_isPerm]
  exact Worlds.Sorting.perm_qsort_native_of_replayed qsortWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) permQsortReplayed_uncond xs

/-- The idiomatic `List.Perm` form (through the decode bridge). -/
theorem perm_qsort_perm_driver (xs : List SExpr) :
    (Worlds.Sorting.qsortL xs).Perm xs :=
  List.isPerm_iff.mp
    (Worlds.Sorting.permL_eq_isPerm _ _ ▸ perm_qsort_native_driver xs)

/-- PERM-QSORT at the DEPTH-1 reading (R4 wave 2e) — the same theorem,
    read through `qsortOwnL_eq_qsortL`. A DECODE-SHAPE corollary in the
    class this layer already writes (`ordered_perms_eq_driver`,
    `perm_qsort_perm_driver`, `orderedp_qsort_isChain_driver`): it
    carries no content of its own, and the content is the replay's. It
    exists because the `qsort` MIRROR agree square must face the
    mirror's own access pattern — see
    `MirrorProofs/SortingQsortSquares.lean`. -/
theorem perm_qsort_own_driver (xs : List SExpr) :
    Worlds.Sorting.permL (Worlds.Sorting.qsortOwnL xs) xs = true := by
  rw [Worlds.Sorting.qsortOwnL_eq_qsortL]
  exact perm_qsort_native_driver xs

#print axioms perm_qsort_native_driver

set_option maxHeartbeats 4000000 in
/-- ORDEREDP-QSORT's conditional replayed statement (THE HEADLINE —
    PERM-QSORT's remaining hypotheses plus the in-book
    `rule:ORDEREDP-APPEND`; `tp:ALL-REL` is now supplied by the
    driver's TP prover). -/
def orderedpQsortReplayedCond := driver_replayed% qsortDev qsortWorldD
  "orderedp-qsort" with_termination
  deps [permDev, convertPermDev, orderedPermsDev]

set_option maxHeartbeats 1600000 in
theorem orderedpQsortReplayed_uncond (env : Env) :
    ∃ N, ∀ f, f ≥ N → ∃ v, evalOpt f qsortWorldD env
      Worlds.Sorting.orderedp_qsortFormula = some v ∧ v ≠ SExpr.nil :=
  orderedpQsortReplayedCond env
    -- (total:PERM-COUNTER-EXAMPLE RETIRED 2026-08-13 — see PERM-QSORT.)
    -- (total:O< / total:O-P RETIRED, T1+2 sprint P3b 2026-08-15 — the
    -- ordinal registry row (Replay/OrdinalSim) + the O-FINP recognizer
    -- duality make the driver PROVE both admissions from ACL2's own
    -- emitted ground-zero termination clauses, so the hypotheses left
    -- the telescope and `dis_o_lt_total` was deleted.)
    -- (rule:CONVERT-PERM-TO-HOW-MANY RETIRED, T1+2 sprint P3c
    -- 2026-08-15 — the cross-book D1 transfer replays the dependency
    -- at this world, so the hypothesis left the telescope and
    -- `dis_convert_perm` was deleted.)
    -- (the five arithmetic-3 runes rule:(+ y x) / (+ y (+ x z)) /
    -- (+ (+ x y) z) / (+ x (if a b c)) / (equal (if a b c) x) RETIRED,
    -- T1+2 sprint P4b 2026-08-15 — the D5 registry discharges each at its
    -- CITED rune from the prelude constant, so the hypotheses left the
    -- telescope and the hand-applied `dis_*` arguments went with them.)
    -- (rule:ORDEREDP-APPEND RETIRED, T1+2 sprint P5a 2026-08-16 — the
    -- IFF-CONCLUSION DECODE class: ACL2 stores an `(IFF lhs rhs)` defthm
    -- conclusion as an `:EQUIV EQUAL` rule when both sides are boolean,
    -- and `dischargeRuleHyp` now recomputes exactly that normalization,
    -- taking the two-valuedness from the EMITTED :TYPE-PRESCRIPTION
    -- corollaries. The hypothesis left the telescope and the
    -- hand-applied `dis_rule_orderedp_append` — the waypoint layer's
    -- registered DECODE EXCEPTION — went with it, deleted.)

set_option maxHeartbeats 1600000 in
/-- ENTRY, PROVED — ORDEREDP-QSORT natively: QUICKSORT SORTS —
    `qsortL xs` is adjacent-pair lexorder-sorted for EVERY input. -/
theorem orderedp_qsort_native_driver (xs : List SExpr) :
    Worlds.Sorting.orderedpRec (Worlds.Sorting.qsortL xs) = true :=
  Worlds.Sorting.orderedp_qsort_native_of_replayed qsortWorldD (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    orderedpQsortReplayed_uncond xs

/-- HOW-MANY-QSORT at the DEPTH-1 reading — the same theorem, read
    through `qsortOwnL_eq_qsortL`; see `perm_qsort_own_driver` for the
    class. -/
theorem how_many_qsort_own_driver (ev : SExpr) (xs : List SExpr) :
    Worlds.Sorting.howManyL ev (Worlds.Sorting.qsortOwnL xs)
      = Worlds.Sorting.howManyL ev xs := by
  rw [Worlds.Sorting.qsortOwnL_eq_qsortL]
  exact how_many_qsort_native_driver ev xs

/-- ORDEREDP-QSORT at the DEPTH-1 reading (R4 wave 2e) — the same
    theorem, read through `qsortOwnL_eq_qsortL`; see
    `perm_qsort_own_driver` for the class. -/
theorem orderedp_qsort_own_driver (xs : List SExpr) :
    Worlds.Sorting.orderedpRec (Worlds.Sorting.qsortOwnL xs) = true := by
  rw [Worlds.Sorting.qsortOwnL_eq_qsortL]
  exact orderedp_qsort_native_driver xs

/-- ORDEREDP-QSORT, Mathlib form. -/
theorem orderedp_qsort_isChain_driver (xs : List SExpr) :
    (Worlds.Sorting.qsortL xs).IsChain
      (fun a b => Worlds.Sorting.lexorderB a b = true) :=
  (Worlds.Sorting.chain2Rec_iff_isChain _ _).mp
    (orderedp_qsort_native_driver xs)

#print axioms orderedp_qsort_native_driver

end ACL2.Imported.Waypoints
