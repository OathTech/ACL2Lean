/-
  Replay/Lemmas/MeasureMu — the measure table's μ-INTERPRETATION row
  (T1+2 sprint phase 2, 2026-08-14; overspecialization audit F6/F7/F8).

  `Replay/MeasureTable.lean` is the dependency-light CLASSIFIER (a
  `:MEASURE` term → a `MeasureShape` row). This module carries the part
  of the table that names trusted-core constants: each row's `SExpr → Nat`
  interpretation, plus the NFIX row's own lemma family (the `nfixNat`
  twin of `lenNat`, exactly parallel to the LEN row's registration).

  μ is proof bookkeeping (design I1) — it appears in no statement, so a
  wrong entry here can only fail a proof, never weaken one.
-/
import ACL2Lean.Replay.Lemmas.Judgments
import ACL2Lean.Replay.MeasureTable

namespace ACL2.Replay

open ACL2

/-! ## The NFIX row's `Nat` twin

`(NFIX N)` is the arithmetic-countdown family's measure (`CD2`,
`COUNT-DOWN`, `MY-EVENP` in `acl2_samples/recon-tests/11-custom-measure`
and `07-mutual-recursion`). `Logic.nfix` computes it as an int atom;
`nfixNat` is the `Nat`-typed twin the μ-registry interprets it by — the
same shape as `lenNat`/`Logic.len` (Judgments) and
`SExpr.consCount`/`ACL2-COUNT`. -/

/-- Nat-valued twin of `Logic.nfix`: a non-negative integer atom is its own
    natural, everything else is `0`. -/
def nfixNat : SExpr → Nat
  | .atom (.number (.int n)) => n.toNat
  | _ => 0

@[simp] theorem nfixNat_int (n : Int) :
    nfixNat (.atom (.number (.int n))) = n.toNat := rfl

/-- `Logic.nfix` computes `nfixNat` as an int atom. -/
theorem logic_nfix_eq_nfixNat (x : SExpr) :
    Logic.nfix x = .atom (.number (.int (nfixNat x))) := by
  match x with
  | .atom (.number (.int n)) =>
    by_cases h : n ≥ 0
    · simp [Logic.nfix, nfixNat, h, Int.toNat_of_nonneg h]
    · simp [Logic.nfix, nfixNat, h]
      omega
  | .atom (.number (.rational _ _ _)) => rfl
  | .atom (.symbol _) => rfl
  | .atom (.keyword _) => rfl
  | .atom (.string _) => rfl
  | .atom (.char _) => rfl
  | .nil => rfl
  | .cons _ _ => rfl

/-! ## The μ-registry row -/

/-- THE μ-REGISTRY: each measure-table row's trusted-core `SExpr → Nat`
    interpretation, ONE entry per measured variable in `MeasureShape.vars`
    order (a `sumCount` row interprets each component by `consCount` and
    the consumer adds them). `none` = the row has NO μ — `userFn` measures
    are interpreted only by the RECORDED-TERMINATION route, through the
    replayed admission waterfall (`interpCount`), never here.

    Extension is additive: a row's entry here IS the whole of its
    μ-registration, and the match is total, so adding a row to
    `MeasureShape` forces a decision at this site. -/
def MeasureShape.muHeads : MeasureShape → Option (List Lean.Name)
  | .count _ => some [``SExpr.consCount]
  | .len _ => some [``ACL2.Replay.lenNat]
  | .nfix _ => some [``ACL2.Replay.nfixNat]
  | .sumCount _ _ => some [``SExpr.consCount, ``SExpr.consCount]
  | .userFn _ _ => none

end ACL2.Replay
