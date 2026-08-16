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

-- (`logic_nfix_eq_nfixNat` — the bridge `Logic.nfix x = int (nfixNat x)`
-- — DELETED 2026-08-16: it landed with R3 and nothing ever consumed it.
-- Its siblings are load-bearing and stay (`nfixNat_int` is `@[simp]`
-- and used in-file; `nfixNat_plus_lt_of_not_zp` at Decrease.lean). It
-- comes back the day a consumer needs the twin bridge stated.)

/-! ## The NFIX row's ARITHMETIC decrease (T1+2 sprint phase 3a)

The `count`/`len` rows decrease along a DESTRUCTOR CHAIN; the NFIX row does
not. Its emitted obligations are arithmetic — the three corpus witnesses
(`recon-tests/11-custom-measure`'s `CD2`, `06-measure`'s `COUNT-DOWN`,
`07-mutual-recursion`'s `MY-EVENP`/`MY-ODDP`) all emit

    ((ZP N) … (O< (NFIX (BINARY-+ 'k N)) (NFIX N)))     with k < 0

i.e. the recursive call adds a NEGATIVE integer literal, ruled by a
REFUTED `(ZP N)`. These are the `nfixNat` twins the decrease walk
(`chainLtNfix`, Driver/Decrease) consumes; the emitted clause remains the
sole license (CLAUDE.md's admission carve-out extension) — this is only the
arithmetic that discharges it. -/

/-- A REFUTED `(ZP v)` ruler says exactly `0 < toInt v` (`Logic.zp` is
    `toInt ≤ 0`, and `toBool` is nil-dichotomous). -/
theorem toInt_pos_of_not_zp {v : SExpr}
    (h : Logic.toBool (Logic.zp v) = false) : 0 < Logic.toInt v := by
  by_cases hz : Logic.toInt v ≤ 0
  · exfalso
    have hzt : Logic.zp v = SExpr.t := if_pos hz
    rw [hzt] at h
    exact absurd h (by decide)
  · omega

/-- A value with a non-zero `toInt` IS an integer atom (everything else
    coerces to `0`). -/
theorem exists_int_of_toInt_ne_zero {x : SExpr} (h : Logic.toInt x ≠ 0) :
    ∃ n : Int, x = .atom (.number (.int n)) := by
  match x with
  | .atom (.number (.int n)) => exact ⟨n, rfl⟩
  | .atom (.number (.rational _ _ _)) => exact absurd rfl h
  | .atom (.symbol _) => exact absurd rfl h
  | .atom (.keyword _) => exact absurd rfl h
  | .atom (.string _) => exact absurd rfl h
  | .atom (.char _) => exact absurd rfl h
  | .nil => exact absurd rfl h
  | .cons _ _ => exact absurd rfl h

/-- THE NFIX ROW'S DECREASE: adding a NEGATIVE integer to a value whose
    `(ZP …)` ruler is refuted strictly decreases `nfixNat`. `c`'s negative
    `toInt` forces it to be a negative integer atom, and the refuted `ZP`
    forces `v` to be a POSITIVE one — so the sum is `< v` and its
    zero-clipped natural is strictly below `v`'s. -/
theorem nfixNat_plus_lt_of_not_zp {c v : SExpr} (hc : Logic.toInt c < 0)
    (hz : Logic.toBool (Logic.zp v) = false) :
    nfixNat (Logic.plus c v) < nfixNat v := by
  have hv : 0 < Logic.toInt v := toInt_pos_of_not_zp hz
  obtain ⟨m, rfl⟩ := exists_int_of_toInt_ne_zero (x := c) (by omega)
  obtain ⟨n, rfl⟩ := exists_int_of_toInt_ne_zero (x := v) (by omega)
  rw [Logic.plus_int]
  simp only [nfixNat_int]
  simp only [Logic.toInt_int] at hc hv
  omega

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
