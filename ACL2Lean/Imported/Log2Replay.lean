import ACL2Lean.Logic

open ACL2 ACL2.Logic

namespace ACL2
namespace Imported
namespace Log2Replay

private def intExpr (z : Int) : SExpr :=
  .atom (.number (.int z))

private def natExpr (n : Nat) : SExpr :=
  intExpr (Int.ofNat n)

/--
A proof-friendly semantic mirror of the imported ACL2 `clog2`, restricted to
the positive-integer case that matters for theorem replay.
-/
private def clog2Nat (n : Nat) : Nat :=
  if n ≤ 1 then 0 else (n - 1).log2 + 1

private def nbrCallsClog2Nat (n : Nat) : Nat :=
  if n = 0 then 1 else clog2Nat n + 1

private theorem int_toNat_pos {z : Int} (h : 0 < z) : 0 < z.toNat := by
  exact Int.ofNat_lt.mp <| by
    have hz : 0 ≤ z := by omega
    simpa [Int.toNat_of_nonneg hz] using h

private theorem int_toNat_gt_one {z : Int} (h : 1 < z) : 1 < z.toNat := by
  exact Int.ofNat_lt.mp <| by
    have hz : 0 ≤ z := by omega
    simpa [Int.toNat_of_nonneg hz] using h

private theorem clog2Nat_pos {n : Nat} (h : 1 < n) : 0 < clog2Nat n := by
  simp [clog2Nat, Nat.not_le.mpr h]

private theorem self_le_two_pow_clog2Nat (n : Nat) : n ≤ 2 ^ clog2Nat n := by
  by_cases h : n ≤ 1
  · simp [clog2Nat, h]
  · have hn : 1 < n := Nat.lt_of_not_ge h
    have hpow : n ≤ 2 ^ ((n - 1).log2 + 1) := by
      simpa [Nat.sub_add_cancel (Nat.le_of_lt hn)] using
        (Nat.succ_le_of_lt (Nat.lt_log2_self (n := n - 1)))
    simpa [clog2Nat, Nat.not_le.mpr hn] using hpow

private theorem two_pow_pred_clog2Nat_lt_self {n : Nat} (h : 1 < n) :
    2 ^ (clog2Nat n - 1) < n := by
  have hpow : 2 ^ ((n - 1).log2) ≤ n - 1 :=
    Nat.log2_self_le (Nat.sub_ne_zero_of_lt h)
  have hlt : 2 ^ ((n - 1).log2) < n := by
    have hsub : n - 1 < n := by omega
    omega
  simpa [clog2Nat, Nat.not_le.mpr h] using hlt

/-- Imported from `acl2_samples/2009-log2.lisp`, normalized through `Nat`. -/
def clog2 : SExpr → SExpr
  | .atom (.number (.int z)) =>
      if 0 < z then natExpr (clog2Nat z.toNat) else intExpr (-1)
  | _ => intExpr (-1)

/-- Imported from `acl2_samples/2009-log2.lisp`, normalized through `Nat`. -/
def nbrCallsClog2 : SExpr → SExpr
  | .atom (.number (.int z)) =>
      if 0 < z then natExpr (nbrCallsClog2Nat z.toNat) else intExpr 1
  | _ => intExpr 1

private theorem clog2_eq_natExpr_of_pos {z : Int} (hz : 0 < z) :
    clog2 (intExpr z) = natExpr (clog2Nat z.toNat) := by
  simp [clog2, intExpr, natExpr, hz]

private theorem expt_two_clog2_eq_natExpr_of_pos {z : Int} (hz : 0 < z) :
    Logic.expt (intExpr 2) (clog2 (intExpr z)) = natExpr (2 ^ clog2Nat z.toNat) := by
  simp [Logic.expt, clog2, intExpr, natExpr, hz]

private theorem expt_two_pred_clog2_eq_natExpr_of_gt_one {z : Int} (hz : 1 < z) :
    Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr z))) =
      natExpr (2 ^ (clog2Nat z.toNat - 1)) := by
  have hz0 : 0 < z := by omega
  have hclog : 0 < clog2Nat z.toNat := clog2Nat_pos (int_toNat_gt_one hz)
  have hnonneg : ¬ (-1 + Int.ofNat (clog2Nat z.toNat) < 0) := by
    have : (1 : Int) ≤ Int.ofNat (clog2Nat z.toNat) :=
      Int.ofNat_le.mpr (Nat.succ_le_of_lt hclog)
    omega
  simp [Logic.expt, Logic.plus, toRat, mkNumber, clog2, intExpr, natExpr, hz0]
  have htoNat : (-1 + (clog2Nat z.toNat : Int)).toNat = clog2Nat z.toNat - 1 := by
    calc
      (-1 + (clog2Nat z.toNat : Int)).toNat = (((clog2Nat z.toNat : Nat) : Int) - 1).toNat := by
        omega
      _ = clog2Nat z.toNat - 1 := by
        simp
  split <;> simp_all

private theorem nbrCallsClog2Nat_eq_1_plus_clog2Nat {n : Nat} (h : 0 < n) :
    nbrCallsClog2Nat n = clog2Nat n + 1 := by
  simp [nbrCallsClog2Nat, Nat.ne_of_gt h]

/--
A proof-friendly semantic mirror of the imported ACL2 `flog2`, restricted to
the positive-integer case that matters for theorem replay.
-/
private def flog2Nat (n : Nat) : Nat :=
  n.log2

private def nbrCallsFlog2Nat : Nat → Nat
  | 0 => 1
  | n + 1 =>
      if (n + 1) % 2 = 0 then
        1 + nbrCallsFlog2Nat ((n + 1) / 2)
      else
        1 + nbrCallsFlog2Nat n
termination_by n => n

private theorem two_pow_flog2Nat_le_self {n : Nat} (h : 0 < n) :
    2 ^ flog2Nat n ≤ n := by
  simpa [flog2Nat] using Nat.log2_self_le (Nat.ne_of_gt h)

private theorem self_lt_two_pow_succ_flog2Nat (n : Nat) :
    n < 2 ^ (flog2Nat n + 1) := by
  simpa [flog2Nat] using Nat.lt_log2_self (n := n)

private theorem flog2Nat_even {n : Nat} (h : 0 < n) :
    flog2Nat (2 * n) = flog2Nat n + 1 := by
  simpa [flog2Nat, Nat.mul_comm] using Nat.log2_two_mul (n := n) (Nat.ne_of_gt h)

private theorem flog2Nat_odd {n : Nat} (h : 0 < n) :
    flog2Nat (2 * n + 1) = flog2Nat n + 1 := by
  obtain ⟨h₁, h₂⟩ := (Nat.log2_eq_iff (n := n) (k := n.log2) (Nat.ne_of_gt h)).mp rfl
  rw [flog2Nat, flog2Nat, Nat.log2_eq_iff (n := 2 * n + 1) (k := n.log2 + 1) (by omega)]
  constructor
  · rw [Nat.pow_succ]
    omega
  · rw [Nat.pow_succ]
    omega

private theorem nbrCallsFlog2Nat_even {n : Nat} (h : 0 < n) :
    nbrCallsFlog2Nat (2 * n) = 1 + nbrCallsFlog2Nat n := by
  have hsucc : 2 * n = Nat.succ (2 * n - 1) := by omega
  rw [hsucc, nbrCallsFlog2Nat]
  have hmod : (2 * n - 1 + 1) % 2 = 0 := by omega
  have hdiv : (2 * n - 1 + 1) / 2 = n := by omega
  simp [hmod, hdiv]

private theorem nbrCallsFlog2Nat_odd {n : Nat} (h : 0 < n) :
    nbrCallsFlog2Nat (2 * n + 1) = 2 + nbrCallsFlog2Nat n := by
  have hsucc : 2 * n + 1 = Nat.succ (2 * n) := by omega
  rw [hsucc, nbrCallsFlog2Nat]
  have hmod : ¬ ((2 * n + 1) % 2 = 0) := by omega
  rw [if_neg hmod, nbrCallsFlog2Nat_even h]
  omega

private theorem nbrCallsFlog2Nat_lower : ∀ n : Nat, 0 < n → 2 + flog2Nat n ≤ nbrCallsFlog2Nat n
  | 0, h => by cases Nat.lt_asymm h h
  | 1, _ => by
      have hlog : flog2Nat 1 = 0 := by
        rw [flog2Nat]
        exact (Nat.log2_eq_iff (n := 1) (k := 0) (by decide)).2 (by decide)
      simp [nbrCallsFlog2Nat, hlog]
  | n + 2, _ => by
      rcases Nat.mod_two_eq_zero_or_one (n + 2) with hmod | hmod
      · have hhalfPos : 0 < (n + 2) / 2 := by omega
        have ih := nbrCallsFlog2Nat_lower ((n + 2) / 2) hhalfPos
        have hEq : n + 2 = 2 * ((n + 2) / 2) := by omega
        rw [hEq, nbrCallsFlog2Nat_even hhalfPos, flog2Nat_even hhalfPos]
        omega
      · have hhalfPos : 0 < (n + 2) / 2 := by omega
        have ih := nbrCallsFlog2Nat_lower ((n + 2) / 2) hhalfPos
        have hEq : n + 2 = 2 * ((n + 2) / 2) + 1 := by omega
        rw [hEq, nbrCallsFlog2Nat_odd hhalfPos, flog2Nat_odd hhalfPos]
        omega

private theorem nbrCallsFlog2Nat_upper : ∀ n : Nat, 0 < n → nbrCallsFlog2Nat n ≤ 2 + 2 * flog2Nat n
  | 0, h => by cases Nat.lt_asymm h h
  | 1, _ => by
      have hlog : flog2Nat 1 = 0 := by
        rw [flog2Nat]
        exact (Nat.log2_eq_iff (n := 1) (k := 0) (by decide)).2 (by decide)
      simp [nbrCallsFlog2Nat, hlog]
  | n + 2, _ => by
      rcases Nat.mod_two_eq_zero_or_one (n + 2) with hmod | hmod
      · have hhalfPos : 0 < (n + 2) / 2 := by omega
        have ih := nbrCallsFlog2Nat_upper ((n + 2) / 2) hhalfPos
        have hEq : n + 2 = 2 * ((n + 2) / 2) := by omega
        rw [hEq, nbrCallsFlog2Nat_even hhalfPos, flog2Nat_even hhalfPos]
        omega
      · have hhalfPos : 0 < (n + 2) / 2 := by omega
        have ih := nbrCallsFlog2Nat_upper ((n + 2) / 2) hhalfPos
        have hEq : n + 2 = 2 * ((n + 2) / 2) + 1 := by omega
        rw [hEq, nbrCallsFlog2Nat_odd hhalfPos, flog2Nat_odd hhalfPos]
        omega

private theorem nbrCallsFlog2Nat_even_upper {n : Nat} (h : 0 < n) :
    nbrCallsFlog2Nat (2 * n) ≤ 1 + 2 * flog2Nat (2 * n) := by
  rw [nbrCallsFlog2Nat_even h, flog2Nat_even h]
  have hUpper := nbrCallsFlog2Nat_upper n h
  omega

private theorem nbrCallsFlog2Nat_odd_upper {n : Nat} (h : 0 < n) :
    nbrCallsFlog2Nat (2 * n + 1) ≤ 2 + 2 * flog2Nat (2 * n + 1) := by
  rw [nbrCallsFlog2Nat_odd h, flog2Nat_odd h]
  have hUpper := nbrCallsFlog2Nat_upper n h
  omega

/-- Imported from `acl2_samples/2009-log2.lisp`, normalized through `Nat`. -/
def flog2 : SExpr → SExpr
  | .atom (.number (.int z)) =>
      if 0 < z then natExpr (flog2Nat z.toNat) else intExpr 0
  | _ => intExpr 0

/-- Imported from `acl2_samples/2009-log2.lisp`, normalized through `Nat`. -/
def nbrCallsFlog2 : SExpr → SExpr
  | .atom (.number (.int z)) =>
      if 0 < z then natExpr (nbrCallsFlog2Nat z.toNat) else intExpr 1
  | _ => intExpr 1

private theorem flog2_eq_natExpr_of_pos {z : Int} (hz : 0 < z) :
    flog2 (intExpr z) = natExpr (flog2Nat z.toNat) := by
  simp [flog2, intExpr, natExpr, hz]

private theorem nbrCallsFlog2_eq_natExpr_of_pos {z : Int} (hz : 0 < z) :
    nbrCallsFlog2 (intExpr z) = natExpr (nbrCallsFlog2Nat z.toNat) := by
  simp [nbrCallsFlog2, intExpr, natExpr, hz]

private theorem expt_two_flog2_eq_natExpr_of_pos {z : Int} (hz : 0 < z) :
    Logic.expt (intExpr 2) (flog2 (intExpr z)) = natExpr (2 ^ flog2Nat z.toNat) := by
  simp [Logic.expt, flog2, intExpr, natExpr, hz]

private theorem expt_two_succ_flog2_eq_natExpr_of_pos {z : Int} (hz : 0 < z) :
    Logic.expt (intExpr 2) (Logic.plus (intExpr 1) (flog2 (intExpr z))) =
      natExpr (2 ^ (flog2Nat z.toNat + 1)) := by
  have hPlus : Logic.plus (intExpr 1) (flog2 (intExpr z)) = natExpr (flog2Nat z.toNat + 1) := by
    simp [Logic.plus, toRat, mkNumber, flog2, intExpr, natExpr, hz]
    omega
  rw [hPlus]
  simp [Logic.expt, intExpr, natExpr]
  intro hneg
  omega

private theorem two_plus_flog2_eq_natExpr_of_pos {z : Int} (hz : 0 < z) :
    Logic.plus (intExpr 2) (flog2 (intExpr z)) =
      natExpr (2 + flog2Nat z.toNat) := by
  simp [Logic.plus, toRat, mkNumber, flog2, intExpr, natExpr, hz]

private theorem one_plus_two_times_flog2_eq_natExpr_of_pos {z : Int} (hz : 0 < z) :
    Logic.plus (intExpr 1) (Logic.times (intExpr 2) (flog2 (intExpr z))) =
      natExpr (1 + 2 * flog2Nat z.toNat) := by
  simp [Logic.plus, Logic.times, toRat, mkNumber, flog2, intExpr, natExpr, hz]

private theorem two_plus_two_times_flog2_eq_natExpr_of_pos {z : Int} (hz : 0 < z) :
    Logic.plus (intExpr 2) (Logic.times (intExpr 2) (flog2 (intExpr z))) =
      natExpr (2 + 2 * flog2Nat z.toNat) := by
  simp [Logic.plus, Logic.times, toRat, mkNumber, flog2, intExpr, natExpr, hz]

/--
Reconstruction of ACL2 theorem `natp-clog2` from
`acl2_samples/2009-log2.lisp`.
-/
theorem natp_clog2 (n : SExpr) :
    Logic.toBool
      (Logic.implies (Logic.and (Logic.integerp n) (Logic.gt n (intExpr 0)))
        (Logic.ge (clog2 n) (intExpr 0))) = true := by
  cases n with
  | nil =>
      simp [Logic.implies, Logic.integerp]
  | cons a d =>
      simp [Logic.implies, Logic.integerp]
  | atom a =>
      cases a with
      | number value =>
          cases value with
          | int z =>
              by_cases hz : 0 < z
              · have hGe : Logic.ge (clog2 (intExpr z)) (intExpr 0) = .t := by
                  rw [clog2_eq_natExpr_of_pos hz]
                  simp [Logic.ge, toRat, intExpr, natExpr]
                change
                  Logic.toBool
                    (Logic.implies
                      (Logic.and (Logic.integerp (intExpr z)) (Logic.gt (intExpr z) (intExpr 0)))
                      (Logic.ge (clog2 (intExpr z)) (intExpr 0))) = true
                rw [show Logic.and (Logic.integerp (intExpr z)) (Logic.gt (intExpr z) (intExpr 0)) =
                    .t by
                  simp [Logic.and, Logic.integerp, Logic.gt, toRat, intExpr, hz]]
                rw [hGe]
                rfl
              · simp [Logic.implies, Logic.and, Logic.integerp, Logic.gt, toRat, intExpr, hz]
          | _ =>
              simp [Logic.implies, Logic.integerp]
      | _ =>
          simp [Logic.implies, Logic.integerp]

/--
Reconstruction of ACL2 theorem `posp-clog2` from
`acl2_samples/2009-log2.lisp`.
-/
theorem posp_clog2 (n : SExpr) :
    Logic.toBool
      (Logic.implies (Logic.and (Logic.integerp n) (Logic.gt n (intExpr 1)))
        (Logic.gt (clog2 n) (intExpr 0))) = true := by
  cases n with
  | nil =>
      simp [Logic.implies, Logic.integerp]
  | cons a d =>
      simp [Logic.implies, Logic.integerp]
  | atom a =>
      cases a with
      | number value =>
          cases value with
          | int z =>
              by_cases hz : 1 < z
              · have hz0 : 0 < z := by omega
                have hGt : Logic.gt (clog2 (intExpr z)) (intExpr 0) = .t := by
                  rw [clog2_eq_natExpr_of_pos hz0]
                  simp [Logic.gt, toRat, intExpr, natExpr, clog2Nat_pos (int_toNat_gt_one hz)]
                change
                  Logic.toBool
                    (Logic.implies
                      (Logic.and (Logic.integerp (intExpr z)) (Logic.gt (intExpr z) (intExpr 1)))
                      (Logic.gt (clog2 (intExpr z)) (intExpr 0))) = true
                rw [show Logic.and (Logic.integerp (intExpr z)) (Logic.gt (intExpr z) (intExpr 1)) =
                    .t by
                  simp [Logic.and, Logic.integerp, Logic.gt, toRat, intExpr, hz]]
                rw [hGt]
                rfl
              · simp [Logic.implies, Logic.and, Logic.integerp, Logic.gt, toRat, intExpr, hz]
          | _ =>
              simp [Logic.implies, Logic.integerp]
      | _ =>
          simp [Logic.implies, Logic.integerp]

/--
Reconstruction of ACL2 theorem `clog2-is-correct-lower` from
`acl2_samples/2009-log2.lisp`.
-/
theorem clog2_is_correct_lower (n : SExpr) :
    Logic.toBool
      (Logic.implies (Logic.posp n)
        (Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 n))) n)) = true := by
  cases n with
  | nil =>
      simp [Logic.implies, Logic.posp]
  | cons a d =>
      simp [Logic.implies, Logic.posp]
  | atom a =>
      cases a with
      | number value =>
          cases value with
          | int z =>
              by_cases hz : 0 < z
              · by_cases h1 : z = 1
                · subst h1
                  have hLt :
                      Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr 1))))
                        (intExpr 1) = .t := by
                    decide
                  change
                    Logic.toBool
                      (Logic.implies (Logic.posp (intExpr 1))
                        (Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr 1))))
                          (intExpr 1))) = true
                  rw [show Logic.posp (intExpr 1) = .t by
                    simp [Logic.posp, intExpr]]
                  rw [hLt]
                  rfl
                · have hzNat : 0 < z.toNat := int_toNat_pos hz
                  have hzNat1 : 1 < z.toNat := by
                    have : 1 < z := by omega
                    exact int_toNat_gt_one this
                  have hNat : 2 ^ (clog2Nat z.toNat - 1) < z.toNat :=
                    two_pow_pred_clog2Nat_lt_self hzNat1
                  have hzNonneg : 0 ≤ z := by omega
                  have hInt : (2 ^ (clog2Nat z.toNat - 1) : Int) < z := by
                    simpa [Int.toNat_of_nonneg hzNonneg] using (Int.ofNat_lt.mpr hNat)
                  have hLt :
                      Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr z))))
                        (intExpr z) = .t := by
                    rw [expt_two_pred_clog2_eq_natExpr_of_gt_one (by omega : 1 < z)]
                    simpa [Logic.lt, toRat, intExpr, natExpr] using hInt
                  change
                    Logic.toBool
                      (Logic.implies (Logic.posp (intExpr z))
                        (Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr z))))
                          (intExpr z))) = true
                  rw [show Logic.posp (intExpr z) = .t by
                    simp [Logic.posp, intExpr, hz]]
                  rw [hLt]
                  rfl
              · simp [Logic.implies, Logic.posp, hz]
          | _ =>
              simp [Logic.implies, Logic.posp]
      | _ =>
          simp [Logic.implies, Logic.posp]

/--
Reconstruction of ACL2 theorem `clog2-is-correct-upper` from
`acl2_samples/2009-log2.lisp`.
-/
theorem clog2_is_correct_upper (n : SExpr) :
    Logic.toBool
      (Logic.implies (Logic.natp n)
        (Logic.le n (Logic.expt (intExpr 2) (clog2 n)))) = true := by
  cases n with
  | nil =>
      simp [Logic.implies, Logic.natp]
  | cons a d =>
      simp [Logic.implies, Logic.natp]
  | atom a =>
      cases a with
      | number value =>
          cases value with
          | int z =>
              by_cases hz : 0 < z
              · have hNat : z.toNat ≤ 2 ^ clog2Nat z.toNat :=
                  self_le_two_pow_clog2Nat z.toNat
                have hzNonneg : 0 ≤ z := by omega
                have hInt : z ≤ Int.ofNat (2 ^ clog2Nat z.toNat) := by
                  simpa [Int.toNat_of_nonneg hzNonneg] using (Int.ofNat_le.mpr hNat)
                have hLe : Logic.le (intExpr z) (Logic.expt (intExpr 2) (clog2 (intExpr z))) =
                    .t := by
                  rw [expt_two_clog2_eq_natExpr_of_pos hz]
                  simpa [Logic.le, toRat, intExpr, natExpr] using hInt
                change
                  Logic.toBool
                    (Logic.implies (Logic.natp (intExpr z))
                      (Logic.le (intExpr z) (Logic.expt (intExpr 2) (clog2 (intExpr z))))) = true
                rw [show Logic.natp (intExpr z) = .t by
                  simp [Logic.natp, intExpr, hzNonneg]]
                rw [hLe]
                rfl
              · by_cases hz0 : z = 0
                · subst hz0
                  have hLe : Logic.le (intExpr 0) (Logic.expt (intExpr 2) (clog2 (intExpr 0))) =
                      .t := by
                    decide
                  change
                    Logic.toBool
                      (Logic.implies (Logic.natp (intExpr 0))
                        (Logic.le (intExpr 0) (Logic.expt (intExpr 2) (clog2 (intExpr 0))))) = true
                  rw [show Logic.natp (intExpr 0) = .t by
                    simp [Logic.natp, intExpr]]
                  rw [hLe]
                  rfl
                · have hneg : ¬ 0 ≤ z := by omega
                  simp [Logic.implies, Logic.natp, hneg]
          | _ =>
              simp [Logic.implies, Logic.natp]
      | _ =>
          simp [Logic.implies, Logic.natp]

/--
Reconstruction of ACL2 theorem `clog2-is-correct` from
`acl2_samples/2009-log2.lisp`.
-/
theorem clog2_is_correct (n : SExpr) :
    Logic.toBool
      (Logic.implies (Logic.posp n)
        (Logic.and
          (Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 n))) n)
          (Logic.le n (Logic.expt (intExpr 2) (clog2 n))))) = true := by
  cases n with
  | nil =>
      simp [Logic.implies, Logic.posp]
  | cons a d =>
      simp [Logic.implies, Logic.posp]
  | atom a =>
      cases a with
      | number value =>
          cases value with
          | int z =>
              by_cases hz : 0 < z
              · by_cases h1 : z = 1
                · subst h1
                  have hLt :
                      Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr 1))))
                        (intExpr 1) = .t := by
                    decide
                  have hLe :
                      Logic.le (intExpr 1) (Logic.expt (intExpr 2) (clog2 (intExpr 1))) =
                        .t := by
                    decide
                  change
                    Logic.toBool
                      (Logic.implies (Logic.posp (intExpr 1))
                        (Logic.and
                          (Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr 1))))
                            (intExpr 1))
                          (Logic.le (intExpr 1) (Logic.expt (intExpr 2) (clog2 (intExpr 1)))))) = true
                  rw [show Logic.posp (intExpr 1) = .t by
                    simp [Logic.posp, intExpr]]
                  rw [show
                    Logic.and
                      (Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr 1))))
                        (intExpr 1))
                      (Logic.le (intExpr 1) (Logic.expt (intExpr 2) (clog2 (intExpr 1)))) =
                    .t by
                    rw [hLt, hLe]
                    rfl]
                  rfl
                · have hzNat : 0 < z.toNat := int_toNat_pos hz
                  have hzNat1 : 1 < z.toNat := by
                    have : 1 < z := by omega
                    exact int_toNat_gt_one this
                  have hLowerNat : 2 ^ (clog2Nat z.toNat - 1) < z.toNat :=
                    two_pow_pred_clog2Nat_lt_self hzNat1
                  have hUpperNat : z.toNat ≤ 2 ^ clog2Nat z.toNat :=
                    self_le_two_pow_clog2Nat z.toNat
                  have hzNonneg : 0 ≤ z := by omega
                  have hLowerInt : (2 ^ (clog2Nat z.toNat - 1) : Int) < z := by
                    simpa [Int.toNat_of_nonneg hzNonneg] using (Int.ofNat_lt.mpr hLowerNat)
                  have hUpperInt : z ≤ Int.ofNat (2 ^ clog2Nat z.toNat) := by
                    simpa [Int.toNat_of_nonneg hzNonneg] using (Int.ofNat_le.mpr hUpperNat)
                  have hLt :
                      Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr z))))
                        (intExpr z) = .t := by
                    rw [expt_two_pred_clog2_eq_natExpr_of_gt_one (by omega : 1 < z)]
                    simpa [Logic.lt, toRat, intExpr, natExpr] using hLowerInt
                  have hLe :
                      Logic.le (intExpr z) (Logic.expt (intExpr 2) (clog2 (intExpr z))) =
                        .t := by
                    rw [expt_two_clog2_eq_natExpr_of_pos hz]
                    simpa [Logic.le, toRat, intExpr, natExpr] using hUpperInt
                  change
                    Logic.toBool
                      (Logic.implies (Logic.posp (intExpr z))
                        (Logic.and
                          (Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr z))))
                            (intExpr z))
                          (Logic.le (intExpr z) (Logic.expt (intExpr 2) (clog2 (intExpr z)))))) = true
                  rw [show Logic.posp (intExpr z) = .t by
                    simp [Logic.posp, intExpr, hz]]
                  rw [show
                    Logic.and
                      (Logic.lt (Logic.expt (intExpr 2) (Logic.plus (intExpr (-1)) (clog2 (intExpr z))))
                        (intExpr z))
                      (Logic.le (intExpr z) (Logic.expt (intExpr 2) (clog2 (intExpr z)))) =
                    .t by
                    rw [hLt, hLe]
                    rfl]
                  rfl
              · simp [Logic.implies, Logic.posp, hz]
          | _ =>
              simp [Logic.implies, Logic.posp]
      | _ =>
          simp [Logic.implies, Logic.posp]

/--
Reconstruction of ACL2 theorem `nbr-calls-clog2=1+clog2` from
`acl2_samples/2009-log2.lisp`.
-/
theorem nbr_calls_clog2_eq_1_plus_clog2 (n : SExpr) :
    Logic.toBool
      (Logic.implies (Logic.posp n)
        (Logic.equal (nbrCallsClog2 n) (Logic.plus (intExpr 1) (clog2 n)))) = true := by
  cases n with
  | nil =>
      simp [Logic.implies, Logic.posp]
  | cons a d =>
      simp [Logic.implies, Logic.posp]
  | atom a =>
      cases a with
      | number value =>
          cases value with
          | int z =>
              by_cases hz : 0 < z
              · have hz' : 0 ≤ z := by
                  omega
                have hzNatInt : (0 : Int) < z.toNat := by
                  simpa [Int.toNat_of_nonneg hz'] using hz
                have hNat : 0 < z.toNat :=
                  Int.ofNat_lt.mp hzNatInt
                have hEq : nbrCallsClog2 (intExpr z) = Logic.plus (intExpr 1) (clog2 (intExpr z)) := by
                  simp [nbrCallsClog2, clog2, intExpr, natExpr, hz, Logic.plus, toRat, mkNumber,
                    nbrCallsClog2Nat_eq_1_plus_clog2Nat hNat]
                  omega
                change
                  Logic.toBool
                    (Logic.implies (Logic.posp (intExpr z))
                      (Logic.equal (nbrCallsClog2 (intExpr z))
                        (Logic.plus (intExpr 1) (clog2 (intExpr z))))) = true
                rw [show Logic.posp (intExpr z) = .t by
                  simp [intExpr, Logic.posp, hz]]
                rw [show Logic.equal (nbrCallsClog2 (intExpr z)) (Logic.plus (intExpr 1) (clog2 (intExpr z))) =
                    .t by
                  simp [hEq]]
                rfl
              · simp [hz, Logic.implies, Logic.posp]
          | _ =>
              simp [Logic.implies, Logic.posp]
      | _ =>
          simp [Logic.implies, Logic.posp]

/--
Reconstruction of ACL2 theorem `nbr-calls-flog2-lower-bound` from
`acl2_samples/2009-log2.lisp`.
-/
theorem nbr_calls_flog2_lower_bound (n : SExpr) :
    Logic.toBool
      (Logic.implies (Logic.posp n)
        (Logic.le (Logic.plus (intExpr 2) (flog2 n)) (nbrCallsFlog2 n))) = true := by
  cases n with
  | nil =>
      simp [Logic.implies, Logic.posp]
  | cons a d =>
      simp [Logic.implies, Logic.posp]
  | atom a =>
      cases a with
      | number value =>
          cases value with
          | int z =>
              by_cases hz : 0 < z
              · have hNat : 2 + flog2Nat z.toNat ≤ nbrCallsFlog2Nat z.toNat :=
                  nbrCallsFlog2Nat_lower z.toNat (int_toNat_pos hz)
                have hLe :
                    Logic.le (Logic.plus (intExpr 2) (flog2 (intExpr z))) (nbrCallsFlog2 (intExpr z)) =
                      .t := by
                  rw [two_plus_flog2_eq_natExpr_of_pos hz, nbrCallsFlog2_eq_natExpr_of_pos hz]
                  have hInt :
                      Int.ofNat (2 + flog2Nat z.toNat) ≤ Int.ofNat (nbrCallsFlog2Nat z.toNat) :=
                    Int.ofNat_le.mpr hNat
                  simpa [Logic.le, toRat, intExpr, natExpr] using hInt
                change
                  Logic.toBool
                    (Logic.implies (Logic.posp (intExpr z))
                      (Logic.le (Logic.plus (intExpr 2) (flog2 (intExpr z))) (nbrCallsFlog2 (intExpr z)))) =
                    true
                rw [show Logic.posp (intExpr z) = .t by
                  simp [Logic.posp, intExpr, hz]]
                rw [hLe]
                rfl
              · simp [Logic.implies, Logic.posp, hz]
          | _ =>
              simp [Logic.implies, Logic.posp]
      | _ =>
          simp [Logic.implies, Logic.posp]

/--
Reconstruction of ACL2 theorem `nbr-calls-flog2-upper-bound` from
`acl2_samples/2009-log2.lisp`.
-/
theorem nbr_calls_flog2_upper_bound (n : SExpr) :
    Logic.toBool
      (Logic.and
        (Logic.implies (Logic.and (Logic.posp n) (Logic.evenp n))
          (Logic.le (nbrCallsFlog2 n)
            (Logic.plus (intExpr 1) (Logic.times (intExpr 2) (flog2 n)))))
        (Logic.implies (Logic.and (Logic.posp n) (Logic.oddp n))
          (Logic.le (nbrCallsFlog2 n)
            (Logic.plus (intExpr 2) (Logic.times (intExpr 2) (flog2 n)))))) = true := by
  cases n with
  | nil =>
      simp [Logic.and, Logic.implies, Logic.posp]
  | cons a d =>
      simp [Logic.and, Logic.implies, Logic.posp]
  | atom a =>
      cases a with
      | number value =>
          cases value with
          | int z =>
              have hEven :
                  Logic.implies (Logic.and (Logic.posp (intExpr z)) (Logic.evenp (intExpr z)))
                    (Logic.le (nbrCallsFlog2 (intExpr z))
                      (Logic.plus (intExpr 1) (Logic.times (intExpr 2) (flog2 (intExpr z))))) =
                    .t := by
                by_cases hz : 0 < z
                · by_cases heven : z % 2 = 0
                  · have hHalfPos : 0 < z.toNat / 2 := by
                      omega
                    have hEqNat : z.toNat = 2 * (z.toNat / 2) := by
                      omega
                    have hNat : nbrCallsFlog2Nat z.toNat ≤ 1 + 2 * flog2Nat z.toNat := by
                      rw [hEqNat]
                      simpa using (nbrCallsFlog2Nat_even_upper hHalfPos)
                    have hLe :
                        Logic.le (nbrCallsFlog2 (intExpr z))
                          (Logic.plus (intExpr 1) (Logic.times (intExpr 2) (flog2 (intExpr z)))) =
                          .t := by
                      rw [nbrCallsFlog2_eq_natExpr_of_pos hz, one_plus_two_times_flog2_eq_natExpr_of_pos hz]
                      have hInt :
                          Int.ofNat (nbrCallsFlog2Nat z.toNat) ≤ Int.ofNat (1 + 2 * flog2Nat z.toNat) :=
                        Int.ofNat_le.mpr hNat
                      simpa [Logic.le, toRat, intExpr, natExpr] using hInt
                    rw [show Logic.and (Logic.posp (intExpr z)) (Logic.evenp (intExpr z)) = .t by
                      simp [Logic.and, Logic.posp, Logic.evenp, intExpr, hz, heven]]
                    rw [hLe]
                    rfl
                  · simp [Logic.implies, Logic.and, Logic.posp, intExpr, hz, heven]
                · simp [Logic.implies, Logic.and, Logic.posp, intExpr, hz]
              have hOdd :
                  Logic.implies (Logic.and (Logic.posp (intExpr z)) (Logic.oddp (intExpr z)))
                    (Logic.le (nbrCallsFlog2 (intExpr z))
                      (Logic.plus (intExpr 2) (Logic.times (intExpr 2) (flog2 (intExpr z))))) =
                    .t := by
                by_cases hz : 0 < z
                · by_cases hodd : z % 2 ≠ 0
                  · have hNat : nbrCallsFlog2Nat z.toNat ≤ 2 + 2 * flog2Nat z.toNat :=
                      nbrCallsFlog2Nat_upper z.toNat (int_toNat_pos hz)
                    have hLe :
                        Logic.le (nbrCallsFlog2 (intExpr z))
                          (Logic.plus (intExpr 2) (Logic.times (intExpr 2) (flog2 (intExpr z)))) =
                          .t := by
                      rw [nbrCallsFlog2_eq_natExpr_of_pos hz, two_plus_two_times_flog2_eq_natExpr_of_pos hz]
                      have hInt :
                          Int.ofNat (nbrCallsFlog2Nat z.toNat) ≤ Int.ofNat (2 + 2 * flog2Nat z.toNat) :=
                        Int.ofNat_le.mpr hNat
                      simpa [Logic.le, toRat, intExpr, natExpr] using hInt
                    rw [show Logic.and (Logic.posp (intExpr z)) (Logic.oddp (intExpr z)) = .t by
                      simp [Logic.and, Logic.posp, Logic.oddp, intExpr, hz, hodd]]
                    rw [hLe]
                    rfl
                  · simp [Logic.implies, Logic.and, Logic.posp, intExpr, hz, hodd]
                · simp [Logic.implies, Logic.and, Logic.posp, intExpr, hz]
              change
                Logic.toBool
                  (Logic.and
                    (Logic.implies (Logic.and (Logic.posp (intExpr z)) (Logic.evenp (intExpr z)))
                      (Logic.le (nbrCallsFlog2 (intExpr z))
                        (Logic.plus (intExpr 1) (Logic.times (intExpr 2) (flog2 (intExpr z))))))
                    (Logic.implies (Logic.and (Logic.posp (intExpr z)) (Logic.oddp (intExpr z)))
                      (Logic.le (nbrCallsFlog2 (intExpr z))
                        (Logic.plus (intExpr 2) (Logic.times (intExpr 2) (flog2 (intExpr z))))))) =
                  true
              rw [hEven, hOdd]
              simp [Logic.and]
          | _ =>
              simp [Logic.and, Logic.implies, Logic.posp]
      | _ =>
          simp [Logic.and, Logic.implies, Logic.posp]

/--
Reconstruction of ACL2 theorem `nbr-calls-flog2-is-logarithmic` from
`acl2_samples/2009-log2.lisp`.
-/
theorem nbr_calls_flog2_is_logarithmic (n : SExpr) :
    Logic.toBool
      (Logic.implies (Logic.posp n)
        (Logic.and
          (Logic.le (Logic.plus (intExpr 2) (flog2 n)) (nbrCallsFlog2 n))
          (Logic.le (nbrCallsFlog2 n)
            (Logic.plus (intExpr 2) (Logic.times (intExpr 2) (flog2 n)))))) = true := by
  cases n with
  | nil =>
      simp [Logic.implies, Logic.posp]
  | cons a d =>
      simp [Logic.implies, Logic.posp]
  | atom a =>
      cases a with
      | number value =>
          cases value with
          | int z =>
              by_cases hz : 0 < z
              · have hLowerNat : 2 + flog2Nat z.toNat ≤ nbrCallsFlog2Nat z.toNat :=
                    nbrCallsFlog2Nat_lower z.toNat (int_toNat_pos hz)
                have hUpperNat : nbrCallsFlog2Nat z.toNat ≤ 2 + 2 * flog2Nat z.toNat :=
                    nbrCallsFlog2Nat_upper z.toNat (int_toNat_pos hz)
                have hLower :
                    Logic.le (Logic.plus (intExpr 2) (flog2 (intExpr z))) (nbrCallsFlog2 (intExpr z)) =
                      .t := by
                  rw [two_plus_flog2_eq_natExpr_of_pos hz, nbrCallsFlog2_eq_natExpr_of_pos hz]
                  have hInt :
                      Int.ofNat (2 + flog2Nat z.toNat) ≤ Int.ofNat (nbrCallsFlog2Nat z.toNat) :=
                    Int.ofNat_le.mpr hLowerNat
                  simpa [Logic.le, toRat, intExpr, natExpr] using hInt
                have hUpper :
                    Logic.le (nbrCallsFlog2 (intExpr z))
                      (Logic.plus (intExpr 2) (Logic.times (intExpr 2) (flog2 (intExpr z)))) =
                      .t := by
                  rw [nbrCallsFlog2_eq_natExpr_of_pos hz, two_plus_two_times_flog2_eq_natExpr_of_pos hz]
                  have hInt :
                      Int.ofNat (nbrCallsFlog2Nat z.toNat) ≤ Int.ofNat (2 + 2 * flog2Nat z.toNat) :=
                    Int.ofNat_le.mpr hUpperNat
                  simpa [Logic.le, toRat, intExpr, natExpr] using hInt
                change
                  Logic.toBool
                    (Logic.implies (Logic.posp (intExpr z))
                      (Logic.and
                        (Logic.le (Logic.plus (intExpr 2) (flog2 (intExpr z))) (nbrCallsFlog2 (intExpr z)))
                        (Logic.le (nbrCallsFlog2 (intExpr z))
                          (Logic.plus (intExpr 2) (Logic.times (intExpr 2) (flog2 (intExpr z))))))) =
                    true
                rw [show Logic.posp (intExpr z) = .t by
                  simp [Logic.posp, intExpr, hz]]
                rw [show
                  Logic.and
                    (Logic.le (Logic.plus (intExpr 2) (flog2 (intExpr z))) (nbrCallsFlog2 (intExpr z)))
                    (Logic.le (nbrCallsFlog2 (intExpr z))
                      (Logic.plus (intExpr 2) (Logic.times (intExpr 2) (flog2 (intExpr z))))) =
                  .t by
                  rw [hLower, hUpper]
                  rfl]
                rfl
              · simp [Logic.implies, Logic.posp, hz]
          | _ =>
              simp [Logic.implies, Logic.posp]
      | _ =>
          simp [Logic.implies, Logic.posp]

#guard clog2 (intExpr 1) = intExpr 0
#guard clog2 (intExpr 10) = intExpr 4
#guard nbrCallsClog2 (intExpr 10) = intExpr 5
#guard nbrCallsClog2 (intExpr 17) = intExpr 6

end Log2Replay
end Imported
end ACL2
