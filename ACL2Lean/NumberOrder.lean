import ACL2Lean.Lexorder
import Init.Data.Rat.Lemmas

/-! # Numeric alphorder facts

Canonical rationals in value order, followed by genuine complexes in
real/imaginary component order. These generic primitive facts feed the
ground-zero lexorder rules; they prove no book theorem. Core-only imports
preserve the String order used by LexorderOrder.
-/

namespace ACL2
open Logic

/-! ## Within-class facts: numbers -/

/-- Unpack the canonicity invariant. -/
private theorem canonRat_facts {n : Int} {d : Nat} (h : canonRat n d = true) :
    2 ≤ d ∧ Nat.gcd n.natAbs d = 1 := by
  simpa [canonRat] using h

/-- The denominator `toRat` extracts from a (canonical) number is positive. -/
private theorem den_pos (v : Number) :
    0 < (Logic.toRat (.atom (.number v))).2 := by
  cases v with
  | int n => simp [Logic.toRat]
  | rational n d hc =>
    have := (canonRat_facts hc).1
    simp only [Logic.toRat]
    omega
  | complex _ _ _ => simp [Logic.toRat]

private theorem mul_right_comm' (a b c : Int) : a * b * c = a * c * b := by
  rw [Int.mul_assoc, Int.mul_comm b c, ← Int.mul_assoc]

/-- Transitivity of the cross-multiplication order on exact rationals:
    `n1/d1 ≤ n2/d2 ≤ n3/d3` (as `nᵢ*dⱼ ≤ nⱼ*dᵢ`) chains, cancelling the
    positive middle denominator. -/
private theorem cross_le_trans {n1 n2 n3 : Int} {d1 d2 d3 : Nat}
    (hd2 : 0 < d2)
    (h12 : n1 * (d2 : Int) ≤ n2 * (d1 : Int))
    (h23 : n2 * (d3 : Int) ≤ n3 * (d2 : Int)) :
    n1 * (d3 : Int) ≤ n3 * (d1 : Int) := by
  have h1 : n1 * d2 * d3 ≤ n2 * d1 * d3 :=
    Int.mul_le_mul_of_nonneg_right h12 (Int.natCast_nonneg d3)
  have h2 : n2 * d3 * d1 ≤ n3 * d2 * d1 :=
    Int.mul_le_mul_of_nonneg_right h23 (Int.natCast_nonneg d1)
  have h3 : n1 * d2 * d3 ≤ n3 * d2 * d1 := by
    refine Int.le_trans h1 ?_
    rw [mul_right_comm' n2 d1 d3]
    exact h2
  have h4 : n1 * d3 * d2 ≤ n3 * d1 * d2 := by
    rw [mul_right_comm' n1 d3 d2, mul_right_comm' n3 d1 d2]
    exact h3
  exact Int.le_of_mul_le_mul_right h4 (by omega)

/-- A canonical rational is never integral: `m * d = n` is impossible when
    `(n, d)` is canonical (`d ≥ 2` would divide `n`, contradicting
    reducedness). -/
private theorem cross_ne_int {m n : Int} {d : Nat} (hc : canonRat n d = true) :
    m * (d : Int) ≠ n := by
  intro h
  rcases canonRat_facts hc with ⟨hd2, hcop⟩
  have hdvd : (d : Int) ∣ n := ⟨m, by rw [← h]; exact Int.mul_comm m d⟩
  have hdvd' : d ∣ n.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  have hg : d ∣ Nat.gcd n.natAbs d := Nat.dvd_gcd hdvd' (Nat.dvd_refl d)
  rw [hcop] at hg
  have := Nat.le_of_dvd Nat.one_pos hg
  omega

/-- INJECTIVITY of the exact rational value on canonical rationals: equal
    cross-products mean equal `Number`s. This is where the BUG-012
    canonical-`Number` invariant pays off — without it (e.g. with `2/4` and
    `1/2` both representable) this, and hence lexorder antisymmetry, is
    FALSE. -/
private theorem rational_eq_of_cross_eq {v1 v2 : Number}
    (hr1 : Logic.isComplex (.atom (.number v1)) = false)
    (hr2 : Logic.isComplex (.atom (.number v2)) = false)
    (h : (Logic.toRat (.atom (.number v1))).1
           * ((Logic.toRat (.atom (.number v2))).2 : Int)
       = (Logic.toRat (.atom (.number v2))).1
           * ((Logic.toRat (.atom (.number v1))).2 : Int)) :
    v1 = v2 := by
  cases v1 with
  | complex _ _ _ => simp [Logic.isComplex] at hr1
  | int m =>
    cases v2 with
    | complex _ _ _ => simp [Logic.isComplex] at hr2
    | int n =>
      simp [Logic.toRat] at h
      exact congrArg Number.int h
    | rational n d hc =>
      simp [Logic.toRat] at h
      exact absurd h (cross_ne_int hc)
  | rational n d hc =>
    cases v2 with
    | complex _ _ _ => simp [Logic.isComplex] at hr2
    | int m =>
      simp [Logic.toRat] at h
      exact absurd h.symm (cross_ne_int hc)
    | rational n2 d2 hc2 =>
      simp only [Logic.toRat] at h
      rcases canonRat_facts hc with ⟨hd2, hcop⟩
      rcases canonRat_facts hc2 with ⟨hd2', hcop2⟩
      -- |n|·d2 = |n2|·d, then coprimality forces d = d2, then n = n2
      have habs : n.natAbs * d2 = n2.natAbs * d := by
        have := congrArg Int.natAbs h
        simpa [Int.natAbs_mul] using this
      have hdd2 : d ∣ d2 := by
        have hdvd : d ∣ n.natAbs * d2 :=
          ⟨n2.natAbs, by rw [habs]; exact Nat.mul_comm _ _⟩
        exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left hdvd
      have hd2d : d2 ∣ d := by
        have hdvd : d2 ∣ n2.natAbs * d :=
          ⟨n.natAbs, by rw [← habs]; exact Nat.mul_comm _ _⟩
        exact (Nat.Coprime.symm hcop2).dvd_of_dvd_mul_left hdvd
      have hdeq : d = d2 := Nat.dvd_antisymm hdd2 hd2d
      subst hdeq
      have hneq : n = n2 :=
        Int.eq_of_mul_eq_mul_right (by omega : (d : Int) ≠ 0) h
      subst hneq
      rfl

private theorem complexPartsLe_antisymm {ar ai br bi : Rat}
    (hab : ar < br ∨ (ar = br ∧ ai ≤ bi))
    (hba : br < ar ∨ (br = ar ∧ bi ≤ ai)) : ar = br ∧ ai = bi := by
  have hr : ar = br := Rat.le_antisymm
    (hab.elim Rat.le_of_lt (fun h => h.1 ▸ Rat.le_refl))
    (hba.elim Rat.le_of_lt (fun h => h.1 ▸ Rat.le_refl))
  subst br
  simp only [Rat.lt_irrefl, false_or, true_and] at hab hba
  exact ⟨rfl, Rat.le_antisymm hab hba⟩

private theorem complexPartsLe_trans {ar ai br bi cr ci : Rat}
    (hab : ar < br ∨ (ar = br ∧ ai ≤ bi))
    (hbc : br < cr ∨ (br = cr ∧ bi ≤ ci)) :
    ar < cr ∨ (ar = cr ∧ ai ≤ ci) := by
  rcases hab with hab | ⟨hr, hi⟩
  · rcases hbc with hbc | ⟨hr, _⟩
    · exact Or.inl (Rat.lt_of_le_of_ne
        (Rat.le_trans (Rat.le_of_lt hab) (Rat.le_of_lt hbc)) (by
          intro h; subst cr
          exact (Rat.not_le.mpr hab) (Rat.le_of_lt hbc)))
    · exact Or.inl (hr ▸ hab)
  · subst br
    rcases hbc with hbc | ⟨hr, hi'⟩
    · exact Or.inl hbc
    · exact Or.inr ⟨hr, Rat.le_trans hi hi'⟩

private theorem complexPartsLe_total (ar ai br bi : Rat) :
    (ar < br ∨ (ar = br ∧ ai ≤ bi)) ∨
    (br < ar ∨ (br = ar ∧ bi ≤ ai)) := by
  by_cases hr : ar = br
  · subst br
    rcases Rat.le_total (a := ai) (b := bi) with h | h
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inr ⟨rfl, h⟩)
  · rcases Rat.le_total (a := ar) (b := br) with h | h
    · exact Or.inl (Or.inl (Rat.lt_of_le_of_ne h hr))
    · exact Or.inr (Or.inl (Rat.lt_of_le_of_ne h (Ne.symm hr)))

theorem numberLe_refl (v : Number) : numberLe v v = true := by
  cases v <;> simp [numberLe, Rat.lt_irrefl]

theorem numberLe_antisymm {a b : Number}
    (hab : numberLe a b = true) (hba : numberLe b a = true) : a = b := by
  cases a <;> cases b <;>
    simp only [numberLe, decide_eq_true_eq] at hab hba
  all_goals first
    | contradiction
    | exact rational_eq_of_cross_eq rfl rfl (Int.le_antisymm hab hba)
    | obtain ⟨hr, hi⟩ := complexPartsLe_antisymm hab hba
      subst hr; subst hi; rfl

theorem numberLe_trans {a b c : Number}
    (hab : numberLe a b = true) (hbc : numberLe b c = true) :
    numberLe a c = true := by
  cases a <;> cases b <;> cases c <;>
    simp only [numberLe, decide_eq_true_eq] at hab hbc ⊢
  all_goals first
    | contradiction
    | rfl
    | exact cross_le_trans (den_pos _) hab hbc
    | exact complexPartsLe_trans hab hbc

theorem numberLe_total (a b : Number) :
    numberLe a b = true ∨ numberLe b a = true := by
  cases a <;> cases b <;> simp only [numberLe, decide_eq_true_eq]
  all_goals first
    | exact Or.inl True.intro
    | exact Or.inr True.intro
    | exact Int.le_total _ _
    | exact complexPartsLe_total _ _ _ _

end ACL2
