import ACL2Lean.Logic
import Init.Data.Rat.Lemmas

/-! # Canonical numeric correspondence

Generic representation and arithmetic facts for the primitive evaluator.
The component view covers every ACL2 number, including genuine complexes;
nonnumbers use ACL2's zero completion. These facts restore the unconditional
ground-zero arithmetic rules after BUG-009's value-domain extension.
-/

namespace ACL2.Logic

theorem rationalValue_fromRat (q : Rat) :
    rationalValue (.atom (.number (Number.fromRat q))) = q := by
  unfold Number.fromRat
  split
  · next hd =>
    apply Rat.ext <;> simp [rationalValue, hd]
  · rfl

theorem mkParts_zero (q : Rat) :
    mkParts q 0 = .atom (.number (Number.fromRat q)) := rfl

theorem numberParts_fromRat (q : Rat) :
    numberParts (.atom (.number (Number.fromRat q))) = (q, 0) := by
  unfold Number.fromRat
  split
  · next hd =>
    change (Rat.ofInt q.num, (0 : Rat)) = (q, 0)
    apply Prod.ext
    · apply Rat.ext <;> simp [hd]
    · rfl
  · rfl

theorem numberParts_mkParts (r i : Rat) :
    numberParts (mkParts r i) = (r, i) := by
  by_cases hi : i.num = 0
  · have hz := Rat.num_eq_zero.mp hi
    subst i
    exact numberParts_fromRat r
  · simp [mkParts, Number.fromParts, hi, numberParts]

theorem mkNumber_eq_fromRat (n : Int) (d : Nat) :
    mkNumber n d = .atom (.number (Number.fromRat (mkRat n d))) := by
  by_cases hd : d = 0
  · subst d; simp [mkNumber, Number.fromRat]
  · simp [mkNumber, Number.fromRat, Rat.num_mkRat, Rat.den_mkRat, hd,
      Nat.gcd_comm, Int.ofNat_eq_natCast]
    split <;> simp_all

theorem rationalValue_num_den (s : SExpr) :
    (rationalValue s).num = (toRat s).1 ∧
    (rationalValue s).den = (toRat s).2 := by
  cases s with
  | nil | cons _ _ => exact ⟨rfl, rfl⟩
  | atom a =>
    cases a with
    | number n => cases n <;> exact ⟨rfl, rfl⟩
    | _ => exact ⟨rfl, rfl⟩

theorem numberParts_of_not_complex (s : SExpr) (h : isComplex s = false) :
    numberParts s = (rationalValue s, 0) := by
  cases s with
  | nil | cons _ _ => rfl
  | atom a =>
    cases a with
    | number n =>
      cases n with
      | int _ | rational _ _ _ => rfl
      | complex _ _ _ => simp [isComplex] at h
    | _ => rfl

/-- Addition through the canonical component view; no rational-only premise. -/
theorem plus_parts (a b : SExpr) :
    plus a b = mkParts ((numberParts a).1 + (numberParts b).1)
      ((numberParts a).2 + (numberParts b).2) := by
  by_cases h : (isComplex a || isComplex b) = true
  · simp only [plus, h, ↓reduceIte]
  · have ha : isComplex a = false := by simpa using (Bool.or_eq_false_iff.mp
      (Bool.eq_false_iff.mpr h)).1
    have hb : isComplex b = false := by simpa using (Bool.or_eq_false_iff.mp
      (Bool.eq_false_iff.mpr h)).2
    rw [numberParts_of_not_complex a ha, numberParts_of_not_complex b hb]
    simp only [Rat.add_zero, mkParts_zero, plus, ha, hb, Bool.false_or,
      Bool.false_eq_true, ↓reduceIte]
    rw [mkNumber_eq_fromRat, Rat.add_def']
    rcases rationalValue_num_den a with ⟨han, had⟩
    rcases rationalValue_num_den b with ⟨hbn, hbd⟩
    rw [han, had, hbn, hbd]

theorem plus_comm (a b : SExpr) : plus a b = plus b a := by
  rw [plus_parts, plus_parts, Rat.add_comm (numberParts a).1,
    Rat.add_comm (numberParts a).2]

theorem plus_assoc (a b c : SExpr) :
    plus (plus a b) c = plus a (plus b c) := by
  simp only [plus_parts, numberParts_mkParts]
  rw [Rat.add_assoc, Rat.add_assoc]

/-- Additive normalization without expanding the completed numeric values. -/
theorem plus_left_comm (a b c : SExpr) : plus a (plus b c) = plus b (plus a c) := by
  rw [← plus_assoc, plus_comm a b, plus_assoc]

end ACL2.Logic
