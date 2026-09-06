import ACL2Lean.Count

/-! # ACL2-value count for admission measures

The value-level interpretation of `acl2-count` (axioms.lisp), distinct from
the structural `SExpr.consCount`. It supports the emitted complex-component
recursive calls as well as the existing cons/EVENS/ODDS decrease families.
This does not make ACL2-COUNT an evaluator builtin: its emitted definition
and proof obligations still go through the normal replay machinery.
-/

namespace ACL2

def Number.rationalCount (q : Rat) : Nat :=
  if q.den = 1 then q.num.natAbs else q.num.natAbs + q.den

def Number.valueCount : Number → Nat
  | .int n => n.natAbs
  | .rational n d _ => n.natAbs + d
  | .complex r i _ => 1 + rationalCount r + rationalCount i

def SExpr.valueCount : SExpr → Nat
  | .nil => 0
  | .atom (.number n) => n.valueCount
  | .atom (.string s) => s.length
  | .atom _ => 0
  | .cons a b => 1 + a.valueCount + b.valueCount

theorem valueCount_fromRat (q : Rat) :
    (SExpr.atom (.number (Number.fromRat q))).valueCount = Number.rationalCount q := by
  unfold Number.fromRat Number.rationalCount
  split <;> rfl

@[simp] theorem valueCount_nil : SExpr.nil.valueCount = 0 := rfl

@[simp] theorem valueCount_cons (a b : SExpr) :
    (SExpr.cons a b).valueCount = 1 + a.valueCount + b.valueCount := rfl

theorem valueCount_car_lt (a b : SExpr) :
    a.valueCount < (SExpr.cons a b).valueCount := by
  simp [SExpr.valueCount]; omega

theorem valueCount_cdr_lt (a b : SExpr) :
    b.valueCount < (SExpr.cons a b).valueCount := by
  simp [SExpr.valueCount]; omega

theorem valueCount_car_le (x : SExpr) :
    (Logic.car x).valueCount ≤ x.valueCount := by
  cases x <;> simp only [Logic.car, valueCount_nil, valueCount_cons] <;> omega

theorem valueCount_cdr_le (x : SExpr) :
    (Logic.cdr x).valueCount ≤ x.valueCount := by
  cases x <;> simp only [Logic.cdr, valueCount_nil, valueCount_cons] <;> omega

theorem valueCount_car_lt_of_consp {x : SExpr}
    (h : Logic.toBool (Logic.consp x) = true) :
    (Logic.car x).valueCount < x.valueCount := by
  cases x with
  | nil | atom _ => simp [Logic.consp, Logic.toBool] at h
  | cons a b => exact valueCount_car_lt a b

theorem valueCount_cdr_lt_of_consp {x : SExpr}
    (h : Logic.toBool (Logic.consp x) = true) :
    (Logic.cdr x).valueCount < x.valueCount := by
  cases x with
  | nil | atom _ => simp [Logic.consp, Logic.toBool] at h
  | cons a b => exact valueCount_cdr_lt a b

theorem valueCount_cdr_lt_of_not_endp {x : SExpr}
    (h : Logic.toBool (Logic.endp x) = false) :
    (Logic.cdr x).valueCount < x.valueCount := by
  cases x with
  | nil | atom _ => simp [Logic.endp, Logic.toBool] at h
  | cons a b => exact valueCount_cdr_lt a b

/-- The INTERLEAVE admission's emitted swap-and-cdr sum. -/
theorem valueCount_swap_cdr_sum_lt_consp {x : SExpr} {y : SExpr}
    (h : Logic.toBool (Logic.consp x) = true) :
    y.valueCount + (Logic.cdr x).valueCount < x.valueCount + y.valueCount := by
  have := valueCount_cdr_lt_of_consp h
  omega

/-- The O-FIRST-EXPT admission's structural component under its cons ruler. -/
theorem valueCount_car_car_lt_of_consp {x : SExpr}
    (h : Logic.toBool (Logic.consp x) = true) :
    (Logic.car (Logic.car x)).valueCount < x.valueCount :=
  Nat.lt_of_le_of_lt (valueCount_car_le (Logic.car x)) (valueCount_car_lt_of_consp h)

theorem valueCount_realpart_lt_of_complex {x : SExpr}
    (h : Logic.toBool (Logic.complexRationalp x) = true) :
    (Logic.realpart x).valueCount < x.valueCount := by
  cases x with
  | nil | cons _ _ => simp [Logic.complexRationalp, Logic.toBool] at h
  | atom a =>
    cases a with
    | number n =>
      cases n with
      | int _ | rational _ _ _ => simp [Logic.complexRationalp, Logic.toBool] at h
      | complex r i hi =>
        change (SExpr.atom (.number (Number.fromRat r))).valueCount <
          1 + Number.rationalCount r + Number.rationalCount i
        rw [valueCount_fromRat]; omega
    | _ => simp [Logic.complexRationalp, Logic.toBool] at h

theorem valueCount_imagpart_lt_of_complex {x : SExpr}
    (h : Logic.toBool (Logic.complexRationalp x) = true) :
    (Logic.imagpart x).valueCount < x.valueCount := by
  cases x with
  | nil | cons _ _ => simp [Logic.complexRationalp, Logic.toBool] at h
  | atom a =>
    cases a with
    | number n =>
      cases n with
      | int _ | rational _ _ _ => simp [Logic.complexRationalp, Logic.toBool] at h
      | complex r i hi =>
        change (SExpr.atom (.number (Number.fromRat i))).valueCount <
          1 + Number.rationalCount r + Number.rationalCount i
        rw [valueCount_fromRat]; omega
    | _ => simp [Logic.complexRationalp, Logic.toBool] at h

theorem valueCount_evens_le (x : SExpr) :
    (Logic.evens x).valueCount ≤ x.valueCount := by
  cases x with
  | nil | atom _ => simp [Logic.evens]
  | cons a d =>
    cases d with
    | nil | atom _ => simp [Logic.evens, valueCount_cons]
    | cons b d' =>
      simp only [Logic.evens, valueCount_cons]
      have ih := valueCount_evens_le d'
      omega
termination_by x.consCount
decreasing_by simp [SExpr.consCount]; omega

theorem valueCount_evens_lt {x : SExpr}
    (h1 : Logic.toBool (Logic.endp x) = false)
    (h2 : Logic.toBool (Logic.endp (Logic.cdr x)) = false) :
    (Logic.evens x).valueCount < x.valueCount := by
  cases x with
  | nil | atom _ => simp [Logic.endp, Logic.toBool] at h1
  | cons a d =>
    cases d with
    | nil | atom _ => simp [Logic.cdr, Logic.endp, Logic.toBool] at h2
    | cons b d' =>
      simp only [Logic.evens, valueCount_cons]
      have ih := valueCount_evens_le d'
      omega

theorem valueCount_odds_lt {x : SExpr}
    (h1 : Logic.toBool (Logic.endp x) = false)
    (h2 : Logic.toBool (Logic.endp (Logic.cdr x)) = false) :
    (Logic.odds x).valueCount < x.valueCount := by
  cases x with
  | nil | atom _ => simp [Logic.endp, Logic.toBool] at h1
  | cons a d =>
    cases d with
    | nil | atom _ => simp [Logic.cdr, Logic.endp, Logic.toBool] at h2
    | cons b d' =>
      simp only [Logic.odds, Logic.cdr, valueCount_cons]
      have ih := valueCount_evens_le (.cons b d')
      simp only [valueCount_cons] at ih
      omega

end ACL2
