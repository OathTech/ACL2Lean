import ACL2Lean.Logic

namespace ACL2

open Logic hiding toBool

/-- CONS-cell count — the structural size measure the totality prover's
    Count library is built on. Renamed from `acl2Count` (audit 2026-07-26,
    refuted-finding residue): it is NOT ACL2's `acl2-count` — real ACL2
    gives `(acl2-count 100) = 100` (integer magnitude), `(acl2-count "ab")
    = 2`, etc., where this gives 0 for every atom. No obligation is
    misstated by the difference (`mkTotalityHypType` builds pure
    interpreter convergence with no measure term at all; the decrease
    prover discharges ACL2's own emitted `o<` clauses), but the old name
    claimed a faithfulness the function does not have.
    Returns 0 for nil and atoms, and `1 + car.consCount + cdr.consCount`
    for cons cells. -/
def SExpr.consCount : SExpr → Nat
  | .nil => 0
  | .atom _ => 0
  | .cons a b => 1 + a.consCount + b.consCount

@[simp] theorem consCount_nil : SExpr.nil.consCount = 0 := rfl

@[simp] theorem consCount_atom (a : Atom) : (SExpr.atom a).consCount = 0 := rfl

@[simp] theorem consCount_cons (a b : SExpr) :
    (SExpr.cons a b).consCount = 1 + a.consCount + b.consCount := rfl

/-- car of a cons has strictly smaller consCount. -/
theorem consCount_car_lt (a b : SExpr) :
    a.consCount < (SExpr.cons a b).consCount := by
  simp [SExpr.consCount]; omega

/-- cdr of a cons has strictly smaller consCount. -/
theorem consCount_cdr_lt (a b : SExpr) :
    b.consCount < (SExpr.cons a b).consCount := by
  simp [SExpr.consCount]; omega

/-- consCount of car decreases for consp values. -/
theorem consCount_car_lt_of_consp {x : SExpr}
    (h : Logic.toBool (consp x) = true) :
    (car x).consCount < x.consCount := by
  cases x with
  | nil => simp [consp, Logic.toBool] at h
  | atom _ => simp [consp, Logic.toBool] at h
  | cons a b => simp [car, SExpr.consCount]; omega

/-- consCount of cdr decreases for consp values. -/
theorem consCount_cdr_lt_of_consp {x : SExpr}
    (h : Logic.toBool (consp x) = true) :
    (cdr x).consCount < x.consCount := by
  cases x with
  | nil => simp [consp, Logic.toBool] at h
  | atom _ => simp [consp, Logic.toBool] at h
  | cons a b => simp [cdr, SExpr.consCount]; omega

/-- cdr never increases consCount (cdr of a non-cons is nil, count 0) —
    the unconditional ≤ step of destructor-chain decreases (#37 rework). -/
theorem consCount_cdr_le (x : SExpr) : (cdr x).consCount ≤ x.consCount := by
  cases x with
  | nil => simp [cdr]
  | atom _ => simp [cdr]
  | cons a b => simp only [cdr, SExpr.consCount]; omega

/-- car never increases consCount — the unconditional ≤ step (#37 rework). -/
theorem consCount_car_le (x : SExpr) : (car x).consCount ≤ x.consCount := by
  cases x with
  | nil => simp [car]
  | atom _ => simp [car]
  | cons a b => simp only [car, SExpr.consCount]; omega

/-- consCount of cdr decreases when endp is false (not at end of list). -/
theorem consCount_cdr_lt_of_not_endp {x : SExpr}
    (h : Logic.toBool (endp x) = false) :
    (cdr x).consCount < x.consCount := by
  cases x with
  | nil => simp [endp, Logic.toBool] at h
  | atom _ => simp [endp, Logic.toBool] at h
  | cons a b => simp [cdr, SExpr.consCount]; omega

/-- When cdr of x decreases consCount, the sum with any other term also decreases. -/
theorem consCount_cdr_sum_lt_left {x : SExpr} {y : SExpr}
    (h : Logic.toBool (endp x) = false) :
    (cdr x).consCount + y.consCount < x.consCount + y.consCount := by
  have := consCount_cdr_lt_of_not_endp h
  omega

/-- When cdr of y decreases consCount, the sum with any other term also decreases. -/
theorem consCount_cdr_sum_lt_right {x : SExpr} {y : SExpr}
    (h : Logic.toBool (endp y) = false) :
    x.consCount + (cdr y).consCount < x.consCount + y.consCount := by
  have := consCount_cdr_lt_of_not_endp h
  omega

/-- When cdr of x decreases consCount via consp, the sum also decreases. -/
theorem consCount_cdr_sum_lt_left_consp {x : SExpr} {y : SExpr}
    (h : Logic.toBool (consp x) = true) :
    (cdr x).consCount + y.consCount < x.consCount + y.consCount := by
  have := consCount_cdr_lt_of_consp h
  omega

/-- When cdr of y decreases consCount via consp, the sum also decreases. -/
theorem consCount_cdr_sum_lt_right_consp {x : SExpr} {y : SExpr}
    (h : Logic.toBool (consp y) = true) :
    x.consCount + (cdr y).consCount < x.consCount + y.consCount := by
  have := consCount_cdr_lt_of_consp h
  omega

/-- The SWAP-sum decrease (INTERLEAVE's scheme, J1(b)-validated): swapping
    the measured pair to `(y, cdr x)` decreases the sum when `x` is a cons —
    the emitted clause `((ATOM X) (O< (+ (ac Y) (ac (CDR X)))
    (+ (ac X) (ac Y))))` at the value level. -/
theorem consCount_swap_cdr_sum_lt_consp {x : SExpr} {y : SExpr}
    (h : Logic.toBool (consp x) = true) :
    y.consCount + (cdr x).consCount < x.consCount + y.consCount := by
  have := consCount_cdr_lt_of_consp h
  omega

/-- consCount of evens is at most consCount of the input. -/
theorem consCount_evens_le (x : SExpr) : (evens x).consCount ≤ x.consCount := by
  cases x with
  | nil => simp [evens]
  | atom _ => simp [evens]
  | cons a d =>
    cases d with
    | nil => simp [evens, SExpr.consCount]
    | atom _ => simp [evens, SExpr.consCount]
    | cons b d' =>
      simp only [evens, SExpr.consCount]
      have ih := consCount_evens_le d'
      omega
termination_by x.consCount
decreasing_by simp [SExpr.consCount]; omega

/-- consCount of evens is strictly less when the list has 2+ elements. -/
theorem consCount_evens_lt {x : SExpr}
    (h1 : Logic.toBool (endp x) = false)
    (h2 : Logic.toBool (endp (cdr x)) = false) :
    (evens x).consCount < x.consCount := by
  cases x with
  | nil => simp [endp, Logic.toBool] at h1
  | atom _ => simp [endp, Logic.toBool] at h1
  | cons a d =>
    cases d with
    | nil => simp [cdr, endp, Logic.toBool] at h2
    | atom _ => simp [cdr, endp, Logic.toBool] at h2
    | cons b d' =>
      simp only [evens, SExpr.consCount]
      have ih := consCount_evens_le d'
      omega

/-- consCount of odds is strictly less when the list has 2+ elements. -/
theorem consCount_odds_lt {x : SExpr}
    (h1 : Logic.toBool (endp x) = false)
    (h2 : Logic.toBool (endp (cdr x)) = false) :
    (odds x).consCount < x.consCount := by
  cases x with
  | nil => simp [endp, Logic.toBool] at h1
  | atom _ => simp [endp, Logic.toBool] at h1
  | cons a d =>
    cases d with
    | nil => simp [cdr, endp, Logic.toBool] at h2
    | atom _ => simp [cdr, endp, Logic.toBool] at h2
    | cons b d' =>
      simp only [odds, cdr, SExpr.consCount]
      have ih := consCount_evens_le (.cons b d')
      simp [SExpr.consCount] at ih
      omega

end ACL2
