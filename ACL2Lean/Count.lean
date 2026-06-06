import ACL2Lean.Logic

namespace ACL2

open Logic hiding toBool

/-- ACL2-count structural size measure for termination proofs.
    Returns 0 for nil and atoms, and `1 + car.acl2Count + cdr.acl2Count` for cons cells. -/
def SExpr.acl2Count : SExpr → Nat
  | .nil => 0
  | .atom _ => 0
  | .cons a b => 1 + a.acl2Count + b.acl2Count

@[simp] theorem acl2Count_nil : SExpr.nil.acl2Count = 0 := rfl

@[simp] theorem acl2Count_atom (a : Atom) : (SExpr.atom a).acl2Count = 0 := rfl

@[simp] theorem acl2Count_cons (a b : SExpr) :
    (SExpr.cons a b).acl2Count = 1 + a.acl2Count + b.acl2Count := rfl

/-- car of a cons has strictly smaller acl2Count. -/
theorem acl2Count_car_lt (a b : SExpr) :
    a.acl2Count < (SExpr.cons a b).acl2Count := by
  simp [SExpr.acl2Count]; omega

/-- cdr of a cons has strictly smaller acl2Count. -/
theorem acl2Count_cdr_lt (a b : SExpr) :
    b.acl2Count < (SExpr.cons a b).acl2Count := by
  simp [SExpr.acl2Count]; omega

/-- acl2Count of car decreases for consp values. -/
theorem acl2Count_car_lt_of_consp {x : SExpr}
    (h : Logic.toBool (consp x) = true) :
    (car x).acl2Count < x.acl2Count := by
  cases x with
  | nil => simp [consp, Logic.toBool] at h
  | atom _ => simp [consp, Logic.toBool] at h
  | cons a b => simp [car, SExpr.acl2Count]; omega

/-- acl2Count of cdr decreases for consp values. -/
theorem acl2Count_cdr_lt_of_consp {x : SExpr}
    (h : Logic.toBool (consp x) = true) :
    (cdr x).acl2Count < x.acl2Count := by
  cases x with
  | nil => simp [consp, Logic.toBool] at h
  | atom _ => simp [consp, Logic.toBool] at h
  | cons a b => simp [cdr, SExpr.acl2Count]; omega

/-- acl2Count of cdr decreases when endp is false (not at end of list). -/
theorem acl2Count_cdr_lt_of_not_endp {x : SExpr}
    (h : Logic.toBool (endp x) = false) :
    (cdr x).acl2Count < x.acl2Count := by
  cases x with
  | nil => simp [endp, Logic.toBool] at h
  | atom _ => simp [endp, Logic.toBool] at h
  | cons a b => simp [cdr, SExpr.acl2Count]; omega

/-- When cdr of x decreases acl2Count, the sum with any other term also decreases. -/
theorem acl2Count_cdr_sum_lt_left {x : SExpr} {y : SExpr}
    (h : Logic.toBool (endp x) = false) :
    (cdr x).acl2Count + y.acl2Count < x.acl2Count + y.acl2Count := by
  have := acl2Count_cdr_lt_of_not_endp h
  omega

/-- When cdr of y decreases acl2Count, the sum with any other term also decreases. -/
theorem acl2Count_cdr_sum_lt_right {x : SExpr} {y : SExpr}
    (h : Logic.toBool (endp y) = false) :
    x.acl2Count + (cdr y).acl2Count < x.acl2Count + y.acl2Count := by
  have := acl2Count_cdr_lt_of_not_endp h
  omega

/-- When cdr of x decreases acl2Count via consp, the sum also decreases. -/
theorem acl2Count_cdr_sum_lt_left_consp {x : SExpr} {y : SExpr}
    (h : Logic.toBool (consp x) = true) :
    (cdr x).acl2Count + y.acl2Count < x.acl2Count + y.acl2Count := by
  have := acl2Count_cdr_lt_of_consp h
  omega

/-- When cdr of y decreases acl2Count via consp, the sum also decreases. -/
theorem acl2Count_cdr_sum_lt_right_consp {x : SExpr} {y : SExpr}
    (h : Logic.toBool (consp y) = true) :
    x.acl2Count + (cdr y).acl2Count < x.acl2Count + y.acl2Count := by
  have := acl2Count_cdr_lt_of_consp h
  omega

/-- acl2Count of evens is at most acl2Count of the input. -/
theorem acl2Count_evens_le (x : SExpr) : (evens x).acl2Count ≤ x.acl2Count := by
  cases x with
  | nil => simp [evens]
  | atom _ => simp [evens]
  | cons a d =>
    cases d with
    | nil => simp [evens, SExpr.acl2Count]
    | atom _ => simp [evens, SExpr.acl2Count]
    | cons b d' =>
      simp only [evens, SExpr.acl2Count]
      have ih := acl2Count_evens_le d'
      omega
termination_by x.acl2Count
decreasing_by simp [SExpr.acl2Count]; omega

/-- acl2Count of evens is strictly less when the list has 2+ elements. -/
theorem acl2Count_evens_lt {x : SExpr}
    (h1 : Logic.toBool (endp x) = false)
    (h2 : Logic.toBool (endp (cdr x)) = false) :
    (evens x).acl2Count < x.acl2Count := by
  cases x with
  | nil => simp [endp, Logic.toBool] at h1
  | atom _ => simp [endp, Logic.toBool] at h1
  | cons a d =>
    cases d with
    | nil => simp [cdr, endp, Logic.toBool] at h2
    | atom _ => simp [cdr, endp, Logic.toBool] at h2
    | cons b d' =>
      simp only [evens, SExpr.acl2Count]
      have ih := acl2Count_evens_le d'
      omega

/-- acl2Count of odds is strictly less when the list has 2+ elements. -/
theorem acl2Count_odds_lt {x : SExpr}
    (h1 : Logic.toBool (endp x) = false)
    (h2 : Logic.toBool (endp (cdr x)) = false) :
    (odds x).acl2Count < x.acl2Count := by
  cases x with
  | nil => simp [endp, Logic.toBool] at h1
  | atom _ => simp [endp, Logic.toBool] at h1
  | cons a d =>
    cases d with
    | nil => simp [cdr, endp, Logic.toBool] at h2
    | atom _ => simp [cdr, endp, Logic.toBool] at h2
    | cons b d' =>
      simp only [odds, cdr, SExpr.acl2Count]
      have ih := acl2Count_evens_le (.cons b d')
      simp [SExpr.acl2Count] at ih
      omega

end ACL2
