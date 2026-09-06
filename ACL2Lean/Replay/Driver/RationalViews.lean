import ACL2Lean.Replay.Driver.NodeCore
import ACL2Lean.NumericOrder
import ACL2Lean.NumericMultiplication

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

private theorem rationalView (v : SExpr) (h : Logic.rationalp v ≠ .nil) :
    ∃ q : Rat, v = .atom (.number (Number.fromRat q)) := by
  have hv : Logic.isComplex v = false ∧ Logic.fix v = v := by
    cases v with
    | nil | cons _ _ => simp [Logic.rationalp] at h
    | atom a => cases a with
      | number n => cases n <;> simp_all [Logic.rationalp, Logic.isComplex, Logic.fix]
      | _ => simp [Logic.rationalp] at h
  refine ⟨Logic.rationalValue v, ?_⟩
  have hm := Logic.mkParts_numberParts v
  rw [Logic.numberParts_of_not_complex v hv.1] at hm
  exact hv.2.symm.trans hm.symm

private theorem rationalpFromRat (q : Rat) :
    Logic.rationalp (.atom (.number (Number.fromRat q))) = .t := by
  unfold Number.fromRat
  split <;> rfl

private theorem equalNil (a b : SExpr) : Logic.equal a b = .nil ↔ a ≠ b := by
  simpa only [ne_eq, not_not] using not_congr (Logic.equal_ne_nil_iff a b)

private theorem fromRatZero (q : Rat) :
    SExpr.atom (.number (Number.fromRat q)) = .atom (.number (.int (Int.ofNat 0))) ↔ q = 0 := by
  constructor
  · intro h
    have hh := congrArg Logic.rationalValue h
    exact (Logic.rationalValue_fromRat q).symm.trans (hh.trans (by decide))
  · rintro rfl
    rfl

private theorem fromRatNeZero (q : Rat) :
    SExpr.atom (.number (Number.fromRat q)) ≠ .atom (.number (.int (Int.ofNat 0))) ↔ q ≠ 0 :=
  not_congr (fromRatZero q)

/-- Extract rational witnesses only from actual recognizer premises in the
DP obligation. Each step removes one SExpr binder; no type is inferred. -/
partial def introDpRationalValues (g : MVarId) : MetaM (MVarId × Bool) := do
  let prf? ← g.withContext do
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let some (_, lhs, rhs) := d.type.eq? | continue
      unless rhs.isConstOf ``SExpr.nil && lhs.isAppOfArity ``Logic.not 1 do continue
      let p := lhs.appArg!
      unless p.isAppOfArity ``Logic.rationalp 1 && p.appArg!.isFVar do continue
      let hn ← mkAppM ``logic_not_nil_ne #[p, mkFVar d.fvarId]
      return some (← mkAppM ``rationalView #[p.appArg!, hn])
    return none
  let some prf := prf? | return (g, false)
  let g ← g.assert `hRationalAtom (← g.withContext (inferType prf)) prf
  let (exFv, g) ← g.intro1P
  let #[sub] ← g.cases exFv | throwError "rational existential split"
  let (g, _) ← introDpRationalValues (← Lean.Meta.subst sub.mvarId sub.fields[1]!.fvarId!)
  return (g, true)

/-- Primitive rational comparison normalization for recorded verdict leaves.
The clause and its rational premises are unchanged; this is used only inside
proveDpFact's existing bounded direct attempt. -/
def dpRationalViewTactic : MetaM (TSyntax `tactic) :=
  `(tactic|
    (try simp_all only [rationalpFromRat, Logic.not, Logic.toBool, SExpr.t,
      reduceCtorEq, Logic.equal_ne_nil_iff, logic_not_equal_nil_iff, equalNil, fromRatZero, fromRatNeZero]) <;>
    (try simp_all only [Logic.lt_parts, Logic.times_parts,
      Logic.numberParts_mkParts, Logic.numberParts_fromRat]) <;>
    (simp_all only [show Logic.numberParts (.atom (.number (.int (Int.ofNat 0)))) = ((0 : Rat), (0 : Rat)) from (by decide),
      Prod.fst, Prod.snd, Rat.mul_zero, Rat.zero_mul, Rat.add_zero, Rat.sub_eq_add_neg, Rat.neg_zero,
      Rat.lt_irrefl, and_false, or_false]) <;>
    (try split_ifs at *) <;>
    simp_all only [Logic.toBool, Logic.not, SExpr.t, reduceCtorEq,
      ite_true, ite_false, not_false_eq_true, fromRatNeZero] <;>
    first | nlinarith | grind -matchEqs -splitMatch [Rat.mul_neg_iff_of_pos_left,
      Rat.mul_neg_iff_of_pos_right, Rat.mul_nonneg, Rat.mul_pos])

/-- Try the rational representation on a fresh goal, assigning the original
only after all resulting obligations close. Failed normalization leaves the
ordinary DP route its original context. The caller owns the existing budget. -/
def closeDpRationalValues (g : MVarId)
    (close : MVarId → MetaM (List MVarId)) : MetaM Bool := g.withContext do
  let mv ← mkFreshExprMVar (← g.getType)
  let (view, changed) ← introDpRationalValues mv.mvarId!
  unless changed do return false
  let remaining ← close view
  unless remaining.isEmpty do return false
  g.assign (← instantiateMVars mv)
  return true

end ACL2.Replay.Driver
