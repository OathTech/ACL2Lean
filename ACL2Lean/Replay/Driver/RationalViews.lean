import ACL2Lean.Replay.Driver.NodeCore
import ACL2Lean.NumericOrder
import ACL2Lean.NumericMultiplication
import ACL2Lean.NumericComponents

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

private partial def rationalPremise? (proof : Expr) : MetaM (Option Expr) := do
  let ty ← inferType proof
  if ty.isAppOfArity ``And 2 then
    if let some h ← rationalPremise? (← mkAppM ``And.left #[proof]) then return some h
    return ← rationalPremise? (← mkAppM ``And.right #[proof])
  if let some (_, lhs, rhs) := ty.eq? then
    if rhs.isConstOf ``SExpr.nil && lhs.isAppOfArity ``Logic.not 1 then
      let p := lhs.appArg!
      if p.isAppOfArity ``Logic.rationalp 1 && p.appArg!.isFVar then
        return some (← mkAppM ``rationalView #[p.appArg!, ← mkAppM ``logic_not_nil_ne #[p, proof]])
  if ty.isAppOfArity ``Not 1 then
    if let some (_, lhs, rhs) := ty.appArg!.eq? then
      if rhs.isConstOf ``SExpr.nil && lhs.isAppOfArity ``Logic.rationalp 1 && lhs.appArg!.isFVar then
        return some (← mkAppM ``rationalView #[lhs.appArg!, proof])
  return none

/-- Extract rational witnesses only from actual recognizer premises in the
DP obligation, including conjunctions introduced by an implication. Each
step removes one SExpr binder; no type is inferred. -/
partial def introDpRationalValues (g : MVarId) : MetaM (MVarId × Bool) := do
  let prf? ← g.withContext do
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if let some h ← rationalPremise? (mkFVar d.fvarId) then return some h
    return none
  let some prf := prf? | return (g, false)
  let g ← g.assert `hRationalAtom (← g.withContext (inferType prf)) prf
  let (exFv, g) ← g.intro1P
  let #[sub] ← g.cases exFv | throwError "rational existential split"
  let (g, _) ← introDpRationalValues (← Lean.Meta.subst sub.mvarId sub.fields[1]!.fvarId!)
  return (g, true)

/-- Substitute a value fixed by two opposite bounds before multiplying or
splitting unrelated Boolean premises. This is deterministic linear
normalization inside an emitted DP leaf: each iteration removes one value
binder, and every equality is constructed by ordered antisymmetry. -/
private partial def substOppositeBounds (g : MVarId) : MetaM MVarId := g.withContext do
  let mut bounds : List (Expr × Expr × Expr) := []
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Not 1 && ty.appArg!.isAppOfArity ``LT.lt 4 then
      let args := ty.appArg!.getAppArgs
      let p ← mkAppM ``le_of_not_gt #[mkFVar d.fvarId]
      bounds := (args[3]!, args[2]!, p) :: bounds
    else if ty.isAppOfArity ``LE.le 4 then
      let args := ty.getAppArgs
      bounds := (args[2]!, args[3]!, mkFVar d.fvarId) :: bounds
  for (a, b, hab) in bounds do
    unless a.isFVar && !(b.containsFVar a.fvarId!) do continue
    for (c, d, hba) in bounds do
      unless a == d && b == c do continue
      let p ← mkAppM ``le_antisymm #[hab, hba]
      let g ← g.assert `hOppositeBounds (← inferType p) p
      let (fv, g) ← g.intro1P
      return ← substOppositeBounds (← Lean.Meta.subst g fv)
  return g

elab "subst_dp_rational_bounds" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do return [← substOppositeBounds g]

/-- Primitive rational comparison normalization for recorded verdict leaves.
Sums and negations normalize through numberParts. Boolean comparisons
are simplified propositionally before splitting to avoid enumerating
combinations of arithmetic signs. The clause and its rational premises stay
unchanged; this is used only inside proveDpFact's existing bounded direct attempt. -/
def dpRationalViewTactic : MetaM (TSyntax `tactic) :=
  `(tactic|
    (try simp_all only [rationalpFromRat, Logic.not_nil_iff, Logic.toBool_eq_true,
      Logic.toBool_eq_false, SExpr.t, reduceCtorEq, Logic.equal_ne_nil_iff,
      logic_not_equal_nil_iff, Logic.equal_nil_iff, fromRatZero, fromRatNeZero]) <;>
    (try simp_all only [Logic.lt_parts, Logic.times_parts, Logic.plus_parts, Logic.neg_parts,
      Logic.numberParts_mkParts, Logic.numberParts_fromRat,
      Logic.numberParts_realpart, Logic.numberParts_imagpart]) <;>
    (simp_all only [show Logic.numberParts (.atom (.number (.int (Int.ofNat 0)))) = ((0 : Rat), (0 : Rat)) from (by decide),
      Prod.fst, Prod.snd, Rat.mul_zero, Rat.zero_mul, Rat.add_zero, Rat.sub_eq_add_neg, Rat.neg_zero,
      Rat.lt_irrefl, and_false, or_false]) <;>
    (simp_all only [ne_eq, Logic.not_nil_iff, Logic.toBool_eq_true,
      ite_eq_left_iff, ite_eq_right_iff, SExpr.t, reduceCtorEq,
      imp_false, not_false_eq_true, not_true_eq_false, not_not]) <;>
    subst_dp_rational_bounds <;>
    -- Substitution can make whole Boolean arms constant. Finish those
    -- before splitting, so the fallback never unfolds value matches in
    -- already contradictory or reflexive branches of the emitted leaf.
    (try simp_all only [Rat.mul_zero, Rat.zero_mul, Rat.add_zero, Rat.zero_add,
      Rat.lt_irrefl, and_false, false_and, true_and, and_true,
      or_false, not_false_eq_true, ite_true, ite_false, ite_self]) <;>
    (try split_ifs at *) <;>
    (try simp_all only [Logic.toBool, Logic.not, SExpr.t, reduceCtorEq,
      ite_true, ite_false, not_false_eq_true, fromRatNeZero]) <;>
    first | nlinarith | grind -matchEqs -splitMatch [Rat.mul_neg_iff_of_pos_left,
      Rat.mul_neg_iff_of_pos_right, Rat.mul_nonneg, Rat.mul_pos])

/-- Expose an emitted implication's premises before selecting rational
views. This is propositional normalization inside the existing DP leaf,
not an additional arithmetic rule or a rewrite-chain fallback. -/
def dpRationalPremisesTactic : MetaM (TSyntax `tactic) :=
  `(tactic|
    (try simp only [Logic.implies_ne_nil_iff, Bool.cond_eq_ite, Logic.not_nil_iff,
      Logic.toBool_eq_true, Logic.toBool_eq_false, ite_ne_left_iff,
      ite_ne_right_iff, ne_eq, not_not] at *) <;> intros)

/-- Try the rational representation on a fresh goal, assigning the original
only after all resulting obligations close. Failed normalization leaves the
ordinary DP route its original context. The caller owns the existing budget. -/
def closeDpRationalValues (g : MVarId)
    (normalize : MVarId → MetaM (List MVarId))
    (close : MVarId → MetaM (List MVarId)) : MetaM Bool := g.withContext do
  let mv ← mkFreshExprMVar (← g.getType)
  for normalized in ← normalize mv.mvarId! do
    let (view, changed) ← introDpRationalValues normalized
    unless changed || ((← g.getType).find? (fun e =>
        e.isConstOf ``Logic.realpart || e.isConstOf ``Logic.imagpart)).isSome do return false
    unless (← close view).isEmpty do return false
  g.assign (← instantiateMVars mv)
  return true

end ACL2.Replay.Driver
