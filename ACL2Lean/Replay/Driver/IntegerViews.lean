import ACL2Lean.Replay.Driver.NodeCore
import ACL2Lean.NumericExponent

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- Match the LIFTED nonneg-int TP hypothesis type
    `(bif toBool (integerp v) then not (lt v '0) else nil) = t` with `v` a
    local fvar; return it (see `dp_nonneg_int_of_tp`). -/
def nonnegIntTpFVar? (ty : Expr) : Option FVarId := do
  let some (_, lhs, rhs) := ty.eq? | none
  unless rhs.isConstOf ``SExpr.t do none
  unless lhs.isAppOfArity ``cond 4 do none
  let b := lhs.getArg! 1
  let thn := lhs.getArg! 2
  let els := lhs.getArg! 3
  unless els.isConstOf ``SExpr.nil do none
  unless b.isAppOfArity ``Logic.toBool 1 do none
  let ip := b.appArg!
  unless ip.isAppOfArity ``Logic.integerp 1 do none
  let v := ip.appArg!
  let .fvar vFv := v | none
  unless thn.isAppOfArity ``Logic.not 1 do none
  let ltE := thn.appArg!
  unless ltE.isAppOfArity ``Logic.lt 2 do none
  unless ltE.appFn!.appArg! == v do none
  unless ltE.appArg! == reflectSExpr (.atom (.number (.int 0))) do none
  return vFv

private theorem rationalp_int_value (k : Int) :
    Logic.rationalp (.atom (.number (.int k))) = SExpr.t := rfl

/-- Eliminate a value binder only when the leaf already supplies its integer
recognizer fact (directly, as a negated literal, or in the nonnegative TP).
The returned flag distinguishes plain integer facts, whose substitution can
expose further conditional TP conclusions, from the existing nonnegative
view. Each step consumes one SExpr binder; no type fact is inferred. -/
partial def introDpIntegerValues (g : MVarId) : MetaM (MVarId × Bool) := do
  let prf? ← g.withContext do
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if (nonnegIntTpFVar? d.type).isSome then
        return some ((← mkAppM ``dp_nonneg_int_of_tp #[mkFVar d.fvarId]), false)
      let mut hInt? : Option Expr := none
      if let some (_, lhs, rhs) := d.type.eq? then
        if rhs.isConstOf ``SExpr.nil && lhs.isAppOfArity ``Logic.not 1 then
          let p := lhs.appArg!
          if p.isAppOfArity ``Logic.integerp 1 && p.appArg!.isFVar then
            let hNe ← mkAppM ``logic_not_nil_ne #[p, mkFVar d.fvarId]
            hInt? := some (← mkAppM ``logic_integerp_ne_nil_t #[p.appArg!, hNe])
        else if rhs.isConstOf ``SExpr.t && lhs.isAppOfArity ``Logic.integerp 1 && lhs.appArg!.isFVar then
          hInt? := some (mkFVar d.fvarId)
      else if d.type.isAppOfArity ``Not 1 then
        if let some (_, lhs, rhs) := d.type.appArg!.eq? then
          if rhs.isConstOf ``SExpr.nil && lhs.isAppOfArity ``Logic.integerp 1 && lhs.appArg!.isFVar then
            hInt? := some (← mkAppM ``logic_integerp_ne_nil_t #[lhs.appArg!, mkFVar d.fvarId])
      if let some hi := hInt? then
        let some (_, p, _) := (← inferType hi).eq? | throwError "integer fact shape"
        return some ((← mkAppM ``logic_integerp_int #[p.appArg!, hi]), true)
    return none
  let some (prf, plain) := prf? | return (g, false)
  let ty ← g.withContext do inferType prf
  let g ← g.assert `hIntegerAtom ty prf
  let (exFv, g) ← g.intro1P
  let #[sub] ← g.cases exFv | throwError "integer existential split"
  let (g, tailPlain) ← introDpIntegerValues (← Lean.Meta.subst sub.mvarId sub.fields[1]!.fvarId!)
  return (g, plain || tailPlain)

/-- Extract existing integer witnesses, normalizing the Boolean premises
only after a new plain-integer fact is consumed. Each recurring round removes
an SExpr value binder, so there is no search or enlarged enumeration budget. -/
partial def normalizeDpIntegerViews (g : MVarId)
    (normalize : MVarId → MetaM (List MVarId)) : MetaM (List MVarId) := do
  let (g, plain) ← introDpIntegerValues g
  unless plain do return [g]
  match ← normalize g with
  | [] => return []
  | [g] => normalizeDpIntegerViews g normalize
  | _ => throwError "integer-view normalization unexpectedly split the goal"

/-- Normalize only the Boolean/recognizer premises after extracting a
new integer value. Primitive integer recognizers reduce without unfolding
recognizers at still-opaque values into constructor matches. -/
def dpIntegerViewTactic : MetaM (TSyntax `tactic) :=
  `(tactic| simp_all [-Logic.integerp, -Logic.rationalp, -Logic.toBool,
    Logic.integerp_int, rationalp_int_value, Logic.not, Logic.implies,
    Bool.cond_eq_ite, Logic.toBool_eq_true, Logic.toBool_eq_false])

end ACL2.Replay.Driver
