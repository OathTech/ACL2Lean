import ACL2Lean.Replay.Driver.NodeCore.TypeSetWalk

namespace ACL2.Replay
open ACL2

/-- Booleanize the checked conclusion of a stored rule. -/
theorem checked_premise_conclusion {w : World} {env : Env} {c vc : SExpr}
    (pc : ∃ N, ∀ f ≥ N, evalOpt f w env c = some vc)
    (hc : EvTrue w env c) :
    cond (Logic.toBool vc) SExpr.t SExpr.nil = SExpr.t := by
  have hne := ne_nil_of_evtrue_conv hc pc
  have ht : Logic.toBool vc = true := by
    cases vc <;> simp_all [Logic.toBool]
  rw [ht]
  rfl

/-- Add one antecedent without knowing the rule's arity or conclusion head. -/
theorem checked_premise_step {w : World} {env : Env} {h vh rest : SExpr}
    (ph : ∃ N, ∀ f ≥ N, evalOpt f w env h = some vh)
    (next : EvTrue w env h → rest = SExpr.t) :
    cond (Logic.toBool vh) rest SExpr.t = SExpr.t := by
  cases hb : Logic.toBool vh with
  | false => rfl
  | true =>
    have hne : vh ≠ SExpr.nil := by
      intro hz
      subst vh
      contradiction
    have ht := next (evtrue_of_conv_ne_nil ph hne)
    exact ht

end ACL2.Replay

namespace ACL2.Replay.Driver
open ACL2 Lean Lean.Meta

/-- First-order ONE-WAY match: bind the pattern's VARIABLES (bare symbol
    atoms — ACL2 constants are quoted, functions are application heads) to
    subterms of `target`. Deterministic; fail-closed on conflicting
    bindings. Used at verdict-class premise sites where ACL2 records no
    substitution: the emitted LINEAR max-term or cited TP trigger selects
    the instance. The complete instantiated fact is transported from the
    offered theorem, with every source variable bound and kernel-checked. -/
partial def oneWayMatch (pat target : SExpr)
    (acc : List (Symbol × SExpr) := []) :
    Option (List (Symbol × SExpr)) :=
  match pat with
  | .atom (.symbol s) =>
    (match acc.find? (fun (v, _) => v == s) with
     | some (_, t) => if t == target then some acc else none
     | none => some ((s, target) :: acc))
  | .cons (.atom (.symbol f)) pargs =>
    if f.name == "QUOTE" then (if pat == target then some acc else none)
    else
      (match target with
       | .cons (.atom (.symbol g)) targs =>
         if f == g then goArgs pargs targs acc else none
       | _ => none)
  | _ => if pat == target then some acc else none
where
  goArgs (pargs targs : SExpr) (acc : List (Symbol × SExpr)) :
      Option (List (Symbol × SExpr)) :=
    match pargs, targs with
    | .nil, .nil => some acc
    | .cons p pr, .cons t tr =>
      (oneWayMatch p t acc).bind fun acc' => goArgs pr tr acc'
    | _, _ => none


def checkedPremiseTerm (hs : List SExpr) (concl : SExpr) : SExpr :=
  let ifT (h t e : SExpr) : SExpr := .cons (.atom (.symbol { name := "IF" }))
    (.cons h (.cons t (.cons e .nil)))
  hs.foldr (fun h rest => ifT h rest quoteT) (ifT concl quoteT quoteNil)

partial def mkCheckedPremise (cfg : ReplayConfig) (ctx : ReplayCtx)
    (hs : List SExpr) (concl : SExpr) (hyp : Expr) : MetaM Expr := do
  match hs with
  | [] => mkAppM ``checked_premise_conclusion #[← ctxValProof cfg ctx concl, hyp]
  | h :: hs =>
    let ph ← ctxValProof cfg ctx h
    let ty := mkAppN (mkConst ``EvTrue)
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr h]
    let tail ← withLocalDeclD `hPremise ty fun hh => do
      let pf ← mkCheckedPremise cfg ctx hs concl (mkApp hyp hh)
      mkLambdaFVars #[hh] pf
    mkAppM ``checked_premise_step #[ph, tail]

end ACL2.Replay.Driver

namespace ACL2.Replay.Driver
open ACL2 Lean Lean.Meta

/-- Re-express the stored curried rule under its recorded max-term match. -/
def instantiateLinearRule (cfg : ReplayConfig) (sb : SubstNBridge)
    (spec : LinearRuleSpec) (inst : SExpr → SExpr) (hypV : Expr) : MetaM Expr := do
  let decls := spec.hyps.zipIdx.toArray.map fun (h, i) =>
    (Name.mkSimple s!"hLinear{i}", BinderInfo.default,
      fun (_ : Array Expr) => pure (mkAppN (mkConst ``EvTrue)
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr (inst h)]))
  withLocalDecls decls fun hs => do
    let sourceHyps ← spec.hyps.zipIdx.toArray.mapM fun (h, i) => do
      mkAppM ``evtrue_of_fuel_eq
        #[← mkAppM ``fuel_eq_symm #[← sb.bridge h], hs[i]!]
    let cSource := mkAppN hypV (#[sb.env'] ++ sourceHyps)
    let cBack ← mkAppM ``evtrue_of_fuel_eq #[← sb.bridge spec.concl, cSource]
    mkLambdaFVars hs cBack

/-- The emitted max-term gates applicability. All hypotheses and the complete
conclusion are transported and checked; no rule-shape restriction substitutes
for any antecedent or proof. Nonmatches and unbound rules contribute nothing. -/
def addLinearPremises (cfg : ReplayConfig) (ctx : ReplayCtx)
    (srcOps : List SExpr) (data : List (SExpr × Expr)) :
    MetaM (List (SExpr × Expr) × ReplayCtx × List SExpr) := do
  let mut data := data
  let mut ctxL := ctx
  let mut newOps := []
  for (spec, hypV) in ctx.linearHyps do
    if let some runes := ctx.clauseRunes then
      unless runes.any (fun r => r.ty == "linear" && r.name == spec.name) do
        continue
    for op in srcOps do
      if let some σ := oneWayMatch spec.maxTerm op then
        let ruleFrees := ((spec.hyps.flatMap ACL2.Replay.freeVars) ++
          ACL2.Replay.freeVars spec.concl).eraseDups
        if ruleFrees.any (fun v => !σ.any (fun (x, _) => x == v)) then
          continue
        let σvars := σ.map (·.1)
        let σterms := σ.map (·.2)
        let inst := ACL2.Replay.substTerm σvars σterms
        let hs := spec.hyps.map inst
        let concl := inst spec.concl
        let premise := checkedPremiseTerm hs concl
        unless data.any (fun (t, _) => t == premise) do
          ctxL ← pinTermOpaques cfg cfg.envExpr ctxL premise
          let sb ← mkSubstNBridge cfg ctxL σvars σterms s!"linear {spec.name}"
          ctxL := sb.ctx
          let hypInst ← instantiateLinearRule cfg sb spec inst hypV
          let fact ← mkCheckedPremise cfg ctxL hs concl hypInst
          data := data ++ [(premise, fact)]
          newOps := (newOps ++ collectOpaques premise).eraseDups
  return (data, ctxL, newOps)

end ACL2.Replay.Driver
