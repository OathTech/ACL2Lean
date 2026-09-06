import ACL2Lean.Replay.Driver.LinearPremises

namespace ACL2.Replay.Driver
open ACL2 Lean Lean.Meta

/-- Instantiate only a leaf-cited stored type prescription whose complete
corollary is an instance of an offered theorem's source formula. The
trigger is ACL2's stored TERM. The resulting value fact is Booleanized from
the checked whole-formula proof, preserving every conditional hypothesis.
No uncited rule or unresolved variable contributes a premise. -/
def addCitedTypePremises (cfg : ReplayConfig) (ctx : ReplayCtx)
    (srcOps : List SExpr) (data : List (SExpr × Expr)) :
    MetaM (List (SExpr × Expr) × ReplayCtx × List SExpr) := do
  let some cited := ctx.clauseRunes | return (data, ctx, [])
  let mut data := data
  let mut ctxT := ctx
  let mut newOps := []
  for (_, rules) in cfg.tpAllTps do
    for rule in rules do
      unless cited.any (fun r => r.ty == "type-prescription" &&
          r.name == rule.rune.name && r.idx == rule.rune.idx) do continue
      for (spec, proof) in ctx.tpThmHyps do
        unless spec.name == rule.rune.name do continue
        let some formulaSubst := oneWayMatch spec.formula rule.corollary | continue
        let sourceVars := formulaSubst.map (·.1)
        unless (ACL2.Replay.freeVars spec.formula).all (sourceVars.contains ·) do continue
        unless ACL2.Replay.substTerm sourceVars (formulaSubst.map (·.2)) spec.formula ==
            rule.corollary do
          throwError "type-prescription {spec.name}: formula substitution did not recompute"
        for op in srcOps do
          let some σ := oneWayMatch rule.term op | continue
          let inst := ACL2.Replay.substTerm (σ.map (·.1)) (σ.map (·.2))
          unless (ACL2.Replay.freeVars rule.corollary).all
              (fun v => (σ.map (·.1)).contains v) do continue
          let formula := inst rule.corollary
          let args := formulaSubst.map (fun (_, t) => inst t)
          unless ACL2.Replay.substTerm sourceVars args spec.formula == formula do
            throwError "type-prescription {spec.name}: composed substitution did not recompute"
          let premise := checkedPremiseTerm [] formula
          unless data.any (fun (t, _) => t == premise) do
            let (hInst, ctx') ← instantiateEvTrueHypAt cfg ctxT proof sourceVars args spec.formula
            ctxT ← pinTermOpaques cfg cfg.envExpr ctx' premise
            let fact ← mkCheckedPremise cfg ctxT [] formula hInst
            data := data ++ [(premise, fact)]
            newOps := (newOps ++ collectOpaques premise).eraseDups
  return (data, ctxT, newOps)

end ACL2.Replay.Driver
