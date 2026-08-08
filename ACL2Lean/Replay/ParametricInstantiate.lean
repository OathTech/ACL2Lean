/-
  Replay/ParametricInstantiate — the "apply a parametric statement at a
  world" ENGINE (Phase 3 2c wiring W1, moved from Imported/Mirrors/Macro
  so the Runner-layer usefi discharge can reach it; Macro re-imports).
-/
import ACL2Lean.Replay.Runner

namespace ACL2.Imported.Mirrors

open ACL2 ACL2.Replay ACL2.Replay.Driver Lean Lean.Meta Lean.Elab

/-- The instantiation walk: peel the premise telescope, discharging each
    binder via `dischargeOne` (`.none` = KEEP as an explicit hypothesis —
    the D6 discipline for frontier-blocked rule:/use: premises). Returns
    the proof λ-abstracted over the KEPT hypotheses (innermost-scope
    lambda), the kept binder names, and the conclusion type. -/
partial def ipGo (dischargeOne : String → Expr → MetaM (Option Expr))
    (ty acc : Expr) (kept : Array Expr) (keptNames : List String) :
    MetaM (Expr × List String × Expr) := do
  if ty.isForall then
    let bName := ty.bindingName!.toString (escape := false)
    match ← dischargeOne bName ty.bindingDomain! with
    | some pf =>
      ipGo dischargeOne (ty.bindingBody!.instantiate1 pf) (mkApp acc pf)
        kept keptNames
    | none =>
      Meta.withLocalDeclD ty.bindingName! ty.bindingDomain! fun h =>
        ipGo dischargeOne (ty.bindingBody!.instantiate1 h) (mkApp acc h)
          (kept.push h) (keptNames ++ [bName])
  else
    return (← Meta.mkLambdaFVars kept acc, keptNames, ty)

/-- The REUSABLE instantiation core (Phase 3 2c wiring): apply a
    parametric proof at an arbitrary WORLD (value + reflected Expr) and
    discharge its premise telescope with the existing provers — the
    engine behind both `instantiate_parametric%` (the canonical world)
    and the usefi: alias-world discharge. `totsNames`: registered
    world-parametric discharger constants (the dis_* family). Returns
    (proof λ-abstracted over KEPT premises, kept names, conclusion). -/
def instantiateParametricAt (dev : Development) (worldVal : World)
    (worldExpr : Expr) (nm : String)
    (crossTrees : List (String × ClauseProof))
    (crossRules : List ACL2.RuleSpec)
    (totsNames : List Name)
    (constE : Expr) (envV : Expr)
    (extraJusts : List (String × ACL2.Justification) := []) :
    MetaM (Expr × List String × Expr) := do
  let ch := ACL2.Replay.Runner.bookChannels dev crossTrees crossRules
  let cfg := ACL2.Replay.Runner.mkBookConfig dev worldVal worldExpr envV
  let rules := ACL2.Replay.Runner.combineRules
    (Driver.rulesBefore dev nm) ch.crossRules
  let ctx : ReplayCtx := {}
  let dischargeBudget : Nat := 3000000
  let totalEnv ← withRealMaxHeartbeats dischargeBudget <|
    buildTotalEnv cfg (dev.justifications ++ extraJusts) (tpCors := ch.tps)
  let tryRegistered := fun (bTy : Expr) => do
    let mut viaReg : Option Expr := none
    for dName in totsNames do
      if viaReg.isNone then
        try
          let mut cand := mkApp (mkConst dName) worldExpr
          let mut n := 0
          while n < 24 && !(← isDefEq (← inferType cand) bTy) do
            let cTy ← Meta.whnf (← inferType cand)
            unless cTy.isForall do break
            cand := mkApp cand
              (← proveByDecide cTy.bindingDomain!
                s!"discharger pin ({dName})")
            n := n + 1
          if ← isDefEq (← inferType cand) bTy then
            viaReg := some cand
        catch _ => pure ()
    pure viaReg
  let ty0 ← inferType constE
  let ty ← Meta.instantiateForall ty0 #[envV, worldExpr]
  let acc := mkApp2 constE envV worldExpr
  let dischargeOne := fun (bName : String) (bTy : Expr) =>
      (do
    let key := fun (pre : String) => (bName.drop pre.length).toString
    let arg? ← withRealMaxHeartbeats dischargeBudget <| do
      if bName.startsWith "hnoshadow_" then
        some <$> proveNoShadow cfg { name := key "hnoshadow_" }
      else if bName.startsWith "htotal_" then
        match totalEnv.find? (fun (n, _, _) => n == key "htotal_") with
        | some (_, _, pf) => pure (some pf)
        | none =>
          match ← tryRegistered bTy with
          | some pf => pure (some pf)
          | none => throwError "instantiate_parametric%: no totality \
              proof for {key "htotal_"} (buildTotalEnv miss; no listed \
              `totals` discharger matched)"
      else if bName.startsWith "htp_" then
        let fn := key "htp_"
        match ch.tps.lookup fn with
        | some cor =>
          try some <$> proveTp cfg totalEnv dev.justifications fn cor
          catch e =>
            match ← tryRegistered bTy with
            | some pf => pure (some pf)
            | none => throw e
        | none => throwError "instantiate_parametric%: no emitted TP \
            corollary for {fn}"
      else if bName.startsWith "hrule_" then
        -- strip the positional disambiguation suffix (_NN) if present
        let raw := key "hrule_"
        let base := match (raw.splitOn "_") with
          | parts@(_ :: _ :: _) =>
            if (parts.getLast!).all Char.isDigit then
              String.intercalate "_" (parts.dropLast) else raw
          | _ => raw
        let cands := rules.filter (·.name == base)
        if cands.isEmpty then
          throwError "instantiate_parametric%: no stored rule named \
            {base} in scope"
        let mut found : Option (Option Expr) := none
        for spec in cands do
          if found.isNone then
            if ← isDefEq (← mkRuleHypType cfg spec) bTy then
              found := some (← (some <$> dischargeRuleHyp cfg ctx spec
                  ch.depProofs []) <|> pure none)
        match found with
        | some pf? => pure pf?
        | none => throwError "instantiate_parametric%: no stored rule \
            named {base} matches binder {bName}'s type (offer drift)"
      else if bName.startsWith "husethm_" then
        let n := key "husethm_"
        match (ch.depProofs.lookup n).bind (·.root) with
        | some root =>
          match root.inputClause with
          | [f] =>
            let spec : UseSpec := { name := n, formula := f }
            unless ← isDefEq (← mkUseHypType cfg spec) bTy do
              throwError "instantiate_parametric%: use:{n} type mismatch"
            (some <$> dischargeUseHyp cfg ctx spec ch.depProofs [])
              <|> pure none
          | _ => throwError "instantiate_parametric%: use:{n} dep Goal \
              is not single-literal"
        | none => throwError "instantiate_parametric%: no dependency \
            tree for use:{n}"
      else
        throwError "instantiate_parametric%: unrecognized premise \
          binder {bName} (class outside the instantiation's provers — \
          investigate or defer, never skip)"
    -- a produced proof must inhabit the binder type exactly
    if let some arg := arg? then
      unless ← isDefEq (← inferType arg) bTy do
        throwError "instantiate_parametric%: discharge for {bName} does \
          not inhabit the binder type"
    pure arg? : MetaM (Option Expr))
  ipGo dischargeOne ty acc #[] []


/-- Reflect a functional substitution to an `Expr` (`List (Symbol ×
    List Symbol × SExpr)`). -/
def reflectSubst (σ : List (Symbol × List Symbol × SExpr)) :
    MetaM Expr := do
  let symTy := mkConst ``ACL2.Symbol
  let entryTy ← Lean.Meta.mkAppM ``Prod
    #[symTy, ← Lean.Meta.mkAppM ``Prod
      #[← Lean.Meta.mkAppM ``List #[symTy], mkConst ``ACL2.SExpr]]
  Lean.Meta.mkListLit entryTy (← σ.mapM fun (fn, formals, body) => do
    Lean.Meta.mkAppM ``Prod.mk
      #[ACL2.Replay.Driver.reflectSymbol fn,
        ← Lean.Meta.mkAppM ``Prod.mk
          #[← Lean.Meta.mkListLit symTy
              (formals.map ACL2.Replay.Driver.reflectSymbol),
            ACL2.Replay.Driver.reflectSExpr body]])

/-- The usefi: discharge composition (R7b 2c W4b): prove the
    functional-instance hypothesis `∀ env', EvTrue w env' ⟦instance⟧`
    by (1) rebuilding the cited theorem's PARAMETRIC statement from its
    dep dev, (2) discharging its premises at the ALIAS world
    `w.withAliases σ` through the shared instantiation engine, and
    (3) crossing to the consumer world by `evtrue_fnalias` (every side
    condition decided on the concrete data or supplied constructively
    by the `withAliases` lemmas).  Premises the engine cannot yet
    discharge at the alias world FRONTIER (the hypothesis stays kept —
    D6); the bridging extensions close them incrementally. -/
def mkUseFiDischarger (crossDevs : List (String × Development))
    (totsNames : List Name := []) :
    ReplayConfig → UseFiSpec → MetaM Expr := fun cfg spec => do
  let some (_, depDev) := crossDevs.find? (fun (_, d) =>
      (Driver.findThm d spec.name).isSome)
    | Driver.throwFrontier m!"usefi discharge: no dep dev carries \
        {spec.name} (crossDevs surface)"
  let some cp := Driver.findThm depDev spec.name
    | Driver.throwFrontier m!"usefi discharge: {spec.name} vanished"
  let σ := spec.subst
  let names := σ.map (·.1)
  let wAliasVal := ACL2.Replay.World.withAliases cfg.worldVal σ
  let σE ← reflectSubst σ
  let wAliasE ← Lean.Meta.mkAppM ``ACL2.Replay.World.withAliases
    #[cfg.worldExpr, σE]
  -- the dep's own offer channels: every OTHER crossDev's trees/rules
  let depCross := crossDevs.filter (fun (_, d) =>
    (Driver.findThm d spec.name).isNone)
  let depCrossTrees := depCross.flatMap
    (fun (_, d) => ACL2.Replay.Runner.bookTrees d)
  let depCrossRules := depCross.foldl (init := [])
    (fun acc (_, d) => acc ++ (ACL2.Replay.Runner.allBookRules d).filter
      (fun r => !acc.any (fun o => o.runeKey == r.runeKey)))
  let scopes ← match depDev.scopes with
    | .ok ss => pure ss
    | .error e => throwError "usefi discharge: {e}"
  let sigFns := ((scopes.flatMap (fun sc =>
    sc.sigs ++ sc.witnesses.map (fun (n, _, _) => ({ name := n } : Symbol)))
    ).eraseDups)
  Lean.Meta.withLocalDeclD `envq (mkConst ``ACL2.Env) fun envV => do
    -- (1) the dep theorem's parametric statement (env free := envV)
    let cfgDep := ACL2.Replay.Runner.mkBookConfig depDev depDev.toWorld
      (mkConst ``ACL2.World) envV
    let ch := ACL2.Replay.Runner.bookChannels depDev depCrossTrees
      depCrossRules
    let (pfParam, _pconds) ← Driver.replayProofParametric cfgDep sigFns
      ch.tps cp depDev.justifications
      (ACL2.Replay.Runner.combineRules
        (Driver.rulesBefore depDev spec.name) ch.crossRules)
      ch.depProofs (equivRefls := ch.equivRefls)
      (congTrees := some ch.localTrees)
    -- (2) premises at the alias world via the shared engine
    let pfParamEnv ← Lean.Meta.mkLambdaFVars #[envV] pfParam
    let (pfAtAlias, kept, _concl) ← instantiateParametricAt depDev
      wAliasVal wAliasE spec.name depCrossTrees depCrossRules totsNames
      pfParamEnv envV (extraJusts := cfg.justs)
    unless kept.isEmpty do
      Driver.throwFrontier m!"usefi discharge: premises KEPT at the \
        alias world (bridging pending): [{", ".intercalate kept}]"
    -- (3) cross to the consumer world
    let some root := cp.root
      | Driver.throwFrontier m!"usefi discharge: {spec.name} has no tree"
    let [phi] := root.inputClause
      | Driver.throwFrontier m!"usefi discharge: {spec.name}'s Goal is \
          not single-literal"
    let phiE := Driver.reflectSExpr phi
    let namesE ← mkListLit (mkConst ``ACL2.Symbol)
      (names.map Driver.reflectSymbol)
    let entryTy := (← inferType σE).appArg!
    -- ∀-mem side conditions, decided on the concrete σ
    let mkMemAll (prop : Expr → MetaM Expr) : MetaM Expr := do
      withLocalDeclD `e entryTy fun eV => do
        let body ← prop eV
        let mem ← mkAppM ``Membership.mem #[σE, eV]
        mkForallFVars #[eV] (← mkArrow mem body)
    let hσdefTy ← mkMemAll fun eV => do
      let fst ← mkAppM ``Prod.fst #[eV]
      let sndFst ← mkAppM ``Prod.fst #[← mkAppM ``Prod.snd #[eV]]
      let sndSnd ← mkAppM ``Prod.snd #[← mkAppM ``Prod.snd #[eV]]
      mkEq (← mkAppM ``ACL2.DefMap.get?
          #[← mkAppM ``ACL2.World.defs #[wAliasE], fst])
        (← mkAppM ``Option.some
          #[← mkAppM ``Prod.mk #[sndFst, sndSnd]])
    let nodupTy ← mkAppM ``List.Nodup
      #[← mkAppM ``List.map
        #[← withLocalDeclD `e entryTy fun eV => do
            mkLambdaFVars #[eV] (← mkAppM ``Prod.fst #[eV]), σE]]
    let nodupPf ← Driver.proveByDecide nodupTy "usefi nodup"
    let hσdef ← do
      let pf ← mkAppM ``ACL2.Replay.withAliases_get
        #[cfg.worldExpr, σE, nodupPf]
      unless ← isDefEq (← inferType pf) hσdefTy do
        Driver.throwFrontier m!"usefi discharge: withAliases_get shape \
          mismatch"
      pure pf
    let hagree ← mkAppM ``ACL2.Replay.withAliases_agree
      #[cfg.worldExpr, σE]
    let mkBoolMem (mk : Expr → MetaM Expr) : MetaM Expr := do
      let ty ← mkMemAll mk
      Driver.proveByDecide ty "usefi σ side condition"
    let hσns ← mkBoolMem fun eV => do
      let fst ← mkAppM ``Prod.fst #[eV]
      let isN := fun (n : String) =>
        mkAppM ``ACL2.Symbol.isNamed #[fst, Lean.mkStrLit n]
      let ors ← [
        ← isN "QUOTE", ← isN "IF", ← isN "LET", ← isN "LET*",
        ← isN "LAMBDA"].foldlM
        (fun acc e => match acc with
          | none => pure (some e)
          | some a => some <$> mkAppM ``HOr.hOr #[a, e]) none
      mkEq ors.get! (mkConst ``Bool.false)
    let hσws ← mkBoolMem fun eV => do
      let sndSnd ← mkAppM ``Prod.snd #[← mkAppM ``Prod.snd #[eV]]
      mkEq (← mkAppM ``ACL2.Replay.WellScoped #[sndSnd])
        (mkConst ``Bool.true)
    let hσcl ← mkBoolMem fun eV => do
      let sndFst ← mkAppM ``Prod.fst #[← mkAppM ``Prod.snd #[eV]]
      let sndSnd ← mkAppM ``Prod.snd #[← mkAppM ``Prod.snd #[eV]]
      let fvs ← mkAppM ``ACL2.Replay.freeVars #[sndSnd]
      let inner ← withLocalDeclD `x (mkConst ``ACL2.Symbol) fun xV => do
        mkLambdaFVars #[xV] (← mkAppM ``List.contains #[sndFst, xV])
      mkEq (← mkAppM ``List.all #[fvs, inner]) (mkConst ``Bool.true)
    let hw ← Driver.proveByDecide
      (← mkEq (← mkAppM ``ACL2.Replay.aliasFreeWorld
        #[namesE, cfg.worldExpr]) (mkConst ``Bool.true))
      "usefi aliasFreeWorld"
    let hws ← Driver.proveByDecide
      (← mkEq (← mkAppM ``ACL2.Replay.WellScoped #[phiE])
        (mkConst ``Bool.true)) "usefi WellScoped Φ"
    let hsimp ← Driver.proveByDecide
      (← mkEq (← mkAppM ``ACL2.Replay.aliasArgsSimple #[namesE, phiE])
        (mkConst ``Bool.true)) "usefi aliasArgsSimple Φ"
    let hfree ← Driver.proveByDecide
      (← mkEq (← mkAppM ``ACL2.Replay.fnFreeTerm
        #[namesE, ← mkAppM ``ACL2.Replay.substFnCalls #[σE, phiE]])
        (mkConst ``Bool.true)) "usefi fnFree image"
    let pfCross ← mkAppM ``ACL2.Replay.evtrue_fnalias
      #[σE, cfg.worldExpr, wAliasE, hσdef, hσns, hσws, hσcl, hagree,
        hw, phiE, hws, hsimp, hfree, envV, pfAtAlias]
    let target := mkAppN (mkConst ``ACL2.Replay.EvTrue)
      #[cfg.worldExpr, envV, Driver.reflectSExpr spec.formula]
    unless ← isDefEq (← inferType pfCross) target do
      Driver.throwFrontier m!"usefi discharge: crossed conclusion does \
        not match the emitted instance (substFnCalls image drift)"
    mkForallFVars #[envV] (← Lean.Meta.mkExpectedTypeHint pfCross target)

end ACL2.Imported.Mirrors
