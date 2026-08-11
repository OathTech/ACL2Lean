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

/-- WORLD-SCALE kernel decision: check the `Decidable` proposition by
    COMPILED evaluation (fast, no deep symbolic reduction on the
    elaborator's stack — the W4c overflow), then emit `mkDecideProof`,
    verified by the kernel's own reducer at declaration. -/
def proveByDecideKernel (p : Expr) (what : String) : MetaM Expr := do
  let b ← unsafe Lean.Meta.evalExpr Bool (mkConst ``Bool)
    (← Lean.Meta.mkDecide p)
  unless b do
    throwError "proveByDecideKernel: {what} evaluated FALSE"
  Lean.Meta.mkDecideProof p

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
    (extraJusts : List (String × ACL2.Justification) := [])
    (innerTotalFallback : Symbol → Expr → MetaM (Option Expr) :=
      fun _ _ => pure none)
    (ruleBridge : ACL2.RuleSpec → Expr → MetaM (Option Expr) :=
      fun _ _ => pure none)
    (useBridge : UseSpec → Expr → MetaM (Option Expr) :=
      fun _ _ => pure none)
    (crossDevs : List (String × Development) := []) :
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
  -- INNER-DISCHARGE tp augmentation (close-out item 1b): the rule/use
  -- premises' re-replays consume ctx.tpHyps — witness-fn TP facts the
  -- pool cannot prove get PROOF-TERM entries from the registered
  -- dischargers (the dis_* family via the same generic peel), so the
  -- inner replays close instead of keeping witness conds
  let ch2 := ACL2.Replay.Runner.bookChannels dev crossTrees crossRules
  let mut tpAug : List (String × SExpr × Expr) := []
  for (fn, cor) in ch2.tps do
    match worldVal.defs.get? { name := fn } with
    | some (formals, _) =>
      let tpTy ← try Driver.mkTpHypType cfg { name := fn } formals cor
        catch _ => pure (mkConst ``True)
      if !tpTy.isConst then
        match ← (some <$> withRealMaxHeartbeats 3000000
            (proveTp cfg totalEnv (dev.justifications ++ extraJusts)
              fn cor)) <|> pure none with
        | some pf => tpAug := tpAug ++ [(fn, cor, pf)]
        | none =>
          match ← tryRegistered tpTy with
          | some pf => tpAug := tpAug ++ [(fn, cor, pf)]
          | none => pure ()
    | none => pure ()
  -- likewise totality: the pool's proofs (and any registered-discharger
  -- successes) become proof-term entries the inner replays can consume
  let mut totAug : List (String × Expr) := []
  for (n, _, pf) in totalEnv do
    totAug := totAug ++ [(n, pf)]
  for (sy, formals, _) in worldVal.defs.entries do
    unless totAug.any (·.1 == sy.name) do
      let totTy ← try Driver.mkTotalityHypType cfg sy formals.length
        catch _ => pure (mkConst ``True)
      if !totTy.isConst then
        match ← tryRegistered totTy with
        | some pf => totAug := totAug ++ [(sy.name, pf)]
        | none => pure ()
  -- DEMAND-DRIVEN rule pre-discharge (close-out 1b): the inner
  -- re-replays cite gz rules (D5 prelude constants) and earlier
  -- theorem rules — pre-discharge the DEMANDED set (citations of the
  -- dep trees the telescope will re-replay) into proof-term entries,
  -- iterating for citation chains; failures skip (the affected
  -- premise then keeps, honest)
  -- equivrefl entries (the type-alist's R-reflexivity evidence, e.g.
  -- (PERM x x)): each equivalence-shaped theorem in scope offers its
  -- reflexivity component, discharged from its dependency tree
  let ctxRef ← IO.mkRef { ctx with
    tpHyps := ctx.tpHyps ++ tpAug,
    totalHyps := ctx.totalHyps ++ totAug }
  let demand := (ch.depProofs.foldl (init := ([] : List String))
    fun acc (_, cp) => acc ++ ACL2.Replay.Runner.citedRuneNames cp).eraseDups
  let demandRules := rules.filter (fun r => demand.contains r.name)
  let equivOffers := ch.equivRefls.filterMap
    (fun (n, f) => Driver.equivReflSpecOfFormula? n f)
  for _round in [0, 1, 2] do
    for spec in demandRules do
      let cur ← ctxRef.get
      unless cur.ruleHyps.any (fun (r, _) => r.runeKey == spec.runeKey) do
        let pf? ←
          match Driver.d5GzRules.lookup spec.name with
          | some (decl, nsFn) =>
            (some <$> Driver.dischargeGzRuleHyp cfg spec decl nsFn)
              <|> pure none
          | none =>
            (some <$> withRealMaxHeartbeats 3000000
              (dischargeRuleHyp cfg cur spec ch.depProofs []))
              <|> pure none
        if let some pf := pf? then
          ctxRef.modify fun c =>
            { c with ruleHyps := c.ruleHyps ++ [(spec, pf)] }
    -- equivrefl entries (the type-alist's R-reflexivity evidence, e.g.
    -- (PERM x x)) join the same rounds: their dep trees cite theorem
    -- rules (PERM-SYMMETRIC) and the use-theorem re-replays need them
    for spec in equivOffers do
      let cur ← ctxRef.get
      unless cur.equivReflHyps.any (fun (sp, _) => sp.name == spec.name) do
        let er? ← try
            some <$> withRealMaxHeartbeats 3000000
              (Driver.dischargeEquivReflHyp cfg cur spec ch.depProofs [])
          catch _ => pure none
        if let some pf := er? then
          ctxRef.modify fun c =>
            { c with equivReflHyps := c.equivReflHyps ++ [(spec, pf)] }
  -- ERROR DISCIPLINE NOTE (close-out audit m2, deliberate): the
  -- discharge ATTEMPTS in this function (the pre-discharge rounds, the
  -- hrule_/husethm_ dispatches, the prepare-time closures) swallow
  -- failures broadly rather than filtering by isFrontierErr, because
  -- attempts may legitimately fail on COST grounds (heartbeat/rec-depth
  -- runtime bounds) for premises that then stay honestly KEPT — a
  -- failure here can only widen the declared constant's hypothesis
  -- list, never produce a wrong proof. The trade-off (a real discharger
  -- defect degrades to a KEPT premise instead of surfacing) is accepted
  -- for this offer-attempt layer; the Harness discharge sites keep the
  -- strict N1 typed-tag discipline.
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
          | none =>
            -- ALIAS-WRAPPER route (W4d): `(fn x) := (g x)` is total
            -- because g is — wrapper_total_1 over g's pool proof
            let fnSym : Symbol := { name := key "htotal_" }
            match worldVal.defs.get? fnSym with
            | some ([x], .cons (.atom (.symbol g))
                (.cons (.atom (.symbol x')) .nil)) =>
              if x' == x then
                match totalEnv.find? (fun (n, _, _) => n == g.name) with
                | some (_, _, hgPf) => do
                  let body : SExpr := .cons (.atom (.symbol g))
                    (.cons (.atom (.symbol x)) .nil)
                  let hdefTy ← mkEq
                    (← mkAppM ``ACL2.DefMap.get?
                      #[← mkAppM ``ACL2.World.defs #[worldExpr],
                        Driver.reflectSymbol fnSym])
                    (← mkAppM ``Option.some #[← mkAppM ``Prod.mk
                      #[← mkListLit (mkConst ``ACL2.Symbol)
                          [Driver.reflectSymbol x],
                        Driver.reflectSExpr body]])
                  let hdef ← proveByDecideKernel hdefTy
                    s!"wrapper hdef {fnSym.name}"
                  let isN := fun (n : String) =>
                    mkAppM ``ACL2.Symbol.isNamed
                      #[Driver.reflectSymbol fnSym, Lean.mkStrLit n]
                  let hq ← Driver.proveByDecide
                    (← mkEq (← isN "QUOTE") (mkConst ``Bool.false))
                    s!"wrapper hq {fnSym.name}"
                  let hif ← Driver.proveByDecide
                    (← mkEq (← isN "IF") (mkConst ``Bool.false))
                    s!"wrapper hif {fnSym.name}"
                  let hlet ← Driver.proveByDecide
                    (← mkEq (← mkAppM ``Bool.or
                      #[← isN "LET", ← isN "LET*"])
                      (mkConst ``Bool.false))
                    s!"wrapper hlet {fnSym.name}"
                  let pf ← mkAppM ``ACL2.Replay.wrapper_total_1
                    #[worldExpr, Driver.reflectSymbol fnSym,
                      Driver.reflectSymbol g, Driver.reflectSymbol x,
                      hdef, hq, hif, hlet, hgPf]
                  pure (some pf)
                | none =>
                  -- consumer-telescope route (W4e): transport the
                  -- CONSUMER's own total:g hypothesis into this world
                  let gHypTy ← Driver.mkTotalityHypType
                    { worldExpr := worldExpr, envExpr := envV,
                      worldVal := worldVal } g 1
                  match ← innerTotalFallback g gHypTy with
                  | some hgPf => do
                    let body : SExpr := .cons (.atom (.symbol g))
                      (.cons (.atom (.symbol x)) .nil)
                    let hdefTy ← mkEq
                      (← mkAppM ``ACL2.DefMap.get?
                        #[← mkAppM ``ACL2.World.defs #[worldExpr],
                          Driver.reflectSymbol fnSym])
                      (← mkAppM ``Option.some #[← mkAppM ``Prod.mk
                        #[← mkListLit (mkConst ``ACL2.Symbol)
                            [Driver.reflectSymbol x],
                          Driver.reflectSExpr body]])
                    let hdef ← proveByDecideKernel hdefTy
                      s!"wrapper hdef {fnSym.name}"
                    let isN := fun (n : String) =>
                      mkAppM ``ACL2.Symbol.isNamed
                        #[Driver.reflectSymbol fnSym, Lean.mkStrLit n]
                    let hq ← Driver.proveByDecide
                      (← mkEq (← isN "QUOTE") (mkConst ``Bool.false))
                      s!"wrapper hq {fnSym.name}"
                    let hif ← Driver.proveByDecide
                      (← mkEq (← isN "IF") (mkConst ``Bool.false))
                      s!"wrapper hif {fnSym.name}"
                    let hlet ← Driver.proveByDecide
                      (← mkEq (← mkAppM ``Bool.or
                        #[← isN "LET", ← isN "LET*"])
                        (mkConst ``Bool.false))
                      s!"wrapper hlet {fnSym.name}"
                    let pf ← mkAppM ``ACL2.Replay.wrapper_total_1
                      #[worldExpr, Driver.reflectSymbol fnSym,
                        Driver.reflectSymbol g, Driver.reflectSymbol x,
                        hdef, hq, hif, hlet, hgPf]
                    pure (some pf)
                  | none => throwError "instantiate_parametric%: wrapper \
                      {key "htotal_"}'s inner fn {g.name} has no pool \
                      totality and no fallback"
              else throwError "instantiate_parametric%: {key "htotal_"} \
                  is not a same-formal wrapper"
            | _ => throwError "instantiate_parametric%: no totality \
                proof for {key "htotal_"} (buildTotalEnv miss; no \
                listed `totals` discharger matched; not a unary alias \
                wrapper)"
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
        let mut found : Option (Option Expr × ACL2.RuleSpec) := none
        for spec in cands do
          if found.isNone then
            if ← isDefEq (← mkRuleHypType cfg spec) bTy then
              found := some (← try
                  let pf ← dischargeRuleHyp cfg (← ctxRef.get) spec
                    ch.depProofs []
                  -- feed forward: later constraint rules cite earlier
                  -- ones (ORDEREDP-SORTFN2 cites ORDEREDP-SORTFN1)
                  ctxRef.modify fun c =>
                    { c with ruleHyps := c.ruleHyps ++ [(spec, pf)] }
                  pure (some pf)
                catch _ => pure none, spec)
        match found with
        | some (some pf, _) => pure (some pf)
        | some (none, spec) =>
          -- W4f: the consumer-side bridge (alias-free fvar crossing /
          -- substituted-rule discharge + lift)
          ruleBridge spec bTy
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
            let usePf? ← try
                some <$> dischargeUseHyp cfg (← ctxRef.get) spec
                  ch.depProofs []
              catch _ =>
                -- retry under the OWNING book's cfg at the consumer
                -- world (the usefi-bridge pattern): the dependency's
                -- justification/gz channels are what its tree's DP
                -- leaves consume
                match crossDevs.find? (fun (_, d) =>
                    (Driver.findThm d n).isSome) with
                | some (_, ownDev) =>
                  let ownCfg := ACL2.Replay.Runner.mkBookConfig ownDev
                    worldVal worldExpr envV
                  try
                    some <$> dischargeUseHyp ownCfg (← ctxRef.get) spec
                      ch.depProofs []
                  catch _ => pure none
                | none => pure none
            match usePf? with
            | some pf => pure (some pf)
            | none => useBridge spec bTy
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
    (totsNames : List Name := [])
    (termByFn : List (String × Lean.Name × List String × List SExpr)
      := []) :
    Development → ReplayConfig → ReplayCtx → UseFiSpec → MetaM Expr :=
    fun consumerDev cfg ctx spec => do
  let _ := consumerDev  -- consumed by the W4f bridging (next increment)
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
    -- DEMAND-FILTER the rebuild's rule offers to the tree's cited
    -- runes (the replayAdmission precedent): the full corpus
    -- accumulation is thousands of offers, and withLocalDecls spends
    -- one native stack frame PER BINDER — stacked on the consuming
    -- row's own telescope frames this overflowed the lake worker
    -- thread (the in-sweep SIGABRT; the CLI's larger main-thread
    -- stack is why the isolation probe survived).
    let cited := ACL2.Replay.Runner.citedRuneNames cp
    let rebuildRules := (ACL2.Replay.Runner.combineRules
      (Driver.rulesBefore depDev spec.name) ch.crossRules).filter
      (fun r => cited.contains r.name)
    let (pfParam, _pconds) ← Driver.replayProofParametric cfgDep sigFns
      ch.tps cp depDev.justifications rebuildRules
      ch.depProofs (equivRefls := ch.equivRefls)
      (congTrees := some ch.localTrees)
    -- (2) premises at the alias world via the shared engine
    let pfParamEnv ← Lean.Meta.mkLambdaFVars #[envV] pfParam
    let namesE ← mkListLit (mkConst ``ACL2.Symbol)
      (names.map Driver.reflectSymbol)
    let hagree ← mkAppM ``ACL2.Replay.withAliases_agree
      #[cfg.worldExpr, σE]
    -- the ONE world-scale fact: declared ONCE per (world, names) and
    -- referenced — an inline decide term makes tryReplay's Meta.check
    -- whnf the whole 200+-defun traversal on the elaborator stack (the
    -- W4f SIGABRT); as a constant the kernel checks it once at addDecl
    let hwProp ← mkEq (← mkAppM ``ACL2.Replay.aliasFreeWorld
      #[namesE, cfg.worldExpr]) (mkConst ``Bool.true)
    let hwKey := (cfg.worldExpr.constName?.map (·.toString)).getD "anon"
      ++ "_" ++ String.intercalate "_" (names.map (·.name))
    let hwName := Lean.Name.mkStr2 "UsefiAliasFree"
      (String.map (fun c => if c.isAlphanum then c else '_') hwKey)
    let hw ← do
      if (← Lean.getEnv).contains hwName then
        pure (mkConst hwName)
      else do
        let b ← unsafe Lean.Meta.evalExpr Bool (mkConst ``Bool)
          (← Lean.Meta.mkDecide hwProp)
        unless b do
          throwError "usefi: aliasFreeWorld evaluated FALSE"
        Lean.Meta.check hwProp
        Lean.addDecl <| .thmDecl
          { name := hwName, levelParams := [], type := hwProp,
            value := ← Lean.Meta.mkDecideProof hwProp }
        pure (mkConst hwName)
    -- hoisted σ-side conditions (shared by the crossing tail and the
    -- Class-2 rule lifts)
    let entryTy := (← inferType σE).appArg!
    let mkMemAll := fun (prop : Expr → MetaM Expr) => do
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
    let nodupPf ← proveByDecideKernel nodupTy "usefi nodup"
    let hσdef ← do
      let pf ← mkAppM ``ACL2.Replay.withAliases_get
        #[cfg.worldExpr, σE, nodupPf]
      unless ← isDefEq (← inferType pf) hσdefTy do
        Driver.throwFrontier m!"usefi discharge: withAliases_get shape \
          mismatch"
      pure pf
    let mkBoolMem := fun (mk : Expr → MetaM Expr) => do
      let ty ← mkMemAll mk
      proveByDecideKernel ty "usefi σ side condition"
    let hσns ← mkBoolMem fun eV => do
      let fst ← mkAppM ``Prod.fst #[eV]
      let isN := fun (n : String) =>
        mkAppM ``ACL2.Symbol.isNamed #[fst, Lean.mkStrLit n]
      let ors ← [
        ← isN "QUOTE", ← isN "IF", ← isN "LET", ← isN "LET*",
        ← isN "LAMBDA"].foldlM
        (fun acc e => match acc with
          | none => pure (some e)
          | some a => some <$> mkAppM ``Bool.or #[a, e]) none
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
    -- W4e: transport a CONSUMER-telescope totality hypothesis into the
    -- alias world for a wrapper's inner fn the pool cannot prove
    let innerTotalFallback := fun (g : Symbol) (wantTy : Expr) => do
      match ctx.totalHyps.find? (fun (n, _) => n == g.name) with
      | none => pure (Option.none (α := Expr))
      | some (_, hFv) =>
        match cfg.worldVal.defs.get? g with
        | some ([x], body) => do
          let isN := fun (n : String) =>
            mkAppM ``ACL2.Symbol.isNamed
              #[Driver.reflectSymbol g, Lean.mkStrLit n]
          let hq ← Driver.proveByDecide
            (← mkEq (← isN "QUOTE") (mkConst ``Bool.false))
            s!"transport hq {g.name}"
          let hif ← Driver.proveByDecide
            (← mkEq (← isN "IF") (mkConst ``Bool.false))
            s!"transport hif {g.name}"
          let hlet ← Driver.proveByDecide
            (← mkEq (← mkAppM ``Bool.or #[← isN "LET", ← isN "LET*"])
              (mkConst ``Bool.false)) s!"transport hlet {g.name}"
          let hget ← proveByDecideKernel
            (← mkEq (← mkAppM ``ACL2.DefMap.get?
                #[← mkAppM ``ACL2.World.defs #[cfg.worldExpr],
                  Driver.reflectSymbol g])
              (← mkAppM ``Option.some #[← mkAppM ``Prod.mk
                #[← mkListLit (mkConst ``ACL2.Symbol)
                    [Driver.reflectSymbol x],
                  Driver.reflectSExpr body]]))
            s!"transport hget {g.name}"
          let hfnFree ← Driver.proveByDecide
            (← mkEq (← mkAppM ``List.contains
              #[namesE, Driver.reflectSymbol g]) (mkConst ``Bool.false))
            s!"transport notAlias {g.name}"
          let hbodyFree ← proveByDecideKernel
            (← mkEq (← mkAppM ``ACL2.Replay.fnFreeTerm
              #[namesE, Driver.reflectSExpr body])
              (mkConst ``Bool.true)) s!"transport bodyFree {g.name}"
          let pf ← mkAppM ``ACL2.Replay.total_fnalias_transport
            #[namesE, cfg.worldExpr, wAliasE, hagree, hw,
              Driver.reflectSymbol g, Driver.reflectSymbol x,
              Driver.reflectSExpr body, hq, hif, hlet, hget,
              hfnFree, hbodyFree, hFv]
          unless ← isDefEq (← inferType pf) wantTy do
            return none
          pure (some pf)
        | _ => pure none
    -- W4f: the consumer-side premise bridges
    let consumerRules :=
      (ACL2.Replay.Runner.allBookRules consumerDev)
      ++ crossDevs.flatMap (fun (_, d) =>
          ACL2.Replay.Runner.allBookRules d)
    let consumerDepProofs :=
      (ACL2.Replay.Runner.bookTrees consumerDev)
      ++ crossDevs.flatMap (fun (_, d) =>
          ACL2.Replay.Runner.bookTrees d)
    let fnFreeV := fun (t : SExpr) =>
      ACL2.Replay.fnFreeTerm names t == true
    let ruleBridge := fun (rspec : ACL2.RuleSpec) (bTy : Expr) => do
      if fnFreeV rspec.lhs && fnFreeV rspec.rhs
          && rspec.hyps.all fnFreeV then
        -- CLASS 1: bind the CONSUMER telescope's matching rule fvar,
        -- crossed by A (hypothesis-free equal shape only)
        match ctx.ruleHyps.find? (fun (r, _) =>
            r.name == rspec.name && r.hyps == rspec.hyps
            && r.lhs == rspec.lhs && r.rhs == rspec.rhs
            && r.equiv == rspec.equiv) with
        | some (_, hFv) =>
          if rspec.hyps.isEmpty && rspec.equiv == "equal" then do
            let pf ← withLocalDeclD `envr (mkConst ``ACL2.Env)
              fun erV => do
                let hAtW := mkApp hFv erV
                let pfc ← mkAppM ``ACL2.Replay.fuelEq_fnfree_cross
                  #[namesE, cfg.worldExpr, wAliasE, hagree, hw,
                    Driver.reflectSExpr rspec.lhs,
                    Driver.reflectSExpr rspec.rhs,
                    ← Driver.proveByDecide (← mkEq
                      (← mkAppM ``ACL2.Replay.fnFreeTerm
                        #[namesE, Driver.reflectSExpr rspec.lhs])
                      (mkConst ``Bool.true)) "bridge fnFree lhs",
                    ← Driver.proveByDecide (← mkEq
                      (← mkAppM ``ACL2.Replay.fnFreeTerm
                        #[namesE, Driver.reflectSExpr rspec.rhs])
                      (mkConst ``Bool.true)) "bridge fnFree rhs",
                    erV, hAtW]
                mkLambdaFVars #[erV] pfc
            pure (some (← Lean.Meta.mkExpectedTypeHint pf bTy))
          else pure none
        | none => pure none
      else
        -- CLASS 2: alias-mentioning constraint rule — discharge the
        -- SUBSTITUTED consumer rule at the consumer world, lift by the
        -- W3 lemmas. Hypothesis-free (STRONG's six), or — the W3
        -- ONE-HYP lift (endgame arc, charter item 5) — exactly one
        -- FN-FREE hypothesis (TRUE-LISTP-SORTFN1/2's `(TRUE-LISTP X)`
        -- shape): the hyp crosses worlds by `evtrue_fnfree_agree_iff`
        -- and the conclusion lifts exactly as before.
        if rspec.equiv != "equal" || rspec.hyps.length > 1 ||
            !rspec.hyps.all fnFreeV then pure none
        else do
        let slhs := ACL2.Replay.substFnCalls σ rspec.lhs
        let srhs := ACL2.Replay.substFnCalls σ rspec.rhs
        let shyps := rspec.hyps.map (ACL2.Replay.substFnCalls σ ·)
        -- exactly-one DISTINCT match (close-out audit O-2, refined in
        -- the fix round: the pool can carry byte-identical copies of
        -- one rule via the own/cross channels — those are not an
        -- ambiguity; two DIFFERENT same-shaped rules are, and get
        -- refused rather than silently resolved to the first)
        -- a HYP-FREE consumer rule may discharge a one-hyp constraint
        -- (strictly stronger; the premise's hyp binder is simply unused —
        -- TRUE-LISTP-ISORT's unconditional `(TRUE-LISTP (ISORT X)) = 'T`
        -- vs TRUE-LISTP-SORTFN2's conditional constraint)
        let cands := (consumerRules.filter (fun r =>
            (r.hyps == shyps || r.hyps.isEmpty) && r.equiv == "equal"
            && r.lhs == slhs && r.rhs == srhs)).eraseDups
        if cands.length > 1 then
          Driver.throwFrontier m!"usefi ruleBridge: {cands.length} \
            distinct same-shaped consumer rules match the substituted \
            constraint (ambiguous — refuse rather than guess)"
        else
        match cands with
        | [] => pure none
        | cspec :: _ => do
          -- discharge with the OWNING book's channel surfaces (its gz
          -- fc/tp/recog snapshots carry what its trees cite) + the
          -- consumer-world recorded-termination pre-pass results
          let ownCfg := match crossDevs.find? (fun (_, d) =>
              (Driver.findThm d cspec.name).isSome) with
            | some (_, ownDev) =>
              { ACL2.Replay.Runner.mkBookConfig ownDev cfg.worldVal
                  cfg.worldExpr cfg.envExpr with
                termReplayed := termByFn }
            | none => { cfg with termReplayed := termByFn }
          let pfW ← try
              dischargeRuleHyp ownCfg ctx cspec consumerDepProofs []
            catch e => Driver.throwFrontier m!"usefi bridge: consumer \
              discharge of {cspec.name} failed: {e.toMessageData}"
          withLocalDeclD `envr (mkConst ``ACL2.Env) fun erV => do
            -- W3 one-hyp: bind the alias-world hypothesis binder and
            -- cross it to the consumer world by fn-freeness
            let hypDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
              (rspec.hyps.map fun h0 =>
                (`hh, BinderInfo.default, fun (_ : Array Expr) => do
                  mkAppM ``EvTrue #[wAliasE, erV, Driver.reflectSExpr h0])).toArray
            withLocalDecls hypDecls fun hypVs => do
            let hAtW ← do
              let mut acc := mkApp pfW erV
              -- apply exactly the CONSUMER rule's hypotheses (== the
              -- substituted constraint's, or NONE when the consumer rule
              -- is the stronger hyp-free form)
              for (h0, hhV) in (rspec.hyps.zip hypVs.toList).take
                  cspec.hyps.length do
                let hfree ← Driver.proveByDecide (← mkEq
                  (← mkAppM ``ACL2.Replay.fnFreeTerm
                    #[namesE, Driver.reflectSExpr h0])
                  (mkConst ``Bool.true)) "bridge fnFree hyp"
                let iff ← mkAppM ``ACL2.Replay.evtrue_fnfree_agree_iff
                  #[namesE, cfg.worldExpr, wAliasE, hagree, hw, erV,
                    Driver.reflectSExpr h0, hfree]
                acc := mkApp acc (← mkAppM ``Iff.mp #[iff, hhV])
              pure acc
            let mkFnFreePf := fun (t : SExpr) (what : String) => do
              Driver.proveByDecide (← mkEq
                (← mkAppM ``ACL2.Replay.fnFreeTerm
                  #[namesE, Driver.reflectSExpr t])
                (mkConst ``Bool.true)) what
            let hwsL ← Driver.proveByDecide (← mkEq
              (← mkAppM ``ACL2.Replay.WellScoped
                #[Driver.reflectSExpr rspec.lhs])
              (mkConst ``Bool.true)) "bridge WS lhs"
            let hsimpL ← Driver.proveByDecide (← mkEq
              (← mkAppM ``ACL2.Replay.aliasArgsSimple
                #[namesE, Driver.reflectSExpr rspec.lhs])
              (mkConst ``Bool.true)) "bridge simple lhs"
            let pfc ←
              match rspec.rhs with
              | .cons (.atom (.symbol q)) (.cons c .nil) =>
                if q.name == "QUOTE" then
                  mkAppM ``ACL2.Replay.fuelEq_fnalias_lift_const
                    #[σE, cfg.worldExpr, wAliasE, hσdef, hσns, hσws,
                      hσcl, hagree, hw, Driver.reflectSExpr rspec.lhs,
                      Driver.reflectSExpr c, hwsL, hsimpL,
                      ← mkFnFreePf slhs "bridge fnFree slhs",
                      erV, hAtW]
                else Driver.throwFrontier m!"usefi bridge: non-quote \
                  symbol rhs (frontier)"
              | _ => do
                -- general rhs: convergence from the consumer totality
                -- hypothesis probed at the (variable) arguments
                let hconv ← match rspec.rhs with
                  | .cons (.atom (.symbol g))
                      (.cons (.atom (.symbol a1))
                        (.cons (.atom (.symbol a2)) .nil)) => do
                    let some (_, hTot) := ctx.totalHyps.find?
                        (fun (n, _) => n == g.name)
                      | Driver.throwFrontier m!"usefi bridge: no \
                          consumer totality for {g.name}"
                    let c1 ← mkAppM ``ACL2.Replay.var_conv_ex
                      #[cfg.worldExpr, erV, Driver.reflectSymbol a1]
                    let c2 ← mkAppM ``ACL2.Replay.var_conv_ex
                      #[cfg.worldExpr, erV, Driver.reflectSymbol a2]
                    let happ := mkAppN hTot #[erV,
                      Driver.reflectSExpr (.atom (.symbol a1)),
                      Driver.reflectSExpr (.atom (.symbol a2)), c1, c2]
                    mkAppM ``ACL2.Replay.conv_repack #[happ]
                  | _ => Driver.throwFrontier m!"usefi bridge: \
                      unsupported general rhs shape"
                mkAppM ``ACL2.Replay.fuelEq_fnalias_lift
                  #[σE, cfg.worldExpr, wAliasE, hσdef, hσns, hσws,
                    hσcl, hagree, hw, Driver.reflectSExpr rspec.lhs,
                    Driver.reflectSExpr rspec.rhs, hwsL, hsimpL,
                    ← mkFnFreePf slhs "bridge fnFree slhs",
                    ← mkFnFreePf rspec.rhs "bridge fnFree rhs",
                    erV, hAtW, hconv]
            let pf ← mkLambdaFVars (#[erV] ++ hypVs) pfc
            pure (some (← Lean.Meta.mkExpectedTypeHint pf bTy))
    let useBridge := fun (uspec : UseSpec) (bTy : Expr) => do
      -- alias-free cited theorem: discharge at the consumer world,
      -- cross by the EvTrue iff
      if !fnFreeV uspec.formula then pure none else do
      let ownCfg := match crossDevs.find? (fun (_, d) =>
          (Driver.findThm d uspec.name).isSome) with
        | some (_, ownDev) =>
          { ACL2.Replay.Runner.mkBookConfig ownDev cfg.worldVal
              cfg.worldExpr cfg.envExpr with
            termReplayed := termByFn }
        | none => { cfg with termReplayed := termByFn }
      let pfW ← try
          dischargeUseHyp ownCfg ctx uspec consumerDepProofs []
        catch e => Driver.throwFrontier m!"usefi useBridge: consumer \
          discharge of {uspec.name} failed: {e.toMessageData}"
      do
      withLocalDeclD `envr (mkConst ``ACL2.Env) fun erV => do
        let hAtW := mkApp pfW erV
        let hfree ← Driver.proveByDecide (← mkEq
          (← mkAppM ``ACL2.Replay.fnFreeTerm
            #[namesE, Driver.reflectSExpr uspec.formula])
          (mkConst ``Bool.true)) "useBridge fnFree"
        let iff ← mkAppM ``ACL2.Replay.evtrue_fnfree_agree_iff
          #[namesE, cfg.worldExpr, wAliasE, hagree, hw, erV,
            Driver.reflectSExpr uspec.formula, hfree]
        let pfc ← mkAppM ``Iff.mpr #[iff, hAtW]
        let pf ← mkLambdaFVars #[erV] pfc
        pure (some (← Lean.Meta.mkExpectedTypeHint pf bTy))
    let (pfAtAlias, kept, _concl) ← instantiateParametricAt depDev
      wAliasVal wAliasE spec.name depCrossTrees depCrossRules totsNames
      pfParamEnv envV (extraJusts := cfg.justs)
      (innerTotalFallback := innerTotalFallback)
      (ruleBridge := ruleBridge) (useBridge := useBridge)
    unless kept.isEmpty do
      Driver.throwFrontier m!"usefi discharge: premises KEPT at the \
        alias world (bridging pending): [{", ".intercalate kept}]"
    -- DECLARE the alias-world proof as a constant NOW, at SINGLE
    -- parametric depth (the scale the sweep's own registrations already
    -- handle) — composing it inline doubled the term depth past every
    -- recursive Expr walk downstream (the W4f SIGABRTs). Free vars
    -- (envV + consumer-telescope hypotheses) are abstracted and
    -- re-applied.
    let pfA ← Lean.instantiateMVars pfAtAlias
    let fvIdsA ← Lean.Meta.sortFVarIds
      ((Lean.collectFVars {} pfA).fvarSet.toList.toArray)
    let fvExprsA := fvIdsA.map Lean.mkFVar
    let pfAClosed ← mkLambdaFVars fvExprsA pfA
    let keyA := (cfg.worldExpr.constName?.map (·.toString)).getD "anon"
      ++ "_atAlias_" ++ spec.name
      ++ "_" ++ toString (hash (toString (repr spec.formula)))
    let cNameA := Lean.Name.mkStr2 "UsefiDischarged"
      (String.map (fun c => if c.isAlphanum then c else '_') keyA)
    let pfAtAlias ← do
      if (← Lean.getEnv).contains cNameA then
        pure (mkAppN (mkConst cNameA) fvExprsA)
      else do
        let phi0 ← match cp.root with
          | some r => match r.inputClause with
            | [f] => pure f
            | _ => Driver.throwFrontier m!"usefi: multi-literal Goal"
          | none => Driver.throwFrontier m!"usefi: no tree"
        let tyA ← mkForallFVars fvExprsA
          (mkAppN (mkConst ``ACL2.Replay.EvTrue)
            #[wAliasE, envV, Driver.reflectSExpr phi0])
        Lean.Meta.check tyA
        Lean.addDecl <| .thmDecl
          { name := cNameA, levelParams := [], type := tyA,
            value := pfAClosed }
        pure (mkAppN (mkConst cNameA) fvExprsA)
    -- (3) cross to the consumer world
    let some root := cp.root
      | Driver.throwFrontier m!"usefi discharge: {spec.name} has no tree"
    let [phi] := root.inputClause
      | Driver.throwFrontier m!"usefi discharge: {spec.name}'s Goal is \
          not single-literal"
    let phiE := Driver.reflectSExpr phi
    let hws ← proveByDecideKernel
      (← mkEq (← mkAppM ``ACL2.Replay.WellScoped #[phiE])
        (mkConst ``Bool.true)) "usefi WellScoped Φ"
    let hfree ← proveByDecideKernel
      (← mkEq (← mkAppM ``ACL2.Replay.fnFreeTerm
        #[namesE, ← mkAppM ``ACL2.Replay.substFnCalls #[σE, phiE]])
        (mkConst ``Bool.true)) "usefi fnFree image"
    let pfCross ← mkAppM ``ACL2.Replay.evtrue_fnalias
      #[σE, cfg.worldExpr, wAliasE, hσdef, hσns, hσws, hσcl, hagree,
        hw, phiE, hws, hfree, envV, pfAtAlias]
    let target := mkAppN (mkConst ``ACL2.Replay.EvTrue)
      #[cfg.worldExpr, envV, Driver.reflectSExpr spec.formula]
    -- NO elaborator-side type gate on the giant term (each inferType
    -- walk is a stack overflow at this depth) — the kernel verifies
    -- the whole value against the CONSTRUCTED type at addDecl below
    let pfAll ← mkLambdaFVars #[envV]
      (← Lean.Meta.mkExpectedTypeHint pfCross target)
    -- DECLARE the discharged hypothesis as a CONSTANT (the D1 pattern):
    -- the row proof then references it small — an inline nesting of the
    -- parametric proof inside the row proof doubled the term depth past
    -- the elaborator checker's stack (the second W4f SIGABRT); the
    -- kernel checks the constant once here. KEPT consumer-telescope
    -- fvars would escape the declaration — this route requires the
    -- discharge to be CLOSED (checked below); a conditional result
    -- frontiers honestly.
    let pfC0 ← Lean.instantiateMVars pfAll
    -- prepare-time closure of parameters the ROW telescope cannot
    -- supply: cross-book cong/equivRefl/equivFull hypotheses consumed
    -- by the bridges' inner re-replays are discharged HERE (shallow
    -- stack, owning-book channels) and let-bound into the constant;
    -- a frontier leaves the parameter abstracted (row-match may then
    -- keep the usefi hypothesis — honest)
    let ownCfgFor := fun (n : String) =>
      match crossDevs.find? (fun (_, d) =>
          (Driver.findThm d n).isSome) with
      | some (_, ownDev) =>
        { ACL2.Replay.Runner.mkBookConfig ownDev cfg.worldVal
            cfg.worldExpr cfg.envExpr with termReplayed := termByFn }
      | none => { cfg with termReplayed := termByFn }
    let mut pfCm := pfC0
    for (cspec, hv) in ctx.congHyps do
      if pfCm.containsFVar hv.fvarId! then
        try
          let pf ← Driver.dischargeCongHyp (ownCfgFor cspec.name) ctx
            cspec consumerDepProofs []
          pfCm ← Driver.letBindFVar pfCm hv pf
        catch _ => pure ()
    for (espec, hv) in ctx.equivReflHyps do
      if pfCm.containsFVar hv.fvarId! then
        try
          let pf ← Driver.dischargeEquivReflHyp (ownCfgFor espec.name)
            ctx espec consumerDepProofs []
          pfCm ← Driver.letBindFVar pfCm hv pf
        catch _ => pure ()
    for (fspec, hv) in ctx.equivFullHyps do
      if pfCm.containsFVar hv.fvarId! then
        try
          let pf ← Driver.dischargeEquivFullHyp (ownCfgFor fspec.name)
            ctx fspec consumerDepProofs []
          pfCm ← Driver.letBindFVar pfCm hv pf
        catch _ => pure ()
    let pfC ← Lean.instantiateMVars pfCm
    -- consumer-telescope fvars (the transports/Class-1 bindings) are
    -- λ-ABSTRACTED into the constant and re-applied at the reference,
    -- so the constant is closed and the row proof stays conditional on
    -- exactly those hypotheses (letBound by the pass like any other)
    let fvIds ← Lean.Meta.sortFVarIds
      ((Lean.collectFVars {} pfC).fvarSet.toList.toArray)
    let fvExprs := fvIds.map Lean.mkFVar
    let pfClosed ← mkLambdaFVars fvExprs pfC
    let declTy ← mkForallFVars fvExprs
      (← mkForallFVars #[envV] target)
    let key := (cfg.worldExpr.constName?.map (·.toString)).getD "anon"
      ++ "_" ++ spec.name
      ++ "_" ++ toString (hash (toString (repr spec.formula)))
    let cName := Lean.Name.mkStr2 "UsefiDischarged"
      (String.map (fun c => if c.isAlphanum then c else '_') key)
    if (← Lean.getEnv).contains cName then
      pure (mkAppN (mkConst cName) fvExprs)
    else do
      Lean.Meta.check declTy
      Lean.addDecl <| .thmDecl
        { name := cName, levelParams := [],
          type := declTy, value := pfClosed }
      pure (mkAppN (mkConst cName) fvExprs)

/-- D2-a PRE-PASS (the ReplayedTermination pattern, applied to usefi):
    run the WHOLE discharge composition in a SHALLOW stack context —
    before any row telescope exists — against FRESHLY DECLARED
    replicas of the consumer-hypothesis surfaces, and capture the
    declared constant plus its parameter types.  The row-time
    discharger then just matches parameters to the row's own telescope
    fvars and applies — constant work on the deep stack.  (Root cause:
    `withLocalDecls` spends one native frame per binder; the row's
    corpus-wide telescope keeps thousands live through every discharge
    pass, and the composition on top overflowed the lake worker
    thread.) -/
def prepareUseFi (crossDevs : List (String × Development))
    (totsNames : List Name) (consumerDev : Development)
    (worldVal : World) (wExpr : Expr) (spec : UseFiSpec)
    (termByFn : List (String × Lean.Name × List String × List SExpr)
      := []) :
    Lean.MetaM (Lean.Name × List (String × String)) := do
  Lean.Meta.withLocalDeclD `envDummy (mkConst ``ACL2.Env) fun envD => do
    let cfg := ACL2.Replay.Runner.mkBookConfig consumerDev worldVal
      wExpr envD
    -- synthetic consumer surfaces: totality offers for every world fn,
    -- rule offers for the full accumulation (correctness first; the
    -- demand-filter tuning is a follow-up)
    let fns := worldVal.defs.entries
    let totalDecls : Array (Lean.Name × Lean.BinderInfo ×
        (Array Expr → Lean.MetaM Expr)) :=
      (fns.map fun (sy, formals, _) =>
        (Lean.Name.mkSimple s!"ptot_{sy.name}", Lean.BinderInfo.default,
         fun _ => Driver.mkTotalityHypType cfg sy formals.length)).toArray
    let rules :=
      (ACL2.Replay.Runner.allBookRules consumerDev)
      ++ crossDevs.foldl (init := [])
        (fun acc (_, d) => acc
          ++ (ACL2.Replay.Runner.allBookRules d).filter
            (fun r => !acc.any (fun o => o.runeKey == r.runeKey)))
    let rules := rules.filter fun r =>
      r.equiv == "equal" ||
      (r.equiv != "iff" &&
       match worldVal.defs.get? { name := r.equiv.map Char.toUpper } with
       | some (formals, _) => formals.length == 2
       | none => false)
    let ruleDecls : Array (Lean.Name × Lean.BinderInfo ×
        (Array Expr → Lean.MetaM Expr)) :=
      (rules.zipIdx.map fun (r, i) =>
        (Lean.Name.mkSimple s!"prule_{i}", Lean.BinderInfo.default,
         fun _ => Driver.mkRuleHypType cfg r)).toArray
    -- tp offers (the liftable/args-valued split, replicated from
    -- replayProofConditional's derivation)
    let tps := consumerDev.typePrescriptions
    let scrubbedFreeVars := fun (fn : Symbol) (formals : List Symbol)
        (cor : SExpr) =>
      let appPat : SExpr :=
        .cons (.atom (.symbol fn))
          ((formals.map (SExpr.atom ∘ Atom.symbol)).foldr SExpr.cons .nil)
      let rec scrub : SExpr → SExpr := fun t =>
        if t == appPat then .nil
        else match t with
          | .cons a b => .cons (scrub a) (scrub b)
          | t => t
      ACL2.Replay.freeVars (scrub cor)
    let tpFns := fns.filterMap fun (sy, formals, _) =>
      (tps.lookup sy.name).bind fun cor =>
        if (scrubbedFreeVars sy formals cor).isEmpty then
          some (sy, formals, cor)
        else none
    let tpAvFns := fns.filterMap fun (sy, formals, _) =>
      (tps.lookup sy.name).bind fun cor =>
        let vs := scrubbedFreeVars sy formals cor
        if !vs.isEmpty && vs.all (formals.contains ·) then
          some (sy, formals, cor)
        else none
    let tpDecls : Array (Lean.Name × Lean.BinderInfo ×
        (Array Expr → Lean.MetaM Expr)) :=
      (tpFns.map fun (sy, formals, cor) =>
        (Lean.Name.mkSimple s!"ptp_{sy.name}", Lean.BinderInfo.default,
         fun _ => Driver.mkTpHypType cfg sy formals cor)).toArray
    let tpAvDecls : Array (Lean.Name × Lean.BinderInfo ×
        (Array Expr → Lean.MetaM Expr)) :=
      (tpAvFns.map fun (sy, formals, cor) =>
        (Lean.Name.mkSimple s!"ptpav_{sy.name}", Lean.BinderInfo.default,
         fun _ => Driver.mkTpHypTypeAv cfg sy formals cor)).toArray
    -- congruence / equiv-refl / equiv-full offers from ALL books'
    -- trees (over-offer; only USED fvars survive into the constant)
    let allTrees :=
      (ACL2.Replay.Runner.bookTrees consumerDev)
      ++ crossDevs.flatMap (fun (_, d) => ACL2.Replay.Runner.bookTrees d)
    let congs : List Driver.CongSpec := allTrees.foldl (init := [])
      fun acc (n, cp) =>
        if acc.any (·.name == n) then acc else
        match cp.root with
        | some root => match root.inputClause with
          | [f] => match Driver.congSpecOfFormula? n f with
            | some sp => acc ++ [sp]
            | none => acc
          | _ => acc
        | none => acc
    let equivRefls :=
      (allTrees.filterMap fun (n, cp) =>
        cp.root.bind fun r => match r.inputClause with
          | [f] => some (n, f) | _ => none)
      ++ consumerDev.includedTheorems
      ++ crossDevs.flatMap (fun (_, d) => d.includedTheorems)
    let equivSpecs : List Driver.EquivReflSpec :=
      equivRefls.foldl (init := []) fun acc (n, f) =>
        if acc.any (·.name == n) then acc else
        match Driver.equivReflSpecOfFormula? n f with
        | some sp => acc ++ [sp]
        | none => acc
    let equivFullSpecs : List Driver.EquivFullSpec :=
      allTrees.foldl (init := []) fun acc (n, cp) =>
        if acc.any (·.name == n) then acc else
        match cp.root with
        | some root => match root.inputClause with
          | [f] => match Driver.equivFullSpecOfGoal? n f with
            | some sp => acc ++ [sp]
            | none => acc
          | _ => acc
        | none => acc
    let congDecls : Array (Lean.Name × Lean.BinderInfo ×
        (Array Expr → Lean.MetaM Expr)) :=
      (congs.map fun c =>
        (Lean.Name.mkSimple s!"pcong_{c.name}", Lean.BinderInfo.default,
         fun _ => Driver.mkCongHypType cfg c)).toArray
    let equivDecls : Array (Lean.Name × Lean.BinderInfo ×
        (Array Expr → Lean.MetaM Expr)) :=
      (equivSpecs.map fun c =>
        (Lean.Name.mkSimple s!"pequivrefl_{c.name}",
         Lean.BinderInfo.default,
         fun _ => Driver.mkEquivReflHypType cfg c)).toArray
    let equivFullDecls : Array (Lean.Name × Lean.BinderInfo ×
        (Array Expr → Lean.MetaM Expr)) :=
      (equivFullSpecs.map fun c =>
        (Lean.Name.mkSimple s!"pequivfull_{c.name}",
         Lean.BinderInfo.default,
         fun _ => Driver.mkEquivFullHypType cfg c)).toArray
    -- linear: offers (equal-descent restructure arc): the bridge's dep
    -- re-replays can be conditional on :LINEAR content
    -- (ORDEREDP-BSORT's recorded-termination bundle keeps
    -- linear:HOW-MANY-BAD-PAIRS-BNEXT) — same dedup as the main harness
    let linearSpecs := cfg.linearRules.foldl (init := [])
      fun acc (r : ACL2.LinearRuleSpec) =>
        if acc.any (fun (q : ACL2.LinearRuleSpec) =>
            q.name == r.name && q.hyps == r.hyps && q.concl == r.concl)
        then acc else acc ++ [r]
    let linearDecls : Array (Lean.Name × Lean.BinderInfo ×
        (Array Expr → Lean.MetaM Expr)) :=
      (linearSpecs.map fun r =>
        (Lean.Name.mkSimple s!"plinear_{r.name}", Lean.BinderInfo.default,
         fun _ => Driver.mkLinearHypType cfg r)).toArray
    Lean.Meta.withLocalDecls totalDecls fun totVs => do
    Lean.Meta.withLocalDecls ruleDecls fun ruleVs => do
    Lean.Meta.withLocalDecls tpDecls fun tpVs => do
    Lean.Meta.withLocalDecls tpAvDecls fun tpAvVs => do
    Lean.Meta.withLocalDecls congDecls fun congVs => do
    Lean.Meta.withLocalDecls equivDecls fun equivVs => do
    Lean.Meta.withLocalDecls equivFullDecls fun equivFullVs => do
    Lean.Meta.withLocalDecls linearDecls fun linVs => do
      let ctx : ReplayCtx :=
        { totalHyps := (fns.map (fun (sy, _, _) => sy.name)).zip
            totVs.toList,
          ruleHyps := rules.zip ruleVs.toList,
          tpHyps := (tpFns.zip tpVs.toList).map
            (fun ((sy, _, cor), h) => (sy.name, cor, h)),
          tpHypsAv := (tpAvFns.zip tpAvVs.toList).map
            (fun ((sy, _, cor), h) => (sy.name, cor, h)),
          congHyps := congs.zip congVs.toList,
          equivReflHyps := equivSpecs.zip equivVs.toList,
          equivFullHyps := equivFullSpecs.zip equivFullVs.toList,
          linearHyps := linearSpecs.zip linVs.toList }
      let pf ← mkUseFiDischarger crossDevs totsNames termByFn
        consumerDev cfg ctx spec
      -- the result is `mkAppN (const) usedFVars`; record each argument
      -- as a (class, key) pair for DIRECT row-time lookup (blind
      -- isDefEq matching over the row pool burned the row's heartbeat
      -- budget)
      let fn := pf.getAppFn
      let some cName := fn.constName?
        | throwError "prepareUseFi: discharge result is not a constant \
            application"
      let keyed ← pf.getAppArgs.toList.mapM fun a => do
        let some fid := a.fvarId?
          | throwError "prepareUseFi: non-fvar constant argument"
        if let some (n, _) := ctx.totalHyps.find?
            (fun (_, h) => h.fvarId! == fid) then
          pure ("total", n)
        else if let some (r, _) := ctx.ruleHyps.find?
            (fun (_, h) => h.fvarId! == fid) then
          pure ("rule", r.runeKey)
        else if let some (n, _, _) := ctx.tpHyps.find?
            (fun (_, _, h) => h.fvarId! == fid) then
          pure ("tp", n)
        else if let some (n, _, _) := ctx.tpHypsAv.find?
            (fun (_, _, h) => h.fvarId! == fid) then
          pure ("tpav", n)
        else if let some (r, _) := ctx.linearHyps.find?
            (fun (_, h) => h.fvarId! == fid) then
          pure ("linear", r.name)
        else
          throwError "prepareUseFi: constant argument outside the \
            row-suppliable classes"
      pure (cName, keyed)

/-- Row-time applier for a prepared usefi constant: match each
    parameter type against the row telescope's hypothesis fvars and
    apply. -/
def applyPreparedUseFi (cName : Lean.Name)
    (keyed : List (String × String)) (ctx : ReplayCtx) :
    Lean.MetaM Expr := do
  let args ← keyed.mapM fun (cls, k) => do
    let h? := match cls with
      | "total" => (ctx.totalHyps.find? (·.1 == k)).map (·.2)
      | "rule" => (ctx.ruleHyps.find? (·.1.runeKey == k)).map (·.2)
      | "tp" => (ctx.tpHyps.find? (·.1 == k)).map (·.2.2)
      | "tpav" => (ctx.tpHypsAv.find? (·.1 == k)).map (·.2.2)
      | "linear" =>
        -- exactly-one (restructure-arc audit N6 — LinearRuleSpec has no
        -- idx, so one rune can name content-distinct rules; refuse
        -- ambiguity like depMirrorProofAt rather than take the first)
        match ctx.linearHyps.filter (·.1.name == k) with
        | [(_, h)] => some h
        | _ => none
      | _ => none
    match h? with
    | some h => pure h
    | none => Driver.throwFrontier m!"usefi apply: no row hypothesis \
        for prepared parameter {cls}:{k}"
  pure (Lean.mkAppN (mkConst cName) args.toArray)

end ACL2.Imported.Mirrors
