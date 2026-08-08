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
      fun _ _ => pure none) :
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
              found := some (← (some <$> dischargeRuleHyp cfg ctx spec
                  ch.depProofs []) <|> pure none, spec)
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
            match ← (some <$> dischargeUseHyp cfg ctx spec
                ch.depProofs []) <|> pure none with
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
    (totsNames : List Name := []) :
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
    let (pfParam, _pconds) ← Driver.replayProofParametric cfgDep sigFns
      ch.tps cp depDev.justifications
      (ACL2.Replay.Runner.combineRules
        (Driver.rulesBefore depDev spec.name) ch.crossRules)
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
                mkForallFVars #[erV] pfc
            if ← isDefEq (← inferType pf) bTy then pure (some pf)
            else pure none
          else pure none
        | none => pure none
      else
        -- CLASS 2: alias-mentioning constraint rule — discharge the
        -- SUBSTITUTED consumer rule at the consumer world, lift by the
        -- W3 lemmas (hypothesis-free only; STRONG's six qualify)
        if !rspec.hyps.isEmpty || rspec.equiv != "equal" then pure none
        else do
        let slhs := ACL2.Replay.substFnCalls σ rspec.lhs
        let srhs := ACL2.Replay.substFnCalls σ rspec.rhs
        match consumerRules.find? (fun r =>
            r.hyps.isEmpty && r.equiv == "equal"
            && r.lhs == slhs && r.rhs == srhs) with
        | none => pure none
        | some cspec => do
          let pfW ← try
              dischargeRuleHyp cfg ctx cspec consumerDepProofs []
            catch _ => Driver.throwFrontier m!"usefi bridge: consumer \
              discharge of {cspec.name} failed"
          withLocalDeclD `envr (mkConst ``ACL2.Env) fun erV => do
            let hAtW := mkApp pfW erV
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
                      Lean.mkApp (Lean.mkApp (mkConst ``SExpr.atom)
                        (Lean.mkApp (mkConst ``Atom.symbol)
                          (Driver.reflectSymbol a1))) |> fun _ =>
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
            let pf ← mkForallFVars #[erV] pfc
            if ← isDefEq (← inferType pf) bTy then pure (some pf)
            else pure none
    let useBridge := fun (uspec : UseSpec) (bTy : Expr) => do
      -- alias-free cited theorem: discharge at the consumer world,
      -- cross by the EvTrue iff
      if !fnFreeV uspec.formula then pure none else do
      let pfW ← try
          dischargeUseHyp cfg ctx uspec consumerDepProofs []
        catch _ => pure (Expr.const ``True [])
      if pfW.isConst then pure none else do
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
        let pf ← mkForallFVars #[erV] pfc
        if ← isDefEq (← inferType pf) bTy then pure (some pf)
        else pure none
    let (pfAtAlias, kept, _concl) ← instantiateParametricAt depDev
      wAliasVal wAliasE spec.name depCrossTrees depCrossRules totsNames
      pfParamEnv envV (extraJusts := cfg.justs)
      (innerTotalFallback := innerTotalFallback)
      (ruleBridge := ruleBridge) (useBridge := useBridge)
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
    let hws ← proveByDecideKernel
      (← mkEq (← mkAppM ``ACL2.Replay.WellScoped #[phiE])
        (mkConst ``Bool.true)) "usefi WellScoped Φ"
    let hsimp ← proveByDecideKernel
      (← mkEq (← mkAppM ``ACL2.Replay.aliasArgsSimple #[namesE, phiE])
        (mkConst ``Bool.true)) "usefi aliasArgsSimple Φ"
    let hfree ← proveByDecideKernel
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
    let pfAll ← mkForallFVars #[envV]
      (← Lean.Meta.mkExpectedTypeHint pfCross target)
    -- DECLARE the discharged hypothesis as a CONSTANT (the D1 pattern):
    -- the row proof then references it small — an inline nesting of the
    -- parametric proof inside the row proof doubled the term depth past
    -- the elaborator checker's stack (the second W4f SIGABRT); the
    -- kernel checks the constant once here. KEPT consumer-telescope
    -- fvars would escape the declaration — this route requires the
    -- discharge to be CLOSED (checked below); a conditional result
    -- frontiers honestly.
    let pfC ← Lean.instantiateMVars pfAll
    -- consumer-telescope fvars (the transports/Class-1 bindings) are
    -- λ-ABSTRACTED into the constant and re-applied at the reference,
    -- so the constant is closed and the row proof stays conditional on
    -- exactly those hypotheses (letBound by the pass like any other)
    let fvIds ← Lean.Meta.sortFVarIds
      ((Lean.collectFVars {} pfC).fvarSet.toList.toArray)
    let fvExprs := fvIds.map Lean.mkFVar
    let pfClosed ← mkLambdaFVars fvExprs pfC
    let key := (cfg.worldExpr.constName?.map (·.toString)).getD "anon"
      ++ "_" ++ spec.name
      ++ "_" ++ String.intercalate "_" (names.map (·.name))
    let cName := Lean.Name.mkStr2 "UsefiDischarged"
      (String.map (fun c => if c.isAlphanum then c else '_') key)
    if (← Lean.getEnv).contains cName then
      pure (mkAppN (mkConst cName) fvExprs)
    else do
      Lean.addDecl <| .thmDecl
        { name := cName, levelParams := [],
          type := ← Lean.Meta.inferType pfClosed, value := pfClosed }
      pure (mkAppN (mkConst cName) fvExprs)

end ACL2.Imported.Mirrors
