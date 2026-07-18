/-
  Driver/Harness — split from Driver/Core (WP2 Stage 3a, 2026-07-17;
  see docs/plans/2026-07-18_driver-modular-refactor.md).

  Walker-dependent entry points: replayProof, dischargeRuleHyp, and the
  conditional-mirror harness (replayProofConditional).
-/
import ACL2Lean.Replay.Driver.Core
import ACL2Lean.Replay.Driver.Provers

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- Replay a whole theorem's proof tree to its mirror statement
    `EvTrue w env cp.formula` (G2: ACL2's own truthiness claim). -/
def replayProof (cfg : ReplayConfig) (cp : ClauseProof) : MetaM Expr := do
  match cp.root with
  | none => throwError "replayProof: theorem {cp.name} has no proof tree"
  | some root => replayClause cfg ReplayCtx.empty root

/-- DISCHARGE a `rule:<thm>` hypothesis from its dependency theorem's replayed
    mirror (v1 step 5, docs/plans/2026-07-05_theorem-dependency-hypotheses.md):
    obtain the dependency's mirror — by APPLYING its D1 registry constant at
    the consumer's own telescope fvars (same world, identical hypothesis
    statements) when registered, else by replaying the dependency INSIDE the
    same hypothesis telescope (`ctx` — its own conditions stay as the shared
    fvars, so transitive conditions compose) — then DECODE the mirror to the
    stored-rule statement. The decode recomputes ACL2's create-rewrite-rule
    normalization between two EMITTED artifacts — the defthm formula (the
    dependency's Goal clause) and the stored rule — and hard-fails on any
    mismatch: strip `implies`, flatten the `and`-antecedent (must equal the
    rule's :HYPS), then either the equality conclusion IS (equal lhs rhs), or
    the boolean-strengthened form (conclusion = lhs, rhs = 'T) pinned by the
    head fn's EMITTED :TYPE-PRESCRIPTION. All value-level: MP on
    `Logic.implies`, two-valued `Logic.equal` decode, TP boolean pin. -/
def dischargeRuleHyp (cfg : ReplayConfig) (ctx : ReplayCtx) (spec : RuleSpec)
    (depProofs : List (String × ClauseProof))
    (mirrors : MirrorRegistry := []) : MetaM Expr := do
  let some cp := depProofs.lookup spec.name
    | throwFrontier m!"dischargeRuleHyp: no dependency proof for rule {spec.name}"
  let some depRoot := cp.root
    | throwFrontier m!"dischargeRuleHyp: dependency {spec.name} has no proof tree"
  let [formula] := depRoot.inputClause
    | throwFrontier m!"dischargeRuleHyp: dependency {spec.name}'s Goal is not a                   single-literal clause (frontier)"
  -- recompute-and-check the create-rewrite-rule normalization
  let (hypsF, concl) := match formula with
    | .cons (.atom (.symbol impS)) (.cons h (.cons c .nil)) =>
      if impS.name == "IMPLIES" then (flattenAnd h, c) else ([], formula)
    | _ => ([], formula)
  unless hypsF == spec.hyps do
    throwFrontier m!"dischargeRuleHyp: {spec.name}'s flattened antecedent                 {repr hypsF} ≠ the stored rule's :HYPS {repr spec.hyps}                 (normalization divergence — frontier)"
  let eqForm : SExpr := .cons (.atom (.symbol { name := "EQUAL" }))
    (.cons spec.lhs (.cons spec.rhs .nil))
  let routeEqual := concl == eqForm
  let routeBool := concl == spec.lhs && spec.rhs == quoteT
  unless routeEqual || routeBool do
    throwFrontier m!"dischargeRuleHyp: {spec.name}'s conclusion {repr concl}                 matches neither (equal lhs rhs) nor the boolean-strengthened                 lhs ⇒ 'T shape (frontier)"
  let w := cfg.worldExpr
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let cfgD := { cfg with envExpr := envV }
    let mut ctxD := { ctx with varVals := [], vals := [], litFacts := [],
                               branchFacts := [], segFacts := [] }
    ctxD ← pinTermOpaques cfgD envV ctxD formula
    -- premises: EvTrue w env' hᵢ for each stored-rule hyp
    let premDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      (spec.hyps.zipIdx.map fun (h, i) =>
        (Name.mkSimple s!"h{i}", BinderInfo.default,
         fun (_ : Array Expr) => do
           pure (← mkAppM ``EvTrue #[w, envV, reflectSExpr h]))).toArray
    let ctxDFixed := ctxD
    withLocalDecls premDecls fun premVs => do
      -- the dependency's mirror at env'. D1 registry hit: APPLY the
      -- dependency's constant at the consumer's own telescope fvars for its
      -- kept conditions (same world — identical hypothesis statements; a
      -- missing/ambiguous mapping is a DEFECT, not a frontier: the consumer
      -- telescope offers every total:/tp:/rule: the dependency could keep).
      -- Otherwise re-replay the dependency inside the shared telescope; a
      -- replay wall in its tree is a FRONTIER for the discharge (keep-hyp).
      let pDep ←
        match mirrors.find? (fun (n, _, _) => n == spec.name) with
        | some (_, decl, depConds) => do
          let condArgs ← depConds.toArray.mapM fun c => do
            if c.startsWith "total:" then
              let fn := (c.drop "total:".length).toString
              let some h := ctx.totalHyps.lookup fn
                | throwError "dischargeRuleHyp: registry dependency \
                    {spec.name} keeps {c}, absent from the consumer \
                    telescope (internal)"
              pure h
            else if c.startsWith "tp:" then
              let fn := (c.drop "tp:".length).toString
              let some (_, _, h) := ctx.tpHyps.find? (fun (nm, _, _) => nm == fn)
                | throwError "dischargeRuleHyp: registry dependency \
                    {spec.name} keeps {c}, absent from the consumer \
                    telescope (internal)"
              pure h
            else if c.startsWith "rule:" then
              let rn := (c.drop "rule:".length).toString
              match ctx.ruleHyps.filter (fun (r, _) => r.runeKey == rn) with
              | [(_, h)] => pure h
              | [] => throwError "dischargeRuleHyp: registry dependency \
                  {spec.name} keeps {c}, absent from the consumer \
                  telescope (internal)"
              | _ => throwError "dischargeRuleHyp: registry dependency \
                  {spec.name} keeps {c} but the consumer telescope offers \
                  several same-named rules (ambiguous — refuse rather than \
                  guess)"
            else throwError "dischargeRuleHyp: registry dependency \
                {spec.name} keeps unrecognized condition {c} (internal)"
          pure (mkAppN (mkConst decl) (#[envV] ++ condArgs))
        | none =>
          try replayClause cfgD ctxDFixed depRoot
          catch e => throwFrontier m!"dischargeRuleHyp: dependency {spec.name}'s \
              replay failed (frontier): {e.toMessageData}"
      let convF ← ctxValProof cfgD ctxDFixed formula
      let hFne ← mkAppM ``ne_nil_of_evtrue_conv #[pDep, convF]
      -- conclusion-value truthiness: bare conclusion, or through MP
      let hvC ←
        if spec.hyps.isEmpty then
          pure hFne
        else do
          -- antecedent truthiness from the premises
          let hvHs ← (spec.hyps.zipIdx.toArray.mapM fun (h, i) => do
            let convH ← ctxValProof cfgD ctxDFixed h
            mkAppM ``ne_nil_of_evtrue_conv #[premVs[i]!, convH])
          let rec andNe (hs : List Expr) : MetaM Expr := do
            match hs with
            | [] => throwError "dischargeRuleHyp: internal — no hyps"
            | [h1] => pure h1
            | h1 :: rest => mkAppM ``and_value_ne_nil #[h1, ← andNe rest]
          let hvH ← andNe hvHs.toList
          mkAppM ``implies_value_mp #[hFne, hvH]
      -- the target eval-equality
      let body ←
        if routeEqual then do
          let hEq ← mkAppM ``Logic.eq_of_equal_ne_nil #[hvC]
          let convL ← ctxValProof cfgD ctxDFixed spec.lhs
          let convR ← ctxValProof cfgD ctxDFixed spec.rhs
          mkAppM ``fuel_eq_of_conv #[convL, convR, hEq]
        else do
          -- boolean route: the conclusion's head fn's EMITTED TP pins the
          -- truthy value to exactly t
          let .cons (.atom (.symbol fs)) argsSpine := concl
            | throwFrontier m!"dischargeRuleHyp: boolean conclusion {repr concl}                           is not a fn application (frontier)"
          -- TWO-VALUED trusted-core conclusion (same registry as the
          -- recognizer arm): TRUE-LISTP/CONSP evaluate through their Logic
          -- lifts, whose boolean range is the core's own PROVED semantics —
          -- no emitted TP required. USER fns still consume the EMITTED
          -- :TYPE-PRESCRIPTION (type facts from ACL2, never Lean inference).
          let coreBool? : Option (Name × Name) :=
            if fs.name == "TRUE-LISTP" then
              some (``Logic.trueListp, ``logic_trueListp_ne_nil_t)
            else if fs.name == "CONSP" then
              some (``Logic.consp, ``logic_consp_ne_nil_t)
            else none
          let hT ← match coreBool? with
            | some (liftC, neLemma) => do
              let vC ← ctxValExpr cfgD ctxDFixed concl
              unless vC.isAppOfArity liftC 1 do
                throwFrontier m!"dischargeRuleHyp: value of {repr concl} is                               not ({liftC} _) (frontier)"
              mkAppM neLemma #[vC.appArg!, hvC]
            | none => do
              let some (_, _, tpHyp) := ctx.tpHyps.find? (fun (nm, _, _) => nm == fs.name)
                | throwFrontier m!"dischargeRuleHyp: no :TYPE-PRESCRIPTION hypothesis                           for {fs.name} (emit more, frontier)"
              let some (formals, _) := cfg.worldVal.defs.get? fs
                | throwFrontier m!"dischargeRuleHyp: {fs.name} not defined in the world"
              let args := (argsSpine.toList?).getD []
              unless formals.length == args.length do
                throwFrontier m!"dischargeRuleHyp: arity mismatch instantiating the                         TP of {fs.name}"
              let some (vC, convC) := ctxDFixed.val? concl
                | throwFrontier m!"dischargeRuleHyp: conclusion {repr concl} has no                           pinned value (frontier)"
              let fact := mkAppN tpHyp ((#[envV] : Array Expr)
                ++ (args.map reflectSExpr).toArray ++ #[vC, convC])
              mkAppM ``tp_cond_boolean_t #[vC, fact, hvC]
          let pq ← mkAppM ``re_val_quote #[w, envV, reflectSExpr SExpr.t]
          let hCast ← proveByDecide
            (← mkEq (mkConst ``SExpr.t) (reflectSExpr SExpr.t)) "t reflects"
          let hEq ← mkAppM ``Eq.trans #[hT, hCast]
          mkAppM ``fuel_eq_of_conv #[← ctxValProof cfgD ctxDFixed concl, pq, hEq]
      let pf ← mkLambdaFVars (#[envV] ++ premVs) body
      mkExpectedTypeHint pf (← mkRuleHypType cfg spec)

/-- The CONDITIONAL generic mirror: bind the machine-generated hypothesis
    telescope (per defined fn: totality; plus the lifted TP corollary when one was
    emitted), replay the theorem under it, and λ-abstract. Returns the proof and
    the condition descriptions (the c2 pattern — obligations explicit in the
    type, discharged later by termination emission / Driver Stage 5). -/
def replayProofConditional (cfg : ReplayConfig) (tps : List (String × SExpr))
    (cp : ClauseProof) (justs : List (String × Justification) := [])
    (rules : List RuleSpec := []) (depProofs : List (String × ClauseProof) := [])
    (mirrors : MirrorRegistry := []) :
    MetaM (Expr × List String) := do
  let fns := cfg.worldVal.defs.entries
  -- hypothesis declarations: totality for every defined fn, TP where
  -- emitted. #37 discharges USED totality hypotheses LAZILY after the
  -- replay (prove + substitute) — so theorems that consume no totality pay
  -- nothing, and the per-theorem prover cost is proportional to use.
  let totalDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (fns.map fun (s, formals, _) =>
      (Name.mkSimple s!"htotal_{s.name}", BinderInfo.default,
       fun (_ : Array Expr) => mkTotalityHypType cfg s formals.length)).toArray
  -- only LIFTABLE corollaries become hypotheses: every variable occurrence must be
  -- inside the (fn formals) application (the value-only hypothesis shape). An
  -- unliftable corollary (e.g. my-app's (EQUAL (MY-APP X Y) Y), which mentions Y
  -- bare) is SKIPPED — the fact is simply not offered, never mis-stated.
  let liftable := fun (fn : Symbol) (formals : List Symbol) (cor : SExpr) =>
    let appPat : SExpr :=
      .cons (.atom (.symbol fn))
        ((formals.map (SExpr.atom ∘ Atom.symbol)).foldr SExpr.cons .nil)
    let rec scrub : SExpr → SExpr := fun t =>
      if t == appPat then .nil
      else match t with
        | .cons a b => .cons (scrub a) (scrub b)
        | t => t
    (ACL2.Replay.freeVars (scrub cor)).isEmpty
  let tpFns := fns.filterMap fun (s, formals, _) =>
    (tps.lookup s.name).bind fun cor =>
      if liftable s formals cor then some (s, formals, cor) else none
  let tpDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (tpFns.map fun (s, formals, cor) =>
      (Name.mkSimple s!"htp_{s.name}", BinderInfo.default,
       fun (_ : Array Expr) => mkTpHypType cfg s formals cor)).toArray
  -- rule:<thm> hypothesis declarations — only rules created BEFORE this theorem
  -- can be cited by its proof, and the caller passes the development's rules in
  -- creation order, so the same list works for every theorem (unused offers are
  -- dropped by the used-filter below). Binder names are disambiguated by
  -- position when one defthm and-split into several rules of the same name.
  -- Only EQUAL-class rules are offered (the `liftable` TP precedent): an
  -- iff/user-equivalence rule's hypothesis shape is an L2 frontier — the fact
  -- is simply not offered, never mis-stated, and a node applying such a rule
  -- hard-fails at the use site ("no stored-rule hypothesis in scope").
  let rules := rules.filter (·.equiv == "equal")
  let ruleDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (rules.zipIdx.map fun (r, i) =>
      let nm := if (rules.filter (·.name == r.name)).length > 1 then
        s!"hrule_{r.name}_{i}" else s!"hrule_{r.name}"
      (Name.mkSimple nm, BinderInfo.default,
       fun (_ : Array Expr) => mkRuleHypType cfg r)).toArray
  let condsAll :=
    fns.map (fun (s, _, _) => s!"total:{s.name}") ++
    tpFns.map (fun (s, _, _) => s!"tp:{s.name}") ++
    rules.map (fun r => s!"rule:{r.runeKey}")
  withLocalDecls totalDecls fun totalVs => do
    withLocalDecls tpDecls fun tpVs => do
     withLocalDecls ruleDecls fun ruleVs => do
      let ctx : ReplayCtx :=
        { totalHyps := (fns.map (fun (s, _, _) => s.name)).zip totalVs.toList,
          tpHyps := (tpFns.zip tpVs.toList).map fun ((s, _, cor), h) => (s.name, cor, h),
          ruleHyps := rules.zip ruleVs.toList }
      let some root := cp.root
        | throwError "replayProofConditional: theorem {cp.name} has no proof tree"
      let prf ← instantiateMVars (← replayClause cfg ctx root)
      -- defense-in-depth (audit 2026-07-06): PIN the replayed proof to the
      -- root clause's own mirror statement — fidelity must not rest solely
      -- on each handler targeting cn.inputClause
      let rootTy ← mkAppM ``EvTrue
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr (disjoinTerm root.inputClause)]
      let prf ← mkExpectedTypeHint prf rootTy
      -- v1 STEP 5 — LAZY rule-hypothesis discharge: derive each USED
      -- rule:<thm> hypothesis from its dependency's replayed mirror,
      -- REVERSE creation order. Creation order is TOPOLOGICAL in the
      -- dependency DAG (ACL2 admits a defthm only after the rules it cites
      -- exist), so a discharge proof can only introduce uses of STRICTLY
      -- EARLIER rules' fvars — one reverse pass substitutes them all.
      let mut prfR := prf
      for (spec, hypV) in (rules.zip ruleVs.toList).reverse do
        if prfR.containsFVar hypV.fvarId! then
          try
            let pf ←
              -- a GROUND-ZERO rule has no dependency theorem to replay
              -- (boot-admitted, proofs skipped): its D5 prelude constant
              -- discharges it instead
              match d5GzRules.lookup spec.name with
              | some (decl, nsFn) => dischargeGzRuleHyp cfg spec decl nsFn
              | none => dischargeRuleHyp cfg ctx spec depProofs mirrors
            -- LET-bind, don't substitute: every use site shares one copy
            prfR ← letBindFVar prfR hypV pf
          catch e =>
            -- keep ONLY the discharger's TAGGED frontier-class failures (the
            -- hypothesis stays visible in the type — D6, like totality);
            -- anything else is a real defect: surface it (typed tag, not
            -- message prefix — fail-closed audit N1)
            unless isFrontierErr e do
              throw e
      let prf ← instantiateMVars prfR
      -- bind only the hypotheses the replay ACTUALLY USED: an unconsumed offer must
      -- not weaken the statement (hypothesis types are mutually independent, so
      -- dropping unused ones is well-formed).
      let used := (condsAll.zip (totalVs ++ tpVs ++ ruleVs).toList).filter
        fun (_, v) => prf.containsFVar v.fvarId!
      -- #37 LAZY discharge: prove admission totality only for the USED
      -- total: hypotheses and SUBSTITUTE; likewise the TP prover for USED
      -- tp: hypotheses (whose walks also need totality facts — the bound
      -- covers both name sets). Frontier failures keep the hypothesis
      -- (D6 — visible in the type).
      let usedTotalNames := used.filterMap fun (c, _) =>
        if c.startsWith "total:" then some ((c.drop "total:".length).toString) else none
      let usedTpNames := used.filterMap fun (c, _) =>
        if c.startsWith "tp:" then some ((c.drop "tp:".length).toString) else none
      let neededFns := usedTotalNames ++ usedTpNames
      let totalEnv ←
        if neededFns.isEmpty then pure []
        else
          -- `defs.entries` is DEV order (user defuns first, ground zero at
          -- the tail — see buildTotalEnv); the lazy bound is the needed fn
          -- LATEST in dev order
          let lastUsed? := (cfg.worldVal.defs.entries.filter
            (fun (s, _, _) => neededFns.contains s.name)).getLast?
          buildTotalEnv cfg justs (upTo := lastUsed?.map (fun (s, _, _) => s.name))
      let mut prf := prf
      let mut kept : List (String × Expr) := []
      for (c, v) in used do
        if c.startsWith "total:" then
          match totalEnv.find? (fun (n, _, _) => s!"total:{n}" == c) with
          | some (_, _, pf) => prf ← letBindFVar prf v pf
          | none => kept := kept ++ [(c, v)]
        else if c.startsWith "tp:" then
          -- the TP prover: derive the emitted-corollary hypothesis from the
          -- fn's body (lifter sprint 2026-07-06); frontier → keep (D6)
          let fnName := (c.drop "tp:".length).toString
          match tps.lookup fnName with
          | some cor =>
            try
              let pf ← proveTp cfg totalEnv justs fnName cor
              let pf ← mkExpectedTypeHint pf (← inferType v)
              prf ← letBindFVar prf v pf
            catch e =>
              unless isFrontierErr e do
                throw e
              kept := kept ++ [(c, v)]
          | none => kept := kept ++ [(c, v)]
        else
          kept := kept ++ [(c, v)]
      let p ← mkLambdaFVars (kept.map (·.2)).toArray prf
      return (p, kept.map (·.1))


/-! ## Importer front-end helpers (promoted from the test harness)

`derive_world` defines a `World` constant PROJECTED from a parsed
`Development` (the world the replay reasons over is derived from the log, not
hand-written); `findThm` extracts a theorem's reconstructed proof from a
development by name. -/

private partial def theoremsWithRulesGo (dev : Development)
    (acc : List RuleSpec) : List (ClauseProof × List RuleSpec) :=
  match dev with
  | .bind (.theorem cp) rest => (cp, acc) :: theoremsWithRulesGo rest acc
  | .bind (.rules specs) rest => theoremsWithRulesGo rest (acc ++ specs)
  | .bind _ rest => theoremsWithRulesGo rest acc
  | .done => []

/-- Theorems of a development, each paired with the STORED rules created
    BEFORE it — the rules its proof could cite (creation order; ACL2's
    certification order makes citing a later rule impossible, so the offer
    is exactly the citable set). GROUND-ZERO snapshot rules (D5) seed the
    accumulator: boot-stored, they precede every theorem — the emitted
    `(:GROUND-ZERO-RULES …)` event itself sits at the log's TAIL (capture
    end), so it cannot be picked up by the in-order walk. -/
def developmentTheoremsWithRules (dev : Development) :
    List (ClauseProof × List RuleSpec) :=
  theoremsWithRulesGo dev dev.groundZeroRuleSpecs

/-- The stored rules created BEFORE the first theorem named `nm`
    (case-insensitive) — the `rules` argument for replaying it by name. -/
def rulesBefore (dev : Development) (nm : String) : List RuleSpec :=
  match (developmentTheoremsWithRules dev).find?
    (fun (cp, _) => cp.name.toLower == nm.toLower) with
  | some (_, rules) => rules
  | none => []

/-- All theorems matching a name (case-insensitive), in development order. -/
partial def findThms : Development → String → List ClauseProof
  | .bind (.theorem cp) rest, nm =>
    if cp.name.toLower == nm.toLower then cp :: findThms rest nm
    else findThms rest nm
  | .bind _ rest, nm => findThms rest nm
  | .done, _ => []

/-- The UNIQUE theorem named `nm` (case-insensitive). `none` when absent — and
    also when AMBIGUOUS (two theorems differing only in case): selecting the
    first match would silently pick a theorem the caller did not name, so we
    refuse to guess (fail-closed; audited 2026-06-10). -/
def findThm (dev : Development) (nm : String) : Option ClauseProof :=
  match findThms dev nm with
  | [cp] => some cp
  | _ => none

open Lean.Elab Lean.Elab.Command in
/-- `derive_world name from devTerm` — define `name : World` as the world
    PROJECTED from a `Development` (`Development.toWorld`), REFLECTED to a
    concrete (fast-reducing) def. -/
elab "derive_world " id:ident " from " t:term : command => do
  let ns ← Lean.getCurrNamespace
  liftTermElabM do
    let devE ← Lean.Elab.Term.elabTermAndSynthesize t (some (mkConst ``ACL2.Development))
    let dev ← unsafe Lean.Meta.evalExpr ACL2.Development (mkConst ``ACL2.Development) devE
    Lean.addAndCompile <| .defnDecl
      { name := ns ++ id.getId, levelParams := [], type := mkConst ``ACL2.World,
        value := ← reflectWorld dev.toWorld, hints := .abbrev, safety := .safe }
    Lean.enableRealizationsForConst (ns ++ id.getId)


end ACL2.Replay.Driver
