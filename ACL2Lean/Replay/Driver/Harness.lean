/-
  Driver/Harness — split from Driver/Core (WP2 Stage 3a, 2026-07-17;
  see docs/plans/2026-07-18_driver-modular-refactor.md).

  Walker-dependent entry points: replayProof, dischargeRuleHyp, and the
  conditional-replayed-statement harness (replayProofConditional).
-/
import ACL2Lean.Replay.Driver.Core
import ACL2Lean.Replay.Driver.Provers

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- Replay a whole theorem's proof tree to its replayed statement
    `EvTrue w env cp.formula` (G2: ACL2's own truthiness claim). -/
def replayProof (cfg : ReplayConfig) (cp : ClauseProof) : MetaM Expr := do
  match cp.root with
  | none => throwError "replayProof: theorem {cp.name} has no proof tree"
  | some root => replayClause cfg ReplayCtx.empty root

/-- The dependency theorem's mirror at `envV` — by APPLYING its D1 registry
    constant at the consumer's own telescope fvars when registered, else by
    replaying the dependency inside the shared telescope. Shared by
    `dischargeRuleHyp` and `dischargeCongHyp` (verbatim extraction, G2
    rung 2 — plus the `cong:` condition arm). -/
def depMirrorProofAt (cfg : ReplayConfig) (ctx : ReplayCtx) (name : String)
    (depRoot : ClauseNode) (envV : Expr) (ctxD : ReplayCtx)
    (mirrors : ReplayedRegistry) : MetaM Expr := do
  match mirrors.find? (fun (n, _, _) => n == name) with
  | some (_, decl, depConds) => do
    let condArgs ← depConds.toArray.mapM fun c => do
      if c.startsWith "total:" then
        let fn := (c.drop "total:".length).toString
        let some h := ctx.totalHyps.lookup fn
          | throwError "depMirrorProofAt: registry dependency \
              {name} keeps {c}, absent from the consumer \
              telescope (internal)"
        pure h
      else if c.startsWith "tp:" then
        let fn := (c.drop "tp:".length).toString
        let some (_, _, h) := ctx.tpHyps.find? (fun (nm, _, _) => nm == fn)
          | throwError "depMirrorProofAt: registry dependency \
              {name} keeps {c}, absent from the consumer \
              telescope (internal)"
        pure h
      else if c.startsWith "rule:" then
        let rn := (c.drop "rule:".length).toString
        match ctx.ruleHyps.filter (fun (r, _) => r.runeKey == rn) with
        | [(_, h)] => pure h
        | [] => throwError "depMirrorProofAt: registry dependency \
            {name} keeps {c}, absent from the consumer \
            telescope (internal)"
        | _ => throwError "depMirrorProofAt: registry dependency \
            {name} keeps {c} but the consumer telescope offers \
            several same-named rules (ambiguous — refuse rather than \
            guess)"
      else if c.startsWith "linear:" then
        let rn := (c.drop "linear:".length).toString
        match ctx.linearHyps.filter (fun (r, _) => r.name == rn) with
        | [(_, h)] => pure h
        | _ => throwError "depMirrorProofAt: registry dependency \
            {name} keeps {c}, absent or ambiguous in the consumer \
            telescope (internal)"
      else if c.startsWith "cong:" then
        let cn := (c.drop "cong:".length).toString
        match ctx.congHyps.filter (fun (s, _) => s.name == cn) with
        | [(_, h)] => pure h
        | _ => throwError "depMirrorProofAt: registry dependency \
            {name} keeps {c}, absent or ambiguous in the consumer \
            telescope (internal)"
      else if c.startsWith "use:" then
        -- a dependency replayed with a KEPT use: condition (R7a): the
        -- consumer's telescope offers it only when the same name is cited
        -- in the consumer's own tree — otherwise refuse (frontier at the
        -- registry application, kept honest by the discharge pass)
        let un := (c.drop "use:".length).toString
        match ctx.useHyps.filter (fun (u, _) => u.name == un) with
        | [(_, h)] => pure h
        | _ => throwError "depMirrorProofAt: registry dependency \
            {name} keeps {c}, absent or ambiguous in the consumer \
            telescope (internal)"
      else if c.startsWith "equivfull:" then
        let en := (c.drop "equivfull:".length).toString
        match ctx.equivFullHyps.filter (fun (e, _) => e.name == en) with
        | [(_, h)] => pure h
        | _ => throwError "depMirrorProofAt: registry dependency \
            {name} keeps {c}, absent or ambiguous in the consumer \
            telescope (internal)"
      else if c.startsWith "tpthm:" then
        let tn := (c.drop "tpthm:".length).toString
        match ctx.tpThmHyps.filter (fun (s, _) => s.name == tn) with
        | [(_, h)] => pure h
        | _ => throwError "depMirrorProofAt: registry dependency \
            {name} keeps {c}, absent or ambiguous in the consumer \
            telescope (internal)"
      else throwError "depMirrorProofAt: registry dependency \
          {name} keeps unrecognized condition {c} (internal)"
    pure (mkAppN (mkConst decl) (#[envV] ++ condArgs))
  | none =>
    try replayClause { cfg with envExpr := envV } ctxD depRoot
    catch e => throwFrontier m!"depMirrorProofAt: dependency {name}'s \
        replay failed (frontier): {e.toMessageData}"

/-- DISCHARGE a `rule:<thm>` hypothesis from its dependency theorem's replayed
    mirror (v1 step 5, docs/plans/2026-07-05_theorem-dependency-hypotheses.md):
    obtain the dependency's replayed statement — by APPLYING its D1 registry constant at
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
    (mirrors : ReplayedRegistry := []) : MetaM Expr := do
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
  let routeEqual := spec.equiv == "equal" && concl == eqForm
  let routeBool := spec.equiv == "equal" && concl == spec.lhs && spec.rhs == quoteT
  -- USER-equivalence rule (G2 rung 2): the stored rule's faithful statement
  -- is the interpreted relation — its defthm conclusion must BE the
  -- R-application `(R lhs rhs)`; the hypothesis body is then that term's
  -- truthiness directly (no equality decode).
  let relForm : SExpr := .cons
    (.atom (.symbol { name := spec.equiv.map Char.toUpper }))
    (.cons spec.lhs (.cons spec.rhs .nil))
  let routeRel := spec.equiv != "equal" && concl == relForm
  -- NEGATIVE boolean strengthening (P3, ORDEREDP-MEMB's shape): a defthm
  -- conclusion `(NOT lhs)` stores as `lhs = 'NIL` — the truthy NOT pins
  -- the lhs VALUE to exactly nil (Logic.not is nil-dichotomous; no TP
  -- needed, unlike the positive route's exact-t pin)
  let notForm : SExpr := .cons (.atom (.symbol { name := "NOT" }))
    (.cons spec.lhs .nil)
  let quoteNilS : SExpr := .cons (.atom (.symbol { name := "QUOTE" }))
    (.cons .nil .nil)
  let routeNotBool := spec.equiv == "equal" && concl == notForm
    && spec.rhs == quoteNilS
  unless routeEqual || routeBool || routeRel || routeNotBool do
    throwFrontier m!"dischargeRuleHyp: {spec.name}'s conclusion {repr concl}                 matches neither (equal lhs rhs), the boolean-strengthened                 lhs ⇒ 'T shape, nor the stored-equivalence application                 (frontier)"
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
      -- the dependency's replayed statement at env'. D1 registry hit: APPLY the
      -- dependency's constant at the consumer's own telescope fvars for its
      -- kept conditions (same world — identical hypothesis statements; a
      -- missing/ambiguous mapping is a DEFECT, not a frontier: the consumer
      -- telescope offers every total:/tp:/rule: the dependency could keep).
      -- Otherwise re-replay the dependency inside the shared telescope; a
      -- replay wall in its tree is a FRONTIER for the discharge (keep-hyp).
      let pDep ← depMirrorProofAt cfg ctx spec.name depRoot envV ctxDFixed mirrors
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
      -- the target eval-equality (or, R-route, the conclusion's truthiness)
      let body ←
        if routeRel then
          mkAppM ``evtrue_of_conv_ne_nil
            #[← ctxValProof cfgD ctxDFixed concl, hvC]
        else if routeEqual then do
          let hEq ← mkAppM ``Logic.eq_of_equal_ne_nil #[hvC]
          let convL ← ctxValProof cfgD ctxDFixed spec.lhs
          let convR ← ctxValProof cfgD ctxDFixed spec.rhs
          mkAppM ``fuel_eq_of_conv #[convL, convR, hEq]
        else if routeNotBool then do
          let vC ← ctxValExpr cfgD ctxDFixed concl
          unless vC.isAppOfArity ``Logic.not 1 do
            throwFrontier m!"dischargeRuleHyp: value of {repr concl} is                 not (Logic.not _) (frontier)"
          let hNil ← mkAppM ``nil_of_logic_not_ne_nil #[hvC]
          let pq ← mkAppM ``re_val_quote #[w, envV, reflectSExpr SExpr.nil]
          let hCast ← proveByDecide
            (← mkEq (mkConst ``SExpr.nil) (reflectSExpr SExpr.nil))
            "nil reflects"
          let hEq ← mkAppM ``Eq.trans #[hNil, hCast]
          mkAppM ``fuel_eq_of_conv
            #[← ctxValProof cfgD ctxDFixed spec.lhs, pq, hEq]
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

/-- DISCHARGE a `cong:<thm>` hypothesis from its dependency's replayed statement
    (G2 rung 2). No decode at all: the hypothesis states the WHOLE formula
    (`∀ env', EvTrue w env' formula`) and the dependency's Goal clause IS that
    single-literal formula — recompute-and-checked, then the mirror applied
    at `env'`. -/
def dischargeCongHyp (cfg : ReplayConfig) (ctx : ReplayCtx) (spec : CongSpec)
    (depProofs : List (String × ClauseProof))
    (mirrors : ReplayedRegistry := []) : MetaM Expr := do
  let some cp := depProofs.lookup spec.name
    | throwFrontier m!"dischargeCongHyp: no dependency proof for {spec.name}"
  let some depRoot := cp.root
    | throwFrontier m!"dischargeCongHyp: dependency {spec.name} has no proof tree"
  let [formula] := depRoot.inputClause
    | throwFrontier m!"dischargeCongHyp: dependency {spec.name}'s Goal is not \
        a single-literal clause (frontier)"
  unless formula == spec.formula do
    throwError "dischargeCongHyp: {spec.name}'s Goal {repr formula} ≠ the \
        offered congruence formula {repr spec.formula} (internal)"
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let cfgD := { cfg with envExpr := envV }
    let mut ctxD := { ctx with varVals := [], vals := [], litFacts := [],
                               branchFacts := [], segFacts := [] }
    ctxD ← pinTermOpaques cfgD envV ctxD formula
    let pDep ← depMirrorProofAt cfg ctx spec.name depRoot envV ctxD mirrors
    let pf ← mkLambdaFVars #[envV] pDep
    mkExpectedTypeHint pf (← mkCongHypType cfg spec)

/-- DISCHARGE an `equivfull:<thm>` hypothesis (the R-solidify lane):
    whole-formula from the dependency's replayed statement — the
    `dischargeCongHyp` shape; the offer's spec.formula IS the dep's Goal
    clause (same-source; the load-bearing shape check happened at offer
    time in `equivFullSpecOfGoal?`). -/
def dischargeEquivFullHyp (cfg : ReplayConfig) (ctx : ReplayCtx)
    (spec : EquivFullSpec) (depProofs : List (String × ClauseProof))
    (mirrors : ReplayedRegistry := []) : MetaM Expr := do
  let some cp := depProofs.lookup spec.name
    | throwFrontier m!"dischargeEquivFullHyp: no dependency proof for \
        {spec.name}"
  let some depRoot := cp.root
    | throwFrontier m!"dischargeEquivFullHyp: dependency {spec.name} has no \
        proof tree"
  let [formula] := depRoot.inputClause
    | throwFrontier m!"dischargeEquivFullHyp: dependency {spec.name}'s Goal \
        is not a single-literal clause (frontier)"
  unless formula == spec.formula do
    throwError "dischargeEquivFullHyp: {spec.name}'s Goal {repr formula} ≠ \
        the offered formula {repr spec.formula} (internal)"
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let cfgD := { cfg with envExpr := envV }
    let mut ctxD := { ctx with varVals := [], vals := [], litFacts := [],
                               branchFacts := [], segFacts := [] }
    ctxD ← pinTermOpaques cfgD envV ctxD formula
    let pDep ← depMirrorProofAt cfg ctx spec.name depRoot envV ctxD mirrors
    let pf ← mkLambdaFVars #[envV] pDep
    mkExpectedTypeHint pf (← mkEquivFullHypType cfg spec)

/-- DISCHARGE a `tpthm:<thm>` hypothesis (the first :CLASSES consumer):
    whole-formula from the dependency's replayed statement — the
    `dischargeCongHyp` shape (same-source formula assert). -/
def dischargeTpThmHyp (cfg : ReplayConfig) (ctx : ReplayCtx)
    (spec : TpThmSpec) (depProofs : List (String × ClauseProof))
    (mirrors : ReplayedRegistry := []) : MetaM Expr := do
  let some cp := depProofs.lookup spec.name
    | throwFrontier m!"dischargeTpThmHyp: no dependency proof for {spec.name}"
  let some depRoot := cp.root
    | throwFrontier m!"dischargeTpThmHyp: dependency {spec.name} has no \
        proof tree"
  let [formula] := depRoot.inputClause
    | throwFrontier m!"dischargeTpThmHyp: dependency {spec.name}'s Goal is \
        not a single-literal clause (frontier)"
  unless formula == spec.formula do
    throwError "dischargeTpThmHyp: {spec.name}'s Goal {repr formula} ≠ the \
        offered formula {repr spec.formula} (internal)"
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let cfgD := { cfg with envExpr := envV }
    let mut ctxD := { ctx with varVals := [], vals := [], litFacts := [],
                               branchFacts := [], segFacts := [] }
    ctxD ← pinTermOpaques cfgD envV ctxD formula
    let pDep ← depMirrorProofAt cfg ctx spec.name depRoot envV ctxD mirrors
    let pf ← mkLambdaFVars #[envV] pDep
    mkExpectedTypeHint pf (← mkTpThmHypType cfg spec)

/-- DISCHARGE a `use:<thm>` hypothesis from its dependency's replayed
    statement (R7a): identical to `dischargeCongHyp` — the hypothesis
    states the WHOLE formula and the dependency's Goal clause IS that
    single-literal formula, the mirror applied at `env'`. The formula
    equality below is a SAME-SOURCE consistency assert (offer and
    discharge read the same depProofs root — R7a audit F7), not an
    independent cross-check; the load-bearing check for `use:` is the
    verbatim σ/:HYPS comparison in the consuming arm. -/
def dischargeUseHyp (cfg : ReplayConfig) (ctx : ReplayCtx) (spec : UseSpec)
    (depProofs : List (String × ClauseProof))
    (mirrors : ReplayedRegistry := []) : MetaM Expr := do
  let some cp := depProofs.lookup spec.name
    | throwFrontier m!"dischargeUseHyp: no dependency proof for {spec.name}"
  let some depRoot := cp.root
    | throwFrontier m!"dischargeUseHyp: dependency {spec.name} has no proof tree"
  let [formula] := depRoot.inputClause
    | throwFrontier m!"dischargeUseHyp: dependency {spec.name}'s Goal is not \
        a single-literal clause (frontier)"
  unless formula == spec.formula do
    throwError "dischargeUseHyp: {spec.name}'s Goal {repr formula} ≠ the \
        offered use formula {repr spec.formula} (internal)"
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let cfgD := { cfg with envExpr := envV }
    let mut ctxD := { ctx with varVals := [], vals := [], litFacts := [],
                               branchFacts := [], segFacts := [] }
    ctxD ← pinTermOpaques cfgD envV ctxD formula
    let pDep ← depMirrorProofAt cfg ctx spec.name depRoot envV ctxD mirrors
    let pf ← mkLambdaFVars #[envV] pDep
    mkExpectedTypeHint pf (← mkUseHypType cfg spec)

/-- DISCHARGE an `equivrefl:<thm>` hypothesis from its dependency's replayed
    statement (P3, the ORDERED-PERMS mirror): the dependency is the
    defequiv-shaped theorem (e.g. PERM-IS-AN-EQUIVALENCE) whose translated
    Goal is `(IF (BOOLEANP (R x y)) (IF (R x x) rest 'NIL) 'NIL)` — the
    reflexivity conjunct sits SECOND. Project it at `env'` by the
    and-projection lemmas: conjunct 1 truthy steps right
    (`evtrue_and_left` + `evtrue_and_right`), the refl conjunct's truthiness
    is the offered hypothesis (`evtrue_of_conv_ne_nil`). Shape
    recompute-and-checked against the OFFERED spec; any divergence keeps
    the hypothesis (frontier). -/
def dischargeEquivReflHyp (cfg : ReplayConfig) (ctx : ReplayCtx)
    (spec : EquivReflSpec) (depProofs : List (String × ClauseProof))
    (mirrors : ReplayedRegistry := []) : MetaM Expr := do
  let some cp := depProofs.lookup spec.name
    | throwFrontier m!"dischargeEquivReflHyp: no dependency proof for \
        {spec.name}"
  let some depRoot := cp.root
    | throwFrontier m!"dischargeEquivReflHyp: dependency {spec.name} has no \
        proof tree"
  let [formula] := depRoot.inputClause
    | throwFrontier m!"dischargeEquivReflHyp: dependency {spec.name}'s Goal \
        is not a single-literal clause (frontier)"
  let rxx : SExpr := .cons (.atom (.symbol spec.rel))
    (.cons (.atom (.symbol spec.vx)) (.cons (.atom (.symbol spec.vx)) .nil))
  let qNil : SExpr := .cons (.atom (.symbol { name := "QUOTE" }))
    (.cons .nil .nil)
  let c1 ← match formula with
    | .cons (.atom (.symbol if1)) (.cons c1
        (.cons (.cons (.atom (.symbol if2)) (.cons r2
          (.cons _rest (.cons e2 .nil)))) (.cons e1 .nil))) =>
      if if1.isNamed "IF" && if2.isNamed "IF" && r2 == rxx
          && e1 == qNil && e2 == qNil then pure c1
      else throwFrontier m!"dischargeEquivReflHyp: {spec.name}'s Goal \
          {repr formula} is not the defequiv and-shape with the OFFERED \
          reflexivity conjunct {repr rxx} second (frontier)"
    | _ => throwFrontier m!"dischargeEquivReflHyp: {spec.name}'s Goal \
        {repr formula} is not an IF-conjunction (frontier)"
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let cfgD := { cfg with envExpr := envV }
    let mut ctxD := { ctx with varVals := [], vals := [], litFacts := [],
                               branchFacts := [], segFacts := [] }
    ctxD ← pinTermOpaques cfgD envV ctxD formula
    let pDep ← depMirrorProofAt cfg ctx spec.name depRoot envV ctxD mirrors
    let conv1 ← ctxValProof cfgD ctxD c1
    let hne1 ← mkAppM ``evtrue_and_left #[conv1, pDep]
    let htb1 ← mkAppM ``toBool_true_of_ne_nil #[hne1]
    let hRight ← mkAppM ``evtrue_and_right #[conv1, htb1, pDep]
    let convR ← ctxValProof cfgD ctxD rxx
    let hneR ← mkAppM ``evtrue_and_left #[convR, hRight]
    let body ← mkAppM ``evtrue_of_conv_ne_nil #[convR, hneR]
    let pf ← mkLambdaFVars #[envV] body
    mkExpectedTypeHint pf (← mkEquivReflHypType cfg spec)

/-- The CONDITIONAL generic mirror: bind the machine-generated hypothesis
    telescope (per defined fn: totality; plus the lifted TP corollary when one was
    emitted), replay the theorem under it, and λ-abstract. Returns the proof and
    the condition descriptions (the c2 pattern — obligations explicit in the
    type, discharged later by termination emission / Driver Stage 5). -/
def replayProofConditional (cfg : ReplayConfig) (tps : List (String × SExpr))
    (cp : ClauseProof) (justs : List (String × Justification) := [])
    (rules : List RuleSpec := []) (depProofs : List (String × ClauseProof) := [])
    (mirrors : ReplayedRegistry := [])
    (equivRefls : List (String × SExpr) := [])
    (termReplayed : List (String × Name × List String × List SExpr) := [])
    (congTrees : Option (List (String × ClauseProof)) := none) :
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
  let scrubbedFreeVars := fun (fn : Symbol) (formals : List Symbol) (cor : SExpr) =>
    let appPat : SExpr :=
      .cons (.atom (.symbol fn))
        ((formals.map (SExpr.atom ∘ Atom.symbol)).foldr SExpr.cons .nil)
    let rec scrub : SExpr → SExpr := fun t =>
      if t == appPat then .nil
      else match t with
        | .cons a b => .cons (scrub a) (scrub b)
        | t => t
    ACL2.Replay.freeVars (scrub cor)
  let tpFns := fns.filterMap fun (s, formals, _) =>
    (tps.lookup s.name).bind fun cor =>
      if (scrubbedFreeVars s formals cor).isEmpty then some (s, formals, cor)
      else none
  let tpDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (tpFns.map fun (s, formals, cor) =>
      (Name.mkSimple s!"htp_{s.name}", BinderInfo.default,
       fun (_ : Array Expr) => mkTpHypType cfg s formals cor)).toArray
  -- ARGS-VALUED corollaries (G1 arc 2026-07-29): a corollary whose scrubbed
  -- residue mentions FORMALS bare (the BINARY-APPEND/my-app
  -- `(EQUAL (fn X Y) Y)` disjunct class) is offered in the args-valued
  -- hypothesis shape (`mkTpHypTypeAv`) — the argument VALUES are bound
  -- alongside the application's, so bare-formal occurrences lift to them.
  -- A residue variable that is NOT a formal stays unliftable (not offered,
  -- never mis-stated).
  let tpFnsAv := fns.filterMap fun (s, formals, _) =>
    (tps.lookup s.name).bind fun cor =>
      let vs := scrubbedFreeVars s formals cor
      if !vs.isEmpty && vs.all (formals.contains ·) then some (s, formals, cor)
      else none
  let tpAvDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (tpFnsAv.map fun (s, formals, cor) =>
      (Name.mkSimple s!"htpav_{s.name}", BinderInfo.default,
       fun (_ : Array Expr) => mkTpHypTypeAv cfg s formals cor)).toArray
  -- rule:<thm> hypothesis declarations — only rules created BEFORE this theorem
  -- can be cited by its proof, and the caller passes the development's rules in
  -- creation order, so the same list works for every theorem (unused offers are
  -- dropped by the used-filter below). Binder names are disambiguated by
  -- position when one defthm and-split into several rules of the same name.
  -- EQUAL-class rules are offered as eval-equalities; a USER-equivalence
  -- rule (G2 rung 2) is offered in the INTERPRETED-relation shape
  -- (`EvTrue env' (R lhs rhs)`) when R names a world-defined binary fn.
  -- Anything else (iff; R with no defun in the world) is simply not
  -- offered, never mis-stated — a node applying such a rule hard-fails at
  -- the use site ("no stored-rule hypothesis in scope").
  let rules := rules.filter fun r =>
    r.equiv == "equal" ||
    -- "iff" excluded EXPLICITLY (audit F4): IFF is a ground-zero world
    -- defun, so the world-defined test alone would admit iff-stored rules
    -- — restoring the defense-in-depth the audit-2026-07-06-E guard had
    -- (iff's lane is the SIff machinery, not the interpreted relation)
    (r.equiv != "iff" &&
     match cfg.worldVal.defs.get? { name := r.equiv.map Char.toUpper } with
     | some (formals, _) => formals.length == 2
     | none => false)
  let ruleDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (rules.zipIdx.map fun (r, i) =>
      let nm := if (rules.filter (·.name == r.name)).length > 1 then
        s!"hrule_{r.name}_{i}" else s!"hrule_{r.name}"
      (Name.mkSimple nm, BinderInfo.default,
       fun (_ : Array Expr) => mkRuleHypType cfg r)).toArray
  -- cong:<thm> hypothesis declarations (G2 rung 2): every strictly-earlier
  -- LOCAL theorem whose formula is congruence-shaped is offered as its
  -- whole-formula mirror (`mkCongHypType`); non-matching formulas are not
  -- offered. The OFFER derives from `congTrees` — the SAME-BOOK
  -- earlier-theorems list in creation order (topological citations) —
  -- NOT the full depProofs, which since 2a also carries CROSS-BOOK trees
  -- (audit F1: deriving offers from those would widen the telescope
  -- O(corpus) and break the topological premise; cross-book cong
  -- discharge is a deliberate future extension, not a side effect).
  -- Callers that pass no congTrees (the per-theorem test macros, whose
  -- depProofs IS same-book) keep the old behavior.
  let congs : List CongSpec := (congTrees.getD depProofs).filterMap fun (n, cp) =>
    cp.root.bind fun root =>
      match root.inputClause with
      | [f] => congSpecOfFormula? n f
      | _ => none
  let congDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (congs.map fun c =>
      (Name.mkSimple s!"hcong_{c.name}", BinderInfo.default,
       fun (_ : Array Expr) => mkCongHypType cfg c)).toArray
  -- use:<thm> offers (R7a, close-out Phase 2): DEMAND-DRIVEN — one
  -- whole-formula offer per theorem NAME cited by a plain-:use LMI in
  -- THIS theorem's tree (the payload's :LMI-LST; the offer set stays
  -- narrow, unlike a per-corpus surface). Formula source: the
  -- dependency's Goal clause ONLY (depProofs — same-book + 2a
  -- cross-book), i.e. the TRANSLATED statement. R7a audit F1: statement
  -- surfaces (`equivRefls`/includedTheorems) carry RAW untranslated
  -- formulas (`(+ …)`, `(AND …)`), which can never pass the arm's
  -- verbatim :HYPS cross-check — offering them mislabeled the failure
  -- as "emission divergence"; a cited theorem with no translated Goal
  -- clause is NOT offered and the arm hard-fails honestly in-walk
  -- (the include-book translated-statement emission is the tracked
  -- follow-up). TOPOLOGICAL guard (audit F2): a SAME-BOOK citation
  -- must name a STRICTLY EARLIER theorem — ACL2 cannot cite a later
  -- one, and accepting it also opens a mutual-citation discharge
  -- cycle; cross-book dependency entries are earlier by construction.
  let useSameBook := congTrees.getD depProofs
  let useEarlier :=
    (useSameBook.takeWhile (fun (n, _) => n != cp.name)).map (·.1)
  let useSpecs : List UseSpec :=
    (theoremUseCitedNames cp).filterMap fun n =>
      if n == cp.name then none
      else if useSameBook.any (fun (m, _) => m == n)
              && !useEarlier.contains n then none
      else
        match (depProofs.lookup n).bind (·.root) with
        | some root =>
          match root.inputClause with
          | [f] => some { name := n, formula := f }
          | _ => none
        | none => none
  let useDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (useSpecs.map fun u =>
      (Name.mkSimple s!"husethm_{u.name}", BinderInfo.default,
       fun (_ : Array Expr) => mkUseHypType cfg u)).toArray
  -- equivrefl:<thm> declarations (sorting-completion-2 Class A): every
  -- equivalence-SHAPED defthm formula in scope (incl. INCLUDE-BOOK'd —
  -- passed by the caller) offers its REFLEXIVITY component; include-book
  -- instances have no dependency mirror and stay KEPT (D6-honest).
  let equivSpecs : List EquivReflSpec := equivRefls.filterMap fun (n, f) =>
    equivReflSpecOfFormula? n f
  let equivDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (equivSpecs.map fun c =>
      (Name.mkSimple s!"hequivrefl_{c.name}", BinderInfo.default,
       fun (_ : Array Expr) => mkEquivReflHypType cfg c)).toArray
  -- equivfull:<thm> offers (the R-solidify lane, Phase 3): per theorem
  -- whose TRANSLATED Goal clause parses as the defequiv IF-conjunction,
  -- the whole-formula statement. Derived from depProofs (same-book +
  -- cross-book — PERM-IS-AN-EQUIVALENCE is cross-book for convert-perm's
  -- consumers): equivalence-shaped Goals are rare (one per relation), so
  -- the telescope widening is bounded, unlike the cong-offer decision.
  -- Consumed by the equivalence-rune own-position congruence, anchored to
  -- the step-cited :EQUIVALENCE rune (the BUG-023 discipline).
  let equivFullSpecs : List EquivFullSpec := depProofs.foldl (init := [])
    fun acc (n, cp) =>
      if acc.any (·.name == n) then acc else
      match cp.root with
      | some root =>
        match root.inputClause with
        | [f] => match equivFullSpecOfGoal? n f with
          | some sp => acc ++ [sp]
          | none => acc
        | _ => acc
      | none => acc
  let equivFullDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (equivFullSpecs.map fun e =>
      (Name.mkSimple s!"hequivfull_{e.name}", BinderInfo.default,
       fun (_ : Array Expr) => mkEquivFullHypType cfg e)).toArray
  -- tpthm:<thm> offers (the FIRST :CLASSES consumer, tpthm sub-arc): per
  -- dependency theorem whose emitted :CLASSES names :TYPE-PRESCRIPTION
  -- (bare keyword or a class-list member), the whole-formula statement.
  -- Rare class (one per hand-classed TP theorem); consumed by
  -- replayRecognizer's cited-rune fallback, unused offers dropped.
  -- topological guard (tpthm audit F5, mirroring useSpecs): no
  -- self-offer, and a SAME-BOOK entry must be strictly earlier — ACL2
  -- cannot cite a not-yet-admitted rule, and the cited-rune anchor alone
  -- rests on untrusted fork emission (the BUG-023 class).
  let tpThmSpecs : List TpThmSpec := depProofs.foldl (init := [])
    fun acc (n, dcp) =>
      if acc.any (·.name == n) then acc
      else if n == cp.name then acc
      else if useSameBook.any (fun (m, _) => m == n)
              && !useEarlier.contains n then acc
      else if !classesNameTP dcp.classes then acc
      else match dcp.root with
      | some root =>
        match root.inputClause with
        | [f] => acc ++ [{ name := n, formula := f }]
        | _ => acc
      | none => acc
  let tpThmDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (tpThmSpecs.map fun s =>
      (Name.mkSimple s!"htpthm_{s.name}", BinderInfo.default,
       fun (_ : Array Expr) => mkTpThmHypType cfg s)).toArray
  -- ASSUMED:dp-fact offers (condition threading, sorting-completion-2): one
  -- hypothesis per DISCHARGE leaf in this theorem's tree, typed as the
  -- leaf's DP-lift obligation (`dpFactStmtOfClause` — the same derivation
  -- `replayDischargeNode` runs, isDefEq-checked there). The replay consumes
  -- one only when the obligation is UNPROVABLE (the prove-first fallback),
  -- and the used-filter below drops untouched offers — provable leaves keep
  -- their rows unconditional.
  let tpsAvail := tpFns.map fun (s, _, cor) => (s.name, cor)
  let dpLeafTerms := ((theoremDischargeLeaves cp).map (·.2.2)).eraseDups
  let dpStmts ← dpLeafTerms.mapM fun t => do
    pure (t, ← dpFactStmtOfClause cfg.worldVal tpsAvail t)
  let dpDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (dpStmts.zipIdx.map fun ((_, stmt), i) =>
      (Name.mkSimple s!"hdpfact_{i}", BinderInfo.default,
       fun (_ : Array Expr) => pure stmt)).toArray
  -- linear:<rune> declarations (sorting-absolute 2b): one hypothesis per
  -- CONTENT-distinct cited ground-zero :LINEAR rule snapshot (the emission
  -- carries one entry per stored trigger; maxTerm is instantiation
  -- metadata, not content). Consumed by replayDischargeNode as a
  -- DP-obligation premise; unconsumed offers are dropped by the
  -- used-filter, consumed ones stay honest D6 conditions.
  let linearSpecs := cfg.linearRules.foldl (init := [])
    fun acc r =>
      if acc.any (fun (q : LinearRuleSpec) =>
          q.name == r.name && q.hyps == r.hyps && q.concl == r.concl)
      then acc else acc ++ [r]
  let linearDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (linearSpecs.map fun r =>
      (Name.mkSimple s!"hlinear_{r.name}", BinderInfo.default,
       fun (_ : Array Expr) => mkLinearHypType cfg r)).toArray
  let condsAll :=
    fns.map (fun (s, _, _) => s!"total:{s.name}") ++
    tpFns.map (fun (s, _, _) => s!"tp:{s.name}") ++
    tpFnsAv.map (fun (s, _, _) => s!"tp:{s.name}") ++
    rules.map (fun r => s!"rule:{r.runeKey}") ++
    congs.map (fun c => s!"cong:{c.name}") ++
    useSpecs.map (fun u => s!"use:{u.name}") ++
    equivSpecs.map (fun c => s!"equivrefl:{c.name}") ++
    equivFullSpecs.map (fun e => s!"equivfull:{e.name}") ++
    tpThmSpecs.map (fun s => s!"tpthm:{s.name}") ++
    linearSpecs.map (fun r => s!"linear:{r.name}") ++
    dpStmts.map (fun _ => "ASSUMED:dp-fact")
  withLocalDecls totalDecls fun totalVs => do
    withLocalDecls (tpDecls ++ tpAvDecls) fun tpAllVs => do
     withLocalDecls ruleDecls fun ruleVs => do
      withLocalDecls congDecls fun congVs => do
      withLocalDecls useDecls fun useVs => do
      withLocalDecls equivDecls fun equivVs => do
      withLocalDecls equivFullDecls fun equivFullVs => do
      withLocalDecls tpThmDecls fun tpThmVs => do
      withLocalDecls linearDecls fun linearVs => do
      withLocalDecls dpDecls fun dpVs => do
      let tpVs := tpAllVs.extract 0 tpDecls.size
      let tpAvVs := tpAllVs.extract tpDecls.size tpAllVs.size
      let ctx : ReplayCtx :=
        { totalHyps := (fns.map (fun (s, _, _) => s.name)).zip totalVs.toList,
          tpHyps := (tpFns.zip tpVs.toList).map fun ((s, _, cor), h) => (s.name, cor, h),
          tpHypsAv := (tpFnsAv.zip tpAvVs.toList).map fun ((s, _, cor), h) => (s.name, cor, h),
          ruleHyps := rules.zip ruleVs.toList,
          congHyps := congs.zip congVs.toList,
          useHyps := useSpecs.zip useVs.toList,
          -- audit F1 (linear-verdicts fold-back): the DECLARATION is
          -- content-deduped (hyps/concl determine the hypothesis; ONE
          -- fvar), but the OFFER carries EVERY emitted spec — max-term is
          -- the ONLY thing the premise matcher consumes, and ACL2 stores
          -- one linear-lemma per max-term (dropping the CAR trigger cost
          -- STRONG a spurious ASSUMED:dp-fact). Each spec points at its
          -- content-representative's fvar; the used-filter and cond
          -- labels stay per-declaration.
          linearHyps := cfg.linearRules.filterMap (fun r =>
            (linearSpecs.zipIdx.find? (fun (q, _) =>
              q.name == r.name && q.hyps == r.hyps && q.concl == r.concl)
            ).bind fun (_, i) => linearVs[i]?.map fun v => (r, v)),
          equivReflHyps := equivSpecs.zip equivVs.toList,
          equivFullHyps := equivFullSpecs.zip equivFullVs.toList,
          tpThmHyps := tpThmSpecs.zip tpThmVs.toList,
          dpFactHyps := (dpStmts.map (·.1)).zip dpVs.toList }
      let some root := cp.root
        | throwError "replayProofConditional: theorem {cp.name} has no proof tree"
      let prf ← instantiateMVars (← replayClause cfg ctx root)
      -- defense-in-depth (audit 2026-07-06): PIN the replayed proof to the
      -- root clause's own replayed statement — fidelity must not rest solely
      -- on each handler targeting cn.inputClause
      let rootTy ← mkAppM ``EvTrue
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr (disjoinTerm root.inputClause)]
      let prf ← mkExpectedTypeHint prf rootTy
      -- v1 STEP 5 — LAZY rule-hypothesis discharge: derive each USED
      -- rule:<thm> hypothesis from its dependency's replayed statement,
      -- REVERSE creation order. Creation order is TOPOLOGICAL in the
      -- dependency DAG (ACL2 admits a defthm only after the rules it cites
      -- exist), so a discharge proof can only introduce uses of STRICTLY
      -- EARLIER rules' fvars — one reverse pass substitutes them all.
      let mut prfR := prf
      -- cong:<thm> discharge (G2 rung 2), BEFORE and AFTER the rule pass:
      -- a defcong cites strictly-earlier rules (its discharge replay can
      -- introduce rule-fvar uses, caught by the rule pass below), and a
      -- rule's discharge replay can itself consume a strictly-earlier
      -- congruence (caught by the second pass). Both passes share the
      -- containsFVar guard, so a quiet pass is free.
      -- PER-DISCHARGE heartbeat window (fold-back audit, the F1
      -- nondeterminism): a discharge re-replays a dependency TREE, whose
      -- cost rides the CONSUMER's telescope size (O(corpus) offers in the
      -- sweep) — under the theorem's single budget, main-replay + Σdeps
      -- raced the bound and a near-boundary dep flip was process-state
      -- dependent (the golden flipped between elaborations). A fresh
      -- window per discharge (the ordinary theorem default — a dep
      -- re-replay is at most a theorem replay) makes each outcome
      -- individually far from its bound.
      let dischargeBudget : Nat := 3000000
      let dischargeCongs (prf0 : Expr) : MetaM Expr := do
        let mut prfC := prf0
        for (spec, hypV) in (congs.zip congVs.toList).reverse do
          if prfC.containsFVar hypV.fvarId! then
            try
              let pf ← withRealMaxHeartbeats dischargeBudget <|
                dischargeCongHyp cfg ctx spec depProofs mirrors
              prfC ← letBindFVar prfC hypV pf
            catch e =>
              unless isFrontierErr e do
                throw e
        pure prfC
      -- use:<thm> discharge (R7a) FIRST: a use discharge re-replays the
      -- cited theorem's whole tree, which can consume rule:/cong:/
      -- equivrefl:/total:/tp: fvars — all caught by the passes below. A
      -- use-discharge that would itself need a use: fvar (nested :use
      -- chains) frontiers and stays kept (honest; single pass).
      for (spec, hypV) in (useSpecs.zip useVs.toList).reverse do
        if prfR.containsFVar hypV.fvarId! then
          try
            let pf ← withRealMaxHeartbeats dischargeBudget <|
              dischargeUseHyp cfg ctx spec depProofs mirrors
            prfR ← letBindFVar prfR hypV pf
          catch e =>
            unless isFrontierErr e do
              throw e
      prfR ← dischargeCongs prfR
      -- equivfull:<thm> discharge (the R-solidify lane): whole-formula
      -- from the dependency's replayed statement; BEFORE the rule pass
      -- (its re-replay can consume rule:/cong:/total:/tp: fvars, all
      -- caught below). Frontier failures keep the hypothesis (D6).
      for (spec, hypV) in (equivFullSpecs.zip equivFullVs.toList).reverse do
        if prfR.containsFVar hypV.fvarId! then
          try
            let pf ← withRealMaxHeartbeats dischargeBudget <|
              dischargeEquivFullHyp cfg ctx spec depProofs mirrors
            prfR ← letBindFVar prfR hypV pf
          catch e =>
            unless isFrontierErr e do
              throw e
      -- tpthm:<thm> discharge (the first :CLASSES consumer): same
      -- whole-formula shape and pass discipline.
      for (spec, hypV) in (tpThmSpecs.zip tpThmVs.toList).reverse do
        if prfR.containsFVar hypV.fvarId! then
          try
            let pf ← withRealMaxHeartbeats dischargeBudget <|
              dischargeTpThmHyp cfg ctx spec depProofs mirrors
            prfR ← letBindFVar prfR hypV pf
          catch e =>
            unless isFrontierErr e do
              throw e
      -- equivrefl:<thm> discharge (P3, the ORDERED-PERMS mirror): projected
      -- from the dependency's replayed statement; BEFORE the rule pass —
      -- the dependency's replay can consume rule:/cong: fvars, caught by
      -- the passes below. Frontier failures keep the hypothesis (D6).
      for (spec, hypV) in (equivSpecs.zip equivVs.toList).reverse do
        if prfR.containsFVar hypV.fvarId! then
          try
            let pf ← withRealMaxHeartbeats dischargeBudget <|
              dischargeEquivReflHyp cfg ctx spec depProofs mirrors
            prfR ← letBindFVar prfR hypV pf
          catch e =>
            unless isFrontierErr e do
              throw e
      for (spec, hypV) in (rules.zip ruleVs.toList).reverse do
        if prfR.containsFVar hypV.fvarId! then
          try
            let pf ← withRealMaxHeartbeats dischargeBudget <|
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
      prfR ← dischargeCongs prfR
      let prf ← instantiateMVars prfR
      -- bind only the hypotheses the replay ACTUALLY USED: an unconsumed offer must
      -- not weaken the statement (hypothesis types are mutually independent, so
      -- dropping unused ones is well-formed).
      let used := (condsAll.zip (totalVs ++ tpAllVs ++ ruleVs ++ congVs ++ useVs ++ equivVs ++ equivFullVs ++ tpThmVs ++ linearVs ++ dpVs).toList).filter
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
      let hypFVarsAll := condsAll.zip ((totalVs ++ tpAllVs ++ ruleVs ++ congVs ++ useVs ++ equivVs ++ equivFullVs ++ tpThmVs ++ linearVs ++ dpVs).toList)
      let totalEnv ←
        if neededFns.isEmpty then pure []
        else
          -- `defs.entries` is DEV order (user defuns first, ground zero at
          -- the tail — see buildTotalEnv); the lazy bound is the needed fn
          -- LATEST in dev order. RECORDED-TERMINATION fns need their
          -- GROUND-ZERO dependencies (ACL2-COUNT/O<…, at the entries
          -- tail), so the bound is dropped when one is in play.
          let hasRecorded := neededFns.any
            (fun n => termReplayed.any (·.1 == n))
          let lastUsed? := (cfg.worldVal.defs.entries.filter
            (fun (s, _, _) => neededFns.contains s.name)).getLast?
          buildTotalEnv cfg justs
            (upTo := if hasRecorded then none
                     else lastUsed?.map (fun (s, _, _) => s.name))
            (termReplayed := termReplayed) (hypFVars := hypFVarsAll)
            (tpCors := tps)
      let mut prf := prf
      for (c, v) in used do
        if c.startsWith "total:" then
          match totalEnv.find? (fun (n, _, _) => s!"total:{n}" == c) with
          | some (_, _, pf) => prf ← letBindFVar prf v pf
          | none => pure ()
        else if c.startsWith "tp:" then
          -- the TP prover: derive the emitted-corollary hypothesis from the
          -- fn's body (lifter sprint 2026-07-06); frontier → keep (D6).
          -- ARGS-VALUED tp hypotheses (G1) stay hypothesis-backed: the
          -- prover targets the value-only shape — an honest condition.
          let fnName := (c.drop "tp:".length).toString
          if tpFns.any (fun (s, _, _) => s.name == fnName) then
            match tps.lookup fnName with
            | some cor =>
              try
                let pf ← proveTp cfg totalEnv justs fnName cor
                let pf ← mkExpectedTypeHint pf (← inferType v)
                prf ← letBindFVar prf v pf
              catch e =>
                unless isFrontierErr e do
                  throw e
            | none => pure ()
      -- kept = the hypotheses STILL FREE in the final proof. Recomputed
      -- AFTER all discharges (sorting arc 2026-07-28): a recorded-
      -- termination totality proof may pull in tp:/rule: fvars the replay
      -- itself never touched — they surface here as honest conditions.
      let prfF ← instantiateMVars prf
      let kept := hypFVarsAll.filter (fun (_, v) => prfF.containsFVar v.fvarId!)
      let p ← mkLambdaFVars (kept.map (·.2)).toArray prfF
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
