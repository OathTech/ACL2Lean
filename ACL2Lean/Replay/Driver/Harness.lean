/-
  Driver/Harness — split from Driver/Core (WP2 Stage 3a, 2026-07-17;
  see docs/plans/2026-07-18_driver-modular-refactor.md).

  Walker-dependent entry points: replayProof, dischargeRuleHyp, and the
  conditional-replayed-statement harness (replayProofConditional).
-/
import ACL2Lean.Replay.Driver.Core
import ACL2Lean.Replay.Driver.TpProver

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- Replay a whole theorem's proof tree to its replayed statement
    `EvTrue w env cp.formula` (G2: ACL2's own truthiness claim). -/
def replayProof (cfg : ReplayConfig) (cp : ClauseProof) : MetaM Expr := do
  match cp.root with
  | none => throwError "replayProof: theorem {cp.name} has no proof tree"
  | some root => replayClause cfg ReplayCtx.empty root

/-- Select the D1 registry entry for a dependency by NAME **and** by its
    translated Goal FORMULA (WP5): the corpus carries two distinct
    `TRUE-LISTP-RM` theorems (convert-perm-to-how-many's and
    ordered-perms'), and a name-only lookup silently takes whichever entry
    was registered first. A name match whose formula differs is NOT this
    dependency — skip it; several entries agreeing on both are the same
    statement, so the first is used. -/
def findReplayedEntry (replayed : ReplayedRegistry) (name : String)
    (formula : SExpr) : Option ReplayedEntry :=
  replayed.find? (fun e => e.thm == name && e.formula == formula)

/-- Select the dependency tree named `name` whose single-literal translated
    Goal IS `formula` (WP5, P3a latent defect 3). `depProofs` carries
    same-book AND cross-book entries, so the former `List.lookup` could
    hand back a DIFFERENT book's same-named theorem — the corpus's two
    `TRUE-LISTP-RM`s are the live witness. The whole-formula dischargers
    already asserted the formula afterwards, but as an untagged internal
    error: selecting on it instead keeps the hypothesis (D6) when no
    candidate matches. -/
def findDepRoot? (depProofs : List (String × ClauseProof)) (name : String)
    (formula : SExpr) : Option ClauseNode :=
  depProofs.findSome? fun (n, c) =>
    if n != name then none else
    match c.root with
    | some r => if r.inputClause == [formula] then some r else none
    | none => none

/-- The dependency theorem's replayed statement at `envV` — by APPLYING its D1 registry
    constant at the consumer's own telescope fvars when registered, else by
    replaying the dependency inside the shared telescope. Shared by
    `dischargeRuleHyp` and `dischargeCongHyp` (verbatim extraction, G2
    rung 2 — plus the `cong:` condition arm).

    WP5: an entry the CROSS-BOOK pre-pass produced (a dependency book's
    tree replayed at THIS world) may keep conditions chosen by the
    dependency book's own telescope — the consumer need not offer them.
    Those mapping failures are FRONTIERS (the hypothesis stays visible,
    D6); for a SAME-BOOK entry the consumer telescope does offer every
    condition the dependency could keep, so a miss stays an internal
    defect. -/
def depReplayedProofAt (cfg : ReplayConfig) (ctx : ReplayCtx) (name : String)
    (depRoot : ClauseNode) (envV : Expr) (ctxD : ReplayCtx)
    (replayed : ReplayedRegistry) : MetaM Expr := do
  let formula := disjoinTerm depRoot.inputClause
  match findReplayedEntry replayed name formula with
  | some entry => do
    let decl := entry.decl
    -- fail-closed severity: cross-book entries frontier, same-book ones
    -- surface as defects (see the docstring)
    let miss : MessageData → MetaM Expr := fun m =>
      if entry.crossBook then throwFrontier m else throwError m
    let condArgs ← entry.conds.toArray.mapM fun c => do
      if c.startsWith "total:" then
        let fn := (c.drop "total:".length).toString
        let some h := ctx.totalHyps.lookup fn
          | miss m!"depReplayedProofAt: registry dependency \
              {name} keeps {c}, absent from the consumer telescope"
        pure h
      else if c.startsWith "tp:" then
        let fn := (c.drop "tp:".length).toString
        let some (_, _, h) := ctx.tpHyps.find? (fun (nm, _, _) => nm == fn)
          | miss m!"depReplayedProofAt: registry dependency \
              {name} keeps {c}, absent from the consumer telescope"
        pure h
      else if c.startsWith "rule:" then
        let rn := (c.drop "rule:".length).toString
        match ctx.ruleHyps.filter (fun (r, _) => r.runeKey == rn) with
        | [(_, h)] => pure h
        | [] => miss m!"depReplayedProofAt: registry dependency \
            {name} keeps {c}, absent from the consumer telescope"
        | _ => miss m!"depReplayedProofAt: registry dependency \
            {name} keeps {c} but the consumer telescope offers \
            several same-named rules (ambiguous — refuse rather than \
            guess)"
      else if c.startsWith "linear:" then
        let rn := (c.drop "linear:".length).toString
        match ctx.linearHyps.filter (fun (r, _) => r.name == rn) with
        | [(_, h)] => pure h
        | _ => miss m!"depReplayedProofAt: registry dependency \
            {name} keeps {c}, absent or ambiguous in the consumer telescope"
      else if c.startsWith "cong:" then
        let cn := (c.drop "cong:".length).toString
        match ctx.congHyps.filter (fun (s, _) => s.name == cn) with
        | [(_, h)] => pure h
        | _ => miss m!"depReplayedProofAt: registry dependency \
            {name} keeps {c}, absent or ambiguous in the consumer telescope"
      else if c.startsWith "use:" then
        -- a dependency replayed with a KEPT use: condition (R7a): the
        -- consumer's telescope offers it only when the same name is cited
        -- in the consumer's own tree — otherwise refuse (frontier at the
        -- registry application, kept honest by the discharge pass)
        let un := (c.drop "use:".length).toString
        match ctx.useHyps.filter (fun (u, _) => u.name == un) with
        | [(_, h)] => pure h
        | _ => miss m!"depReplayedProofAt: registry dependency \
            {name} keeps {c}, absent or ambiguous in the consumer telescope"
      else if c.startsWith "equivfull:" then
        let en := (c.drop "equivfull:".length).toString
        match ctx.equivFullHyps.filter (fun (e, _) => e.name == en) with
        | [(_, h)] => pure h
        | _ => miss m!"depReplayedProofAt: registry dependency \
            {name} keeps {c}, absent or ambiguous in the consumer telescope"
      else if c.startsWith "equivrefl:" then
        -- LATENT DEFECT (P3a, fixed WP5): the arm was MISSING, so a
        -- dependency keeping its equivalence rule's reflexivity component
        -- fell through to the untagged catch-all below and ABORTED the
        -- consumer's replay instead of keeping the hypothesis.
        let en := (c.drop "equivrefl:".length).toString
        match ctx.equivReflHyps.filter (fun (s, _) => s.name == en) with
        | [(_, h)] => pure h
        | _ => miss m!"depReplayedProofAt: registry dependency \
            {name} keeps {c}, absent or ambiguous in the consumer telescope"
      else if c.startsWith "tpthm:" then
        let tn := (c.drop "tpthm:".length).toString
        match ctx.tpThmHyps.filter (fun (s, _) => s.name == tn) with
        | [(_, h)] => pure h
        | _ => miss m!"depReplayedProofAt: registry dependency \
            {name} keeps {c}, absent or ambiguous in the consumer telescope"
      else miss m!"depReplayedProofAt: registry dependency \
          {name} keeps unrecognized condition {c}"
    pure (mkAppN (mkConst decl) (#[envV] ++ condArgs))
  | none =>
    try replayClause { cfg with envExpr := envV } ctxD depRoot
    catch e => throwFrontier m!"depReplayedProofAt: dependency {name}'s \
        replay failed (frontier): {e.toMessageData}"

/-- DISCHARGE a `rule:<thm>` hypothesis from its dependency theorem's replayed
    statement (v1 step 5, docs/plans/2026-07-05_theorem-dependency-hypotheses.md):
    obtain the dependency's replayed statement — by APPLYING its D1 registry constant at
    the consumer's own telescope fvars (same world, identical hypothesis
    statements) when registered, else by replaying the dependency INSIDE the
    same hypothesis telescope (`ctx` — its own conditions stay as the shared
    fvars, so transitive conditions compose) — then DECODE the replayed statement to the
    stored-rule statement. The decode recomputes ACL2's create-rewrite-rule
    normalization between two EMITTED artifacts — the defthm formula (the
    dependency's Goal clause) and the stored rule — and hard-fails on any
    mismatch: strip `implies`, flatten the `and`-antecedent (must equal the
    rule's :HYPS), then either the equality conclusion IS (equal lhs rhs), or
    the boolean-strengthened form (conclusion = lhs, rhs = 'T) pinned by the
    head fn's EMITTED :TYPE-PRESCRIPTION. All value-level: MP on
    `Logic.implies`, two-valued `Logic.equal` decode, TP boolean pin.

    DEPENDENCY SELECTION is RECOMPUTE-BASED (WP5, P3a latent defect 3): the
    candidate set is EVERY tree named `spec.name` (`depProofs` carries
    same-book AND cross-book entries, and the corpus really does hold two
    distinct `TRUE-LISTP-RM` theorems), filtered to those whose translated
    Goal recomputes to THIS stored rule. Zero survivors, or survivors
    disagreeing on the formula, is a frontier — never a first-match
    guess. -/
def dischargeRuleHyp (cfg : ReplayConfig) (ctx : ReplayCtx) (spec : RuleSpec)
    (depProofs : List (String × ClauseProof))
    (replayed : ReplayedRegistry := []) : MetaM Expr := do
  -- the create-rewrite-rule normalization, RECOMPUTED from a candidate's
  -- translated Goal and CHECKED against the stored rule
  let eqForm : SExpr := .cons (.atom (.symbol { name := "EQUAL" }))
    (.cons spec.lhs (.cons spec.rhs .nil))
  -- USER-equivalence rule (G2 rung 2): the stored rule's faithful statement
  -- is the interpreted relation — its defthm conclusion must BE the
  -- R-application `(R lhs rhs)`; the hypothesis body is then that term's
  -- truthiness directly (no equality decode).
  let relForm : SExpr := .cons
    (.atom (.symbol { name := spec.equiv.map Char.toUpper }))
    (.cons spec.lhs (.cons spec.rhs .nil))
  -- NEGATIVE boolean strengthening (P3, ORDEREDP-MEMB's shape): a defthm
  -- conclusion `(NOT lhs)` stores as `lhs = 'NIL` — the truthy NOT pins
  -- the lhs VALUE to exactly nil (Logic.not is nil-dichotomous; no TP
  -- needed, unlike the positive route's exact-t pin)
  let notForm : SExpr := .cons (.atom (.symbol { name := "NOT" }))
    (.cons spec.lhs .nil)
  -- IFF-CONCLUSION rule (the DECODE class, P5a): ACL2's
  -- `create-rewrite-rule` stores an `(IFF lhs rhs)` defthm conclusion as an
  -- `:EQUIV EQUAL` rewrite rule when both sides are boolean. Recomputing
  -- that normalization needs the same fact ACL2 used — the TWO-VALUEDNESS
  -- of both sides — which is why the decode below DEMANDS the emitted
  -- `:TYPE-PRESCRIPTION` disjunctions rather than assuming them.
  let iffForm : SExpr := .cons (.atom (.symbol { name := "IFF" }))
    (.cons spec.lhs (.cons spec.rhs .nil))
  let quoteNilS : SExpr := .cons (.atom (.symbol { name := "QUOTE" }))
    (.cons .nil .nil)
  -- (concl, routeEqual, routeRel, routeNotBool, routeIff) of a candidate
  let route? : SExpr → Option (SExpr × Bool × Bool × Bool × Bool) := fun formula =>
    let (hypsF, concl) := match formula with
      | .cons (.atom (.symbol impS)) (.cons h (.cons c .nil)) =>
        if impS.name == "IMPLIES" then (flattenAnd h, c) else ([], formula)
      | _ => ([], formula)
    if hypsF != spec.hyps then none else
    let routeEqual := spec.equiv == "equal" && concl == eqForm
    let routeBool := spec.equiv == "equal" && concl == spec.lhs
      && spec.rhs == quoteT
    let routeRel := spec.equiv != "equal" && concl == relForm
    let routeNotBool := spec.equiv == "equal" && concl == notForm
      && spec.rhs == quoteNilS
    let routeIff := spec.equiv == "equal" && concl == iffForm
    if routeEqual || routeBool || routeRel || routeNotBool || routeIff then
      some (concl, routeEqual, routeRel, routeNotBool, routeIff)
    else none
  let cands := depProofs.filterMap fun (n, c) =>
    if n != spec.name then none else
    match c.root with
    | some r => match r.inputClause with
      | [f] => (route? f).map (fun rt => (c, r, f, rt))
      | _ => none
    | none => none
  let some (_cp, depRoot, formula,
            (concl, routeEqual, routeRel, routeNotBool, routeIff)) :=
      cands.head?
    | throwFrontier m!"dischargeRuleHyp: no dependency proof whose \
        single-literal Goal recomputes to the stored rule {spec.name} \
        (:HYPS {repr spec.hyps}; candidates \
        {(depProofs.filter (·.1 == spec.name)).length}) — frontier"
  unless cands.all (fun (_, _, f, _) => f == formula) do
    throwFrontier m!"dischargeRuleHyp: several DISTINCT dependency Goals \
        named {spec.name} recompute to the stored rule — refuse to guess \
        (frontier)"
  let w := cfg.worldExpr
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let cfgD := { cfg with envExpr := envV }
    let mut ctxD := { ctx with varVals := [], vals := [], litFacts := [], dedupDrops := [],
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
      let pDep ← depReplayedProofAt cfg ctx spec.name depRoot envV ctxDFixed replayed
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
        else if routeIff then do
          -- the IFF DECODE: the conclusion's value is `Logic.iff vL vR`,
          -- and a truthy iff of two TWO-VALUED values pins them equal.
          -- Two-valuedness comes from `boolDisj?` — the emitted
          -- `:TYPE-PRESCRIPTION` corollaries and the trusted core's own
          -- boolean lifts, structurally through IF-nests. No source, no
          -- decode: the hypothesis stays (D6), never a boolean assumption.
          let vC ← ctxValExpr cfgD ctxDFixed concl
          unless vC.isAppOfArity ``Logic.iff 2 do
            throwFrontier m!"dischargeRuleHyp: value of {repr concl} is \
                not (Logic.iff _ _) (frontier)"
          let some hL ← boolDisj? cfgD ctxDFixed spec.lhs
            | throwFrontier m!"dischargeRuleHyp: no two-valuedness source \
                for the iff-rule lhs {repr spec.lhs} — the IFF⇒EQUAL decode \
                needs it (frontier)"
          let some hR ← boolDisj? cfgD ctxDFixed spec.rhs
            | throwFrontier m!"dischargeRuleHyp: no two-valuedness source \
                for the iff-rule rhs {repr spec.rhs} — the IFF⇒EQUAL decode \
                needs it (frontier)"
          let hEq ← mkAppM ``eq_of_iff_ne_nil_two_valued #[hL, hR, hvC]
          mkAppM ``fuel_eq_of_conv
            #[← ctxValProof cfgD ctxDFixed spec.lhs,
              ← ctxValProof cfgD ctxDFixed spec.rhs, hEq]
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
    single-literal formula — recompute-and-checked, then the replayed statement applied
    at `env'`. -/
def dischargeCongHyp (cfg : ReplayConfig) (ctx : ReplayCtx) (spec : CongSpec)
    (depProofs : List (String × ClauseProof))
    (replayed : ReplayedRegistry := []) : MetaM Expr := do
  let formula := spec.formula
  let some depRoot := findDepRoot? depProofs spec.name formula
    | throwFrontier m!"dischargeCongHyp: no dependency proof for \
        {spec.name} with the offered congruence formula (frontier)"
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let cfgD := { cfg with envExpr := envV }
    let mut ctxD := { ctx with varVals := [], vals := [], litFacts := [], dedupDrops := [],
                               branchFacts := [], segFacts := [] }
    ctxD ← pinTermOpaques cfgD envV ctxD formula
    let pDep ← depReplayedProofAt cfg ctx spec.name depRoot envV ctxD replayed
    let pf ← mkLambdaFVars #[envV] pDep
    mkExpectedTypeHint pf (← mkCongHypType cfg spec)

/-- DISCHARGE an `equivfull:<thm>` hypothesis (the R-solidify lane):
    whole-formula from the dependency's replayed statement — the
    `dischargeCongHyp` shape; the offer's spec.formula IS the dep's Goal
    clause (same-source; the load-bearing shape check happened at offer
    time in `equivFullSpecOfGoal?`). -/
def dischargeEquivFullHyp (cfg : ReplayConfig) (ctx : ReplayCtx)
    (spec : EquivFullSpec) (depProofs : List (String × ClauseProof))
    (replayed : ReplayedRegistry := []) : MetaM Expr := do
  let formula := spec.formula
  let some depRoot := findDepRoot? depProofs spec.name formula
    | throwFrontier m!"dischargeEquivFullHyp: no dependency proof for \
        {spec.name} with the offered formula (frontier)"
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let cfgD := { cfg with envExpr := envV }
    let mut ctxD := { ctx with varVals := [], vals := [], litFacts := [], dedupDrops := [],
                               branchFacts := [], segFacts := [] }
    ctxD ← pinTermOpaques cfgD envV ctxD formula
    let pDep ← depReplayedProofAt cfg ctx spec.name depRoot envV ctxD replayed
    let pf ← mkLambdaFVars #[envV] pDep
    mkExpectedTypeHint pf (← mkEquivFullHypType cfg spec)

/-- DISCHARGE a `tpthm:<thm>` hypothesis (the first :CLASSES consumer):
    whole-formula from the dependency's replayed statement — the
    `dischargeCongHyp` shape (same-source formula assert). -/
def dischargeTpThmHyp (cfg : ReplayConfig) (ctx : ReplayCtx)
    (spec : TpThmSpec) (depProofs : List (String × ClauseProof))
    (replayed : ReplayedRegistry := []) : MetaM Expr := do
  let formula := spec.formula
  let some depRoot := findDepRoot? depProofs spec.name formula
    | throwFrontier m!"dischargeTpThmHyp: no dependency proof for \
        {spec.name} with the offered formula (frontier)"
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let cfgD := { cfg with envExpr := envV }
    let mut ctxD := { ctx with varVals := [], vals := [], litFacts := [], dedupDrops := [],
                               branchFacts := [], segFacts := [] }
    ctxD ← pinTermOpaques cfgD envV ctxD formula
    let pDep ← depReplayedProofAt cfg ctx spec.name depRoot envV ctxD replayed
    let pf ← mkLambdaFVars #[envV] pDep
    mkExpectedTypeHint pf (← mkTpThmHypType cfg spec)

/-- DISCHARGE a `use:<thm>` hypothesis from its dependency's replayed
    statement (R7a): identical to `dischargeCongHyp` — the hypothesis
    states the WHOLE formula and the dependency's Goal clause IS that
    single-literal formula, the replayed statement applied at `env'`. The formula
    equality below is a SAME-SOURCE consistency assert (offer and
    discharge read the same depProofs root — R7a audit F7), not an
    independent cross-check; the load-bearing check for `use:` is the
    verbatim σ/:HYPS comparison in the consuming arm. -/
def dischargeUseHyp (cfg : ReplayConfig) (ctx : ReplayCtx) (spec : UseSpec)
    (depProofs : List (String × ClauseProof))
    (replayed : ReplayedRegistry := []) : MetaM Expr := do
  let formula := spec.formula
  let some depRoot := findDepRoot? depProofs spec.name formula
    | throwFrontier m!"dischargeUseHyp: no dependency proof for \
        {spec.name} with the offered use formula (frontier)"
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let cfgD := { cfg with envExpr := envV }
    let mut ctxD := { ctx with varVals := [], vals := [], litFacts := [], dedupDrops := [],
                               branchFacts := [], segFacts := [] }
    ctxD ← pinTermOpaques cfgD envV ctxD formula
    let pDep ← depReplayedProofAt cfg ctx spec.name depRoot envV ctxD replayed
    let pf ← mkLambdaFVars #[envV] pDep
    mkExpectedTypeHint pf (← mkUseHypType cfg spec)

/-- DISCHARGE an `equivrefl:<thm>` hypothesis from its dependency's replayed
    statement (P3, the ORDERED-PERMS replayed statement): the dependency is the
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
    (replayed : ReplayedRegistry := []) : MetaM Expr := do
  let rxx : SExpr := .cons (.atom (.symbol spec.rel))
    (.cons (.atom (.symbol spec.vx)) (.cons (.atom (.symbol spec.vx)) .nil))
  let qNil : SExpr := .cons (.atom (.symbol { name := "QUOTE" }))
    (.cons .nil .nil)
  -- RECOMPUTE-BASED selection (WP5 defect 3): every tree named `spec.name`
  -- whose Goal IS the defequiv and-shape carrying the OFFERED reflexivity
  -- conjunct — not the first same-named entry of `depProofs`.
  let cands := depProofs.filterMap fun (n, c) =>
    if n != spec.name then none else
    match c.root with
    | some r => match r.inputClause with
      | [f@(.cons (.atom (.symbol if1)) (.cons c1
          (.cons (.cons (.atom (.symbol if2)) (.cons r2
            (.cons _rest (.cons e2 .nil)))) (.cons e1 .nil))))] =>
        if if1.isNamed "IF" && if2.isNamed "IF" && r2 == rxx
            && e1 == qNil && e2 == qNil then some (r, f, c1) else none
      | _ => none
    | none => none
  let some (depRoot, formula, c1) := cands.head?
    | throwFrontier m!"dischargeEquivReflHyp: no dependency proof named \
        {spec.name} whose Goal is the defequiv and-shape with the OFFERED \
        reflexivity conjunct {repr rxx} second (frontier)"
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let cfgD := { cfg with envExpr := envV }
    let mut ctxD := { ctx with varVals := [], vals := [], litFacts := [], dedupDrops := [],
                               branchFacts := [], segFacts := [] }
    ctxD ← pinTermOpaques cfgD envV ctxD formula
    let pDep ← depReplayedProofAt cfg ctx spec.name depRoot envV ctxD replayed
    let conv1 ← ctxValProof cfgD ctxD c1
    let hne1 ← mkAppM ``evtrue_and_left #[conv1, pDep]
    let htb1 ← mkAppM ``toBool_true_of_ne_nil #[hne1]
    let hRight ← mkAppM ``evtrue_and_right #[conv1, htb1, pDep]
    let convR ← ctxValProof cfgD ctxD rxx
    let hneR ← mkAppM ``evtrue_and_left #[convR, hRight]
    let body ← mkAppM ``evtrue_of_conv_ne_nil #[convR, hneR]
    let pf ← mkLambdaFVars #[envV] body
    mkExpectedTypeHint pf (← mkEquivReflHypType cfg spec)

/-- DISCHARGE a `linear:<rune>` hypothesis from its defthm's replayed
    statement (WP5 item 4). ACL2 stores a `:LINEAR` rule as
    `(hyps ⊢ (< a b))` — a `<`-conclusion, i.e. exactly the R-route shape
    `dischargeRuleHyp` already decodes: no equality decode, the hypothesis
    body IS the conclusion term's truthiness.

    The decode is a RECOMPUTE between two EMITTED artifacts — the defthm's
    translated Goal and the `(:GROUND-ZERO-LINEAR-RULES …)` snapshot entry
    (`hyps`/`concl` verbatim; `maxTerm` is instantiation metadata, not
    content, and is deliberately not consulted). Strip `implies`, flatten
    the `and`-antecedent (must equal the stored `:HYPS`), and the
    conclusion must be the stored one VERBATIM. Any divergence keeps the
    hypothesis (D6). Dependency selection is recompute-based, like
    `dischargeRuleHyp`'s. -/
def dischargeLinearHyp (cfg : ReplayConfig) (ctx : ReplayCtx)
    (spec : LinearRuleSpec) (depProofs : List (String × ClauseProof))
    (replayed : ReplayedRegistry := []) : MetaM Expr := do
  let route? : SExpr → Bool := fun formula =>
    let (hypsF, concl) := match formula with
      | .cons (.atom (.symbol impS)) (.cons h (.cons c .nil)) =>
        if impS.name == "IMPLIES" then (flattenAnd h, c) else ([], formula)
      | _ => ([], formula)
    hypsF == spec.hyps && concl == spec.concl
  let cands := depProofs.filterMap fun (n, c) =>
    if n != spec.name then none else
    match c.root with
    | some r => match r.inputClause with
      | [f] => if route? f then some (r, f) else none
      | _ => none
    | none => none
  let some (depRoot, formula) := cands.head?
    | throwFrontier m!"dischargeLinearHyp: no dependency proof whose \
        single-literal Goal recomputes to the stored :LINEAR rule \
        {spec.name} (:HYPS {repr spec.hyps}, concl {repr spec.concl}) — \
        frontier"
  unless cands.all (fun (_, f) => f == formula) do
    throwFrontier m!"dischargeLinearHyp: several DISTINCT dependency Goals \
        named {spec.name} recompute to the stored :LINEAR rule — refuse to \
        guess (frontier)"
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let cfgD := { cfg with envExpr := envV }
    let mut ctxD := { ctx with varVals := [], vals := [], litFacts := [], dedupDrops := [],
                               branchFacts := [], segFacts := [] }
    ctxD ← pinTermOpaques cfgD envV ctxD formula
    let premDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      (spec.hyps.zipIdx.map fun (h, i) =>
        (Name.mkSimple s!"h{i}", BinderInfo.default,
         fun (_ : Array Expr) => do
           pure (← mkAppM ``EvTrue
             #[cfg.worldExpr, envV, reflectSExpr h]))).toArray
    let ctxDFixed := ctxD
    withLocalDecls premDecls fun premVs => do
      let pDep ← depReplayedProofAt cfg ctx spec.name depRoot envV ctxDFixed
        replayed
      let convF ← ctxValProof cfgD ctxDFixed formula
      let hFne ← mkAppM ``ne_nil_of_evtrue_conv #[pDep, convF]
      let hvC ←
        if spec.hyps.isEmpty then pure hFne
        else do
          let hvHs ← (spec.hyps.zipIdx.toArray.mapM fun (h, i) => do
            let convH ← ctxValProof cfgD ctxDFixed h
            mkAppM ``ne_nil_of_evtrue_conv #[premVs[i]!, convH])
          let rec andNe (hs : List Expr) : MetaM Expr := do
            match hs with
            | [] => throwError "dischargeLinearHyp: internal — no hyps"
            | [h1] => pure h1
            | h1 :: rest => mkAppM ``and_value_ne_nil #[h1, ← andNe rest]
          let hvH ← andNe hvHs.toList
          mkAppM ``implies_value_mp #[hFne, hvH]
      let body ← mkAppM ``evtrue_of_conv_ne_nil
        #[← ctxValProof cfgD ctxDFixed spec.concl, hvC]
      let pf ← mkLambdaFVars (#[envV] ++ premVs) body
      mkExpectedTypeHint pf (← mkLinearHypType cfg spec)

/-- D5 GROUND-ZERO `:LINEAR` registry (T1+2 sprint P5a): the boot-stored
    `:LINEAR` rules admitted for prelude discharge. A ground-zero `:LINEAR`
    rule has NO defthm anywhere in the corpus, so `dischargeLinearHyp`'s
    recompute-from-the-dependency route can never reach it — the
    `d5GzRules` situation for the rewrite runes, under the same D5
    admission criterion (class (i): no replayable evidence in ANY
    capturable image).

    A NAME list, not a name↦constant table: the discharge is by the
    DEFINITIONAL-BRANCH class lemma (`gz_linear_defn_branch`), whose
    instance is RECOMPUTED per rule from the cited fn's own emitted body
    — nothing here is rule-specific. The list is the reviewable record of
    WHICH gz rules may be discharged without replayable evidence; a rule
    outside it keeps its honest condition.

    LIVE-GATED BY THE GOLDEN (the J-P4b-c precedent, same reasoning): the
    `sorting/msort` row `ACL2-COUNT-EVENS-STRONG` is unconditional ONLY
    because this discharge fires, so an emission drift or a broken class
    check turns that row conditional and the golden diff shows it —
    a stronger check than a static pin, and one that costs no extra log
    parse. (Honest-mistake standard — do not harden it.) -/
def d5GzLinearRules : List String :=
  -- `((CONSP X)) ⊢ (EQUAL (ACL2-COUNT X) (BINARY-+ '1 (BINARY-+
  --  (ACL2-COUNT (CAR X)) (ACL2-COUNT (CDR X)))))` — verbatim the
  -- CONSP branch of ACL2-COUNT's own `:SOURCE :GROUND-ZERO` `:DEFUN`
  -- body, which is what the class check below re-derives.
  ["ACL2-COUNT-CAR-CDR-LINEAR"]

/-- DISCHARGE a GROUND-ZERO `linear:<rune>` hypothesis by the
    DEFINITIONAL-BRANCH class (D5, the gz-linear family): the stored rule's
    conclusion must BE `(EQUAL (fn x) rhs)` where `rhs` is the branch of
    `fn`'s OWN world body selected by the rule's single hypothesis as
    ruling test.

    Everything is RECOMPUTED between two emitted artifacts — the `:DEFUN`
    body in the world and the `(:GROUND-ZERO-LINEAR-RULES …)` snapshot
    entry: `substTerm [formal] [x] body` is computed here, its `(IF test
    rhs els)` shape read off, and `test`/`rhs` compared against the
    emitted `:HYPS`/conclusion. Any divergence is a FRONTIER (the
    hypothesis stays, D6), never a guess; the class lemma is then
    instantiated and the result type-hinted against `mkLinearHypType`, so
    a drifted emission fails at the kernel. -/
def dischargeGzLinearHyp (cfg : ReplayConfig) (ctx : ReplayCtx)
    (spec : LinearRuleSpec) : MetaM Expr := do
  -- the emitted conclusion must be an EQUAL of a 1-ary call on a VARIABLE
  let .cons (.atom (.symbol eqS)) (.cons lhsT (.cons rhsT .nil)) := spec.concl
    | throwFrontier m!"dischargeGzLinearHyp: {spec.name}'s conclusion \
        {repr spec.concl} is not an application (frontier)"
  unless eqS.name == "EQUAL" do
    throwFrontier m!"dischargeGzLinearHyp: {spec.name}'s conclusion head is \
        {eqS.name}, not EQUAL (frontier)"
  let .cons (.atom (.symbol fnS)) (.cons (.atom (.symbol xvS)) .nil) := lhsT
    | throwFrontier m!"dischargeGzLinearHyp: {spec.name}'s conclusion lhs \
        {repr lhsT} is not a 1-ary call on a variable (frontier)"
  let [hypT] := spec.hyps
    | throwFrontier m!"dischargeGzLinearHyp: {spec.name} has \
        {spec.hyps.length} hypotheses; the definitional-branch class takes \
        exactly one ruling test (frontier)"
  let some (formals, body) := cfg.worldVal.defs.get? fnS
    | throwFrontier m!"dischargeGzLinearHyp: {fnS.name} is not defined in \
        the world (frontier)"
  let [formal] := formals
    | throwFrontier m!"dischargeGzLinearHyp: {fnS.name} has arity \
        {formals.length}, not 1 (frontier)"
  -- RECOMPUTE: the fn's own body at the rule's variable, and its branch shape
  let xTerm : SExpr := .atom (.symbol xvS)
  let inst := substTerm [formal] [xTerm] body
  let .cons (.atom (.symbol ifS)) (.cons testT (.cons thenT (.cons elseT .nil))) :=
      inst
    | throwFrontier m!"dischargeGzLinearHyp: {fnS.name}'s body at the rule's \
        variable is not an IF ({repr inst}) — outside the \
        definitional-branch class (frontier)"
  unless ifS.isNamed "IF" do
    throwFrontier m!"dischargeGzLinearHyp: {fnS.name}'s body head is \
        {ifS.name}, not IF (frontier)"
  unless testT == hypT do
    throwFrontier m!"dischargeGzLinearHyp: {spec.name}'s hypothesis \
        {repr hypT} is not {fnS.name}'s own ruling test {repr testT} \
        (frontier)"
  unless thenT == rhsT do
    throwFrontier m!"dischargeGzLinearHyp: {spec.name}'s conclusion rhs \
        {repr rhsT} is not {fnS.name}'s own then-branch {repr thenT} \
        (frontier)"
  let some htot := ctx.totalHyps.lookup fnS.name
    | throwFrontier m!"dischargeGzLinearHyp: no totality hypothesis for \
        {fnS.name} in the telescope (frontier)"
  let info ← deriveDefInfoN cfg fnS
  let hns ← proveNotSpecial fnS
  let hxvT ← proveByDecide
    (← mkEq (mkApp2 (mkConst ``Symbol.isNamed) (reflectSymbol xvS)
      (mkStrLit "T")) (mkConst ``Bool.false)) "rule variable is not T"
  let hsubst ← proveByDecide
    (← mkEq (← mkAppM ``ACL2.Replay.substTerm
      #[← mkListLit (mkConst ``Symbol) [reflectSymbol formal],
        ← mkListLit (mkConst ``SExpr) [reflectSExpr xTerm],
        reflectSExpr body])
      (reflectSExpr inst)) s!"{fnS.name} body branch"
  let hnoEq ← proveNoShadow cfg { name := "EQUAL" }
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let cfgD := { cfg with envExpr := envV }
    let mut ctxD := { ctx with varVals := [], vals := [], litFacts := [], dedupDrops := [],
                               branchFacts := [], segFacts := [] }
    ctxD ← pinTermOpaques cfgD envV ctxD spec.concl
    ctxD ← pinTermOpaques cfgD envV ctxD hypT
    let ctxDFixed := ctxD
    let premDecl : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      #[(`h0, BinderInfo.default, fun _ => do
          pure (← mkAppM ``EvTrue
            #[cfg.worldExpr, envV, reflectSExpr hypT]))]
    withLocalDecls premDecl fun premVs => do
      let htest ← ctxValProof cfgD ctxDFixed testT
      let hrhs ← ctxValProof cfgD ctxDFixed rhsT
      let inst ← mkAppM ``gz_linear_defn_branch
        #[cfg.worldExpr, envV, reflectSymbol fnS, reflectSymbol formal,
          reflectSymbol xvS, reflectSExpr info.body, reflectSExpr testT,
          reflectSExpr rhsT, reflectSExpr elseT,
          ← ctxValExpr cfgD ctxDFixed testT, ← ctxValExpr cfgD ctxDFixed rhsT,
          hns, info.defFact, info.closedFact, info.wellScopedFact, hxvT,
          hsubst, hnoEq, htot, htest, hrhs, premVs[0]!]
      let pf ← mkLambdaFVars (#[envV] ++ premVs) inst
      mkExpectedTypeHint pf (← mkLinearHypType cfg spec)

/-- The CONDITIONAL generic replayed statement: bind the machine-generated hypothesis
    telescope (per defined fn: totality; plus the lifted TP corollary when one was
    emitted), replay the theorem under it, and λ-abstract. Returns the proof and
    the condition descriptions (the c2 pattern — obligations explicit in the
    type, discharged later by termination emission / Driver Stage 5). -/
def replayProofConditional (cfg : ReplayConfig) (tps : List (String × SExpr))
    (cp : ClauseProof) (justs : List (String × Justification) := [])
    (rules : List RuleSpec := []) (depProofs : List (String × ClauseProof) := [])
    (replayed : ReplayedRegistry := [])
    (equivRefls : List (String × SExpr) := [])
    (termReplayed : List (String × Name × List String × List SExpr) := [])
    (congTrees : Option (List (String × ClauseProof)) := none)
    (discharge : Bool := true)
    (usefiDischarge : Option (ReplayCtx → UseFiSpec → MetaM Expr) := none) :
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
  -- whole-formula replayed statement (`mkCongHypType`); non-matching formulas are not
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
  -- Pre-merge audit fix N8 (2026-08-06): if cp.name is absent from
  -- useSameBook, takeWhile returns the WHOLE list and the topological
  -- guard admits everything — fail closed instead (offer nothing; the
  -- arm then hard-fails honestly in-walk).
  let useEarlier :=
    if useSameBook.any (fun (n, _) => n == cp.name) then
      (useSameBook.takeWhile (fun (n, _) => n != cp.name)).map (·.1)
    else []
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
  -- usefi:<thm> offers (R7b, Phase 3 2a): one per FUNCTIONAL-INSTANCE
  -- citation in THIS theorem's tree. The offered formula is RECOMPUTED —
  -- `substFnCalls` of the dependency's translated Goal under the emitted
  -- lambdas — and must equal the emitted `:HYPS` instance VERBATIM (a
  -- divergence means mis-emission or a substitution-semantics bug: the
  -- offer is not made, and the arm hard-fails honestly in-walk). No
  -- discharge pass yet: a consumed offer stays a KEPT condition (D6) —
  -- the (a1) alias-world composition is the tracked 2c follow-up.
  let useFiSpecs : List UseFiSpec :=
    (theoremFnInstanceCites cp).filterMap fun (n, σ, hypI) =>
      match (depProofs.lookup n).bind (·.root) with
      | some root =>
        match root.inputClause with
        | [f] =>
          if substFnCalls σ f == hypI then
            some { name := n, subst := σ, formula := hypI }
          else none
        | _ => none
      | none => none
  let useFiDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (useFiSpecs.zipIdx.map fun (u, i) =>
      (Name.mkSimple s!"husefi_{u.name}_{i}", BinderInfo.default,
       fun (_ : Array Expr) =>
         mkUseHypType cfg { name := u.name, formula := u.formula })).toArray
  -- equivrefl:<thm> declarations (sorting-completion-2 Class A): every
  -- equivalence-SHAPED defthm formula in scope (incl. INCLUDE-BOOK'd —
  -- passed by the caller) offers its REFLEXIVITY component; include-book
  -- instances have no dependency replayed statement and stay KEPT (D6-honest).
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
  -- tpthm:<thm> offers (the FIRST :CLASSES consumer, tpthm sub-arc;
  -- RESURRECTED at the final close-out — killed at 910785a for lacking a
  -- green consumer, now reachable): per dependency theorem whose emitted
  -- :CLASSES names :TYPE-PRESCRIPTION (bare keyword or a class-list
  -- member), the whole-formula statement. Rare class (one per
  -- hand-classed TP theorem); consumed by replayRecognizer's cited-rune
  -- fallback, unused offers dropped. Topological guard (tpthm audit F5,
  -- mirroring useSpecs): no self-offer, and a SAME-BOOK entry must be
  -- strictly earlier — ACL2 cannot cite a not-yet-admitted rule, and the
  -- cited-rune anchor alone rests on untrusted fork emission (BUG-023).
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
      -- SELF-GATE (restructure-arc audit, convergent DEFECT 1 — verified
      -- by the outside reviewer's guard experiment): the snapshot is the
      -- END-OF-BOOK final world, so a theorem's own :LINEAR rule would be
      -- offered to its own replay — a hypothesis that IS the theorem
      -- (the tpthm/use gates' missing sibling; ACL2 cannot cite a
      -- not-yet-admitted rule). The experiment showed the self-premise
      -- was never load-bearing: the row proves without it, stronger.
      if r.name == cp.name then acc
      else if acc.any (fun (q : LinearRuleSpec) =>
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
    dpStmts.map (fun _ => assumedDpFactCond) ++
    useFiSpecs.map (fun u => s!"usefi:{u.name}")
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
      -- usefi binders LAST: their discharge (the prepared-constant
      -- application) references arbitrary earlier telescope fvars, and
      -- letBindFVar requires every value fvar to PRECEDE the bound one
      withLocalDecls useFiDecls fun useFiVs => do
      let tpVs := tpAllVs.extract 0 tpDecls.size
      let tpAvVs := tpAllVs.extract tpDecls.size tpAllVs.size
      let ctx : ReplayCtx :=
        { totalHyps := (fns.map (fun (s, _, _) => s.name)).zip totalVs.toList,
          tpHyps := (tpFns.zip tpVs.toList).map fun ((s, _, cor), h) => (s.name, cor, h),
          tpHypsAv := (tpFnsAv.zip tpAvVs.toList).map fun ((s, _, cor), h) => (s.name, cor, h),
          ruleHyps := rules.zip ruleVs.toList,
          congHyps := congs.zip congVs.toList,
          useHyps := useSpecs.zip useVs.toList,
          useFiHyps := useFiSpecs.zip useFiVs.toList,
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
      -- LATENT DEFECT 2 (P3a, fixed WP5): `containsFVar` reads the
      -- expression AS GIVEN — an fvar reachable only through an unassigned
      -- metavariable's assignment is INVISIBLE to it, so a pass could skip
      -- a hypothesis the proof really does use (and, symmetrically, `kept`
      -- could under-report). Every occurrence test below goes through this
      -- helper, which instantiates first.
      let usesFVar (e : Expr) (v : Expr) : MetaM Bool := do
        pure ((← instantiateMVars e).containsFVar v.fvarId!)
      -- ONE discharge attempt: run `mk` under a fresh heartbeat window and
      -- let-bind the result (every use site shares one copy); a TAGGED
      -- frontier-class failure keeps the hypothesis (D6, like totality),
      -- anything else is a real defect and is re-thrown (typed tag, not
      -- message prefix — fail-closed audit N1).
      let attempt (prf0 : Expr) (hypV : Expr) (mk : MetaM Expr) :
          MetaM Expr := do
        if !(← usesFVar prf0 hypV) then pure prf0 else
        try
          let pf ← withRealMaxHeartbeats dischargeBudget mk
          letBindFVar prf0 hypV pf
        catch e =>
          unless isFrontierErr e do
            throw e
          pure prf0
      let dischargeCongs (prf0 : Expr) : MetaM Expr := do
        let mut prfC := prf0
        for (spec, hypV) in (congs.zip congVs.toList).reverse do
          if discharge then
            prfC ← attempt prfC hypV (dischargeCongHyp cfg ctx spec depProofs
              replayed)
        pure prfC
      -- ONE SWEEP of every dependency-hypothesis pass, in the order the
      -- lane's topology needs (see the per-pass notes below).
      let dischargeSweep (prf0 : Expr) : MetaM Expr := do
        let mut prfR := prf0
        -- use:<thm> discharge (R7a) FIRST: a use discharge re-replays the
        -- cited theorem's whole tree, which can consume rule:/cong:/
        -- equivrefl:/total:/tp: fvars — all caught by the passes below.
        -- PARAMETRIC mode (Phase 2 item c): `discharge := false` keeps
        -- EVERY used hypothesis — over an abstract world the dischargers'
        -- kernel decisions cannot run, and the kept telescope IS the
        -- parametric statement's premise inventory (ScopeHolds').
        for (spec, hypV) in (useSpecs.zip useVs.toList).reverse do
          if discharge then
            prfR ← attempt prfR hypV (dischargeUseHyp cfg ctx spec depProofs
              replayed)
        -- usefi:<thm> discharge (R7b 2c): the CALLER-provided composition —
        -- parametric rebuild of the cited theorem at the alias world built
        -- from the emitted lambdas, crossed to this world by the FnAlias
        -- transports. Injected as a callback because the composition needs
        -- Runner-layer channel builders (layering); a frontier failure
        -- keeps the hypothesis (D6), and callers passing none (all
        -- pre-2c call sites) keep usefi: conds verbatim.
        if let some dfi := usefiDischarge then
          for (spec, hypV) in (useFiSpecs.zip useFiVs.toList).reverse do
            if discharge then
              prfR ← attempt prfR hypV (dfi ctx spec)
        prfR ← dischargeCongs prfR
        -- tpthm:<thm> discharge (the first :CLASSES consumer):
        -- whole-formula shape, same pass discipline.
        for (spec, hypV) in (tpThmSpecs.zip tpThmVs.toList).reverse do
          prfR ← attempt prfR hypV (dischargeTpThmHyp cfg ctx spec depProofs
            replayed)
        -- equivfull:<thm> discharge (the R-solidify lane): whole-formula
        -- from the dependency's replayed statement; BEFORE the rule pass
        -- (its re-replay can consume rule:/cong:/total:/tp: fvars, all
        -- caught below). Frontier failures keep the hypothesis (D6).
        for (spec, hypV) in (equivFullSpecs.zip equivFullVs.toList).reverse do
          if discharge then
            prfR ← attempt prfR hypV (dischargeEquivFullHyp cfg ctx spec
              depProofs replayed)
        -- equivrefl:<thm> discharge (P3, the ORDERED-PERMS replayed
        -- statement): projected from the dependency's replayed statement;
        -- BEFORE the rule pass — the dependency's replay can consume
        -- rule:/cong: fvars, caught by the passes below.
        for (spec, hypV) in (equivSpecs.zip equivVs.toList).reverse do
          if discharge then
            prfR ← attempt prfR hypV (dischargeEquivReflHyp cfg ctx spec
              depProofs replayed)
        -- linear:<rune> discharge (WP5 item 4): the stored :LINEAR rule's
        -- `<`-conclusion decoded from its defthm's replayed statement —
        -- or, for a GROUND-ZERO rule with no defthm anywhere in the
        -- corpus (P5a), its D5 definitional-branch class discharge.
        for (spec, hypV) in (linearSpecs.zip linearVs.toList).reverse do
          if discharge then
            prfR ← attempt prfR hypV <|
              if d5GzLinearRules.contains spec.name then
                dischargeGzLinearHyp cfg ctx spec
              else dischargeLinearHyp cfg ctx spec depProofs replayed
        for (spec, hypV) in (rules.zip ruleVs.toList).reverse do
          if discharge then
            prfR ← attempt prfR hypV <|
              -- a GROUND-ZERO rule has no dependency theorem to replay
              -- (boot-admitted, proofs skipped): its D5 prelude constant
              -- discharges it instead
              match d5GzRules.lookup spec.name with
              | some (decl, nsFn) => dischargeGzRuleHyp cfg spec decl nsFn
              | none => dischargeRuleHyp cfg ctx spec depProofs replayed
        prfR ← dischargeCongs prfR
        pure prfR
      -- SWEEP TO QUIESCENCE (WP5 item 3). One pass is not a fixed point:
      -- a discharge introduces the DEPENDENCY's own hypothesis uses, and
      -- with the cross-book transfer those can land on classes an EARLIER
      -- pass already walked. Iterate while a condition actually retires,
      -- with a hard cap; no progress (or the cap) stops. Termination is
      -- structural anyway — every iteration strictly shrinks the free-fvar
      -- set or stops — the cap is the honest-mistake speedbump against a
      -- discharger that re-introduces what it retired. Do not harden it.
      let hypVsAll := (totalVs ++ tpAllVs ++ ruleVs ++ congVs ++ useVs
        ++ equivVs ++ equivFullVs ++ tpThmVs ++ linearVs ++ dpVs
        ++ useFiVs).toList
      let freeCount (e : Expr) : MetaM Nat := do
        let ei ← instantiateMVars e
        pure (hypVsAll.filter (fun v => ei.containsFVar v.fvarId!)).length
      let mut sweepIters : Nat := 0
      let mut before ← freeCount prfR
      let mut sweeping := true
      while sweeping do
        prfR ← dischargeSweep prfR
        sweepIters := sweepIters + 1
        let after ← freeCount prfR
        if after >= before || sweepIters >= 4 then
          sweeping := false
        else
          before := after
      let prf ← instantiateMVars prfR
      -- bind only the hypotheses the replay ACTUALLY USED: an unconsumed offer must
      -- not weaken the statement (hypothesis types are mutually independent, so
      -- dropping unused ones is well-formed).
      let used := (condsAll.zip (totalVs ++ tpAllVs ++ ruleVs ++ congVs ++ useVs ++ equivVs ++ equivFullVs ++ tpThmVs ++ linearVs ++ dpVs ++ useFiVs).toList).filter
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
      let neededFns := if discharge then usedTotalNames ++ usedTpNames else []
      let hypFVarsAll := condsAll.zip ((totalVs ++ tpAllVs ++ ruleVs ++ congVs ++ useVs ++ equivVs ++ equivFullVs ++ tpThmVs ++ linearVs ++ dpVs ++ useFiVs).toList)
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
      -- ONE hypothesis's discharge, shared by the `used` pass and the
      -- SECOND pass below (extracted 2026-08-14 — the two were about to be
      -- byte-identical copies).
      let dischargeTotalOrTp (prf0 : Expr) (c : String) (v : Expr) :
          MetaM Expr := do
        if c.startsWith "total:" then
          match totalEnv.find? (fun (n, _, _) => s!"total:{n}" == c) with
          | some (_, _, pf) => letBindFVar prf0 v pf
          | none => pure prf0
        else if c.startsWith "tp:" then
          -- the TP prover: derive the emitted-corollary hypothesis from the
          -- fn's body (lifter sprint 2026-07-06); frontier → keep (D6).
          -- ARGS-VALUED tp hypotheses (G1) go to the SAME prover in its
          -- args-valued mode (TP-replay arc increment 5, 2026-08-13) —
          -- the corollary's bare-formal occurrences lift to the argument
          -- values, exactly as `mkTpHypTypeAv` states them; a frontier
          -- there keeps the hypothesis as before.
          let fnName := (c.drop "tp:".length).toString
          let isAv := tpFnsAv.any (fun (s, _, _) => s.name == fnName)
          if tpFns.any (fun (s, _, _) => s.name == fnName) || isAv then
            match tps.lookup fnName with
            | some cor =>
              try
                -- the RECORDED-TERMINATION bundle, assembled exactly as
                -- `buildTotalEnv` assembles it for `proveTotality` (T1+2
                -- sprint P5b): with it, the TP induction runs over the
                -- INTERPRETED count and a self-call with an OPAQUE measured
                -- actual (`QSORT`'s `(FILTER 'GTE (CDR X) (CAR X))`) takes
                -- the replayed admission's own decrease. A failed assembly
                -- is a frontier there and simply leaves `recTerm? = none`,
                -- i.e. the destructor route's pre-existing behaviour.
                let recTerm? ←
                  match termReplayed.find? (fun (n, _, _, _) => n == fnName),
                        justs.lookup fnName with
                  | some (_, dc, dconds, dgoal), some just =>
                    try
                      pure (some (← mkRecTermInfo cfg totalEnv hypFVarsAll
                        tps just dc dconds dgoal))
                    catch e =>
                      unless isFrontierErr e do throw e
                      pure none
                  | _, _ => pure none
                let pf ← proveTp cfg totalEnv justs fnName cor
                  (cors := tps) (argValued := isAv) (recTerm? := recTerm?)
                let pf ← mkExpectedTypeHint pf (← inferType v)
                letBindFVar prf0 v pf
              catch e =>
                unless isFrontierErr e do
                  throw e
                -- DIAGNOSTIC SINK (T1+2 sprint P4b). A kept `tp:` condition
                -- discards its frontier message here, so the reason a row
                -- stays conditional was invisible to every binary — the
                -- 2026-08-13 fork-emission audit and this sprint's own
                -- scouting both stalled on exactly that. Off unless
                -- `ACL2LEAN_TP_DIAG` is set; stderr only, never a result
                -- line, so no output any gate reads can change.
                if (← IO.getEnv "ACL2LEAN_TP_DIAG").isSome then
                  IO.eprintln s!"[tp-diag] {fnName}: \
                    {← e.toMessageData.toString}"
                pure prf0
            | none => pure prf0
          else pure prf0
        else pure prf0
      for (c, v) in (if discharge then used else []) do
        prf ← dischargeTotalOrTp prf c v
      -- SECOND total:/tp: PASS (T1+2 sprint phase 1, 2026-08-14). The pass
      -- above iterates `used` — the hypotheses the REPLAY ITSELF touched.
      -- A RECORDED-TERMINATION totality proof can pull in FURTHER
      -- total:/tp: fvars (PERM-QSORT's `tp:ACL2-COUNT` arrives exactly that
      -- way, via the admission waterfall's own ACL2-COUNT uses), and those
      -- were surfaced as kept conditions without ever being ATTEMPTED. Same
      -- discharge, same fail-closed type hint; a frontier still keeps the
      -- hypothesis. `tp:` runs first, so a `total:` fvar a TP proof pulls in
      -- is still caught by the second sub-pass.
      if discharge then
        let usedNames := used.map (·.1)
        let mut prfMid ← instantiateMVars prf
        for (c, v) in hypFVarsAll do
          if c.startsWith "tp:" && !usedNames.contains c
              && prfMid.containsFVar v.fvarId! then
            prf ← dischargeTotalOrTp prf c v
        prfMid ← instantiateMVars prf
        for (c, v) in hypFVarsAll do
          if c.startsWith "total:" && !usedNames.contains c
              && prfMid.containsFVar v.fvarId! then
            prf ← dischargeTotalOrTp prf c v
      -- SECOND ground-zero pass (close-out 2026-08-08): the totality/TP
      -- discharge proofs above may pull in gz-rule hyp fvars the replay
      -- itself never touched — they enter AFTER the rule-discharge pass,
      -- so the D5 registry never saw them. Registry-covered rules are
      -- dischargeable without a dependency tree; bind them here rather
      -- than surfacing a prelude-constant fact as a kept condition.
      -- NOT GENERALIZED to the DEPENDENCY dischargers (T1+2 sprint P5a,
      -- item 2 — measured, not adopted). The same fvars arrive here for
      -- `rule:`/`linear:` too: a RECORDED-ADMISSION totality proof
      -- carries the admission's own kept conditions onto this telescope
      -- (`buildTotalEnv`'s hypFVars mapping) after the sweep has run, so
      -- `rule:TRUE-LISTP-BNEXT` / `linear:HOW-MANY-BAD-PAIRS-BNEXT` at
      -- BSORT-IS-ISORT are kept without an attempt ever being made. A
      -- dependency-discharger pass here (with the cross-book seed widened
      -- so the registry entries exist) was BUILT AND MEASURED at
      -- `sorting/sorts-equivalent`: it discharges both — and re-introduces
      -- the dependency's own `total:BNEXT` + `total:BNEXT-SIZE` +
      -- `tp:BNEXT-SIZE`, which arrive AFTER the totality/TP passes. Two
      -- conditions out, three in, so it was reverted under the movement
      -- rule. Closing it needs those passes run to QUIESCENCE (with
      -- `totalEnv` rebuilt for the newly-freed names), not one more pass.
      if discharge then
        let prfMid ← instantiateMVars prf
        for (spec, hypV) in rules.zip ruleVs.toList do
          if prfMid.containsFVar hypV.fvarId! then
            if let some (decl, nsFns) := d5GzRules.lookup spec.name then
              try
                let pf ← withRealMaxHeartbeats dischargeBudget <|
                  dischargeGzRuleHyp cfg spec decl nsFns
                prf ← letBindFVar prf hypV pf
              catch e =>
                unless isFrontierErr e do
                  throw e
      -- kept = the hypotheses STILL FREE in the final proof. Recomputed
      -- AFTER all discharges (sorting arc 2026-07-28): a recorded-
      -- termination totality proof may pull in tp:/rule: fvars the replay
      -- itself never touched — they surface here as honest conditions.
      let prfF ← instantiateMVars prf
      let kept := hypFVarsAll.filter (fun (_, v) => prfF.containsFVar v.fvarId!)
      let p ← mkLambdaFVars (kept.map (·.2)).toArray prfF
      -- FI SELF-VACUITY marker (audit 2026-08-09, outside D1 — verified by
      -- an `rfl` probe on BSORT-IS-ISORT): a KEPT usefi hypothesis whose
      -- formula IS the row's goal makes the conditional row `P → P`. Tag
      -- it with the reserved marker; the runner's ASSUMED choke point
      -- renders such rows ◌ and refuses registration (the
      -- assumedDpFactCond doctrine's second instance). Discharged usefi
      -- hypotheses are substituted away above and never reach `kept`.
      let selfVacuous := kept.any fun (c, _) =>
        c.startsWith "usefi:" && useFiSpecs.any fun u =>
          s!"usefi:{u.name}" == c &&
          (match cp.root with
           | some root => root.inputClause == [u.formula]
           | none => false)
      let conds := kept.map (·.1) ++
        (if selfVacuous then [assumedFiSelfCond] else [])
      return (p, conds)


/-- The PARAMETRIC replay (Phase 2 item c — the R6 scope abstraction,
    docs/notes/2026-08-02_r6-encapsulate-design.md §3/§5): replay a recorded
    tree over an ABSTRACT `w : World` instead of the canonical model. The
    binder inventory is generated uniformly from the canonical model:

    - a definition-pinning hypothesis `w.defs.get? fn = some (formals, body)`
      OFFERED for every canonical-model defun EXCEPT `sigFns` (the scope's
      signature fns AND witness defuns — the caller derives the set from
      the emitted scope surface; audit 2026-08-08 inside F1);
    - a no-shadow hypothesis `w.defs.get? b = none` for every `builtinNames`
      entry (the canonical model never shadows a builtin — `toWorld` skips
      them — so these pins hold there by construction);
    - the ordinary conditional telescope, with `discharge := false`: every
      used hypothesis is KEPT, so the scope's constraint theorems surface
      as `rule:` premises in ACL2's STORED-RULE form (which can be
      strictly stronger than the bare truthy constraint over an abstract
      w — see `parametric_replayed%`'s doc) and the sig fns' totality/TP
      facts as `total:`/`tp:` premises.

    A scope-local fn deliberately gets NO definition pin: an unfold demand
    on it inside the replay hard-fails (`deriveDefInfo` finds neither
    hypothesis nor decidable world), which IS the witness-dereference
    guard (design item 5) — a post-encapsulate tree that dereferences a
    witness is a reconstruction bug, not a frontier. Only USED pins are
    bound in the final statement (the used-filter discipline: an
    unconsumed offer must not weaken the statement; a tree that never
    unfolds keeps NO pins — both equisort capstones keep zero). Returns
    the proof `∀ w, (used pins…) → (used no-shadows…) → (kept telescope…)
    → EvTrue w env Φ` — `env` is the CALLER's binder, OUTSIDE `w` in the
    final constant (semantically inert: no premise mentions it) — and the
    premise descriptions (`def:`/`noshadow:` + the telescope's). -/
def replayProofParametric (cfg0 : ReplayConfig) (sigFns : List Symbol)
    (tps : List (String × SExpr)) (cp : ClauseProof)
    (justs : List (String × Justification) := [])
    (rules : List RuleSpec := [])
    (depProofs : List (String × ClauseProof) := [])
    (equivRefls : List (String × SExpr) := [])
    (congTrees : Option (List (String × ClauseProof)) := none) :
    MetaM (Expr × List String) := do
  withLocalDeclD `w (mkConst ``ACL2.World) fun wE => do
    let mkGet := fun (s : Symbol) => do
      mkAppM ``ACL2.DefMap.get? #[← mkAppM ``ACL2.World.defs #[wE], reflectSymbol s]
    let pins := cfg0.worldVal.defs.entries.filter fun (s, _, _) => !sigFns.contains s
    let pinDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      (pins.map fun (s, formals, body) =>
        (Name.mkSimple s!"hdef_{s.name}", BinderInfo.default,
         fun (_ : Array Expr) => do
           -- EXACTLY the fact shape deriveDefInfo/deriveDefInfoN state (the
           -- hypothesis is consumed verbatim as `defFact`)
           let formalsE ← mkListLit (mkConst ``Symbol) (formals.map reflectSymbol)
           let someE ← mkAppM ``Option.some
             #[← mkAppM ``Prod.mk #[formalsE, reflectSExpr body]]
           mkEq (← mkGet s) someE)).toArray
    let shadowSyms := ACL2.builtinNames.map fun n => ({ name := n } : Symbol)
    let shadowDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      (shadowSyms.map fun s =>
        (Name.mkSimple s!"hnoshadow_{s.name}", BinderInfo.default,
         fun (_ : Array Expr) => do
           let lookup ← mkGet s
           let elemTy := (← inferType lookup).appArg!
           mkEq lookup (mkApp (mkConst ``Option.none [0]) elemTy))).toArray
    withLocalDecls pinDecls fun pinVs => do
    withLocalDecls shadowDecls fun shadowVs => do
      let cfg := { cfg0 with
        worldExpr := wE,
        defFactHyps := (pins.map (·.1)).zip pinVs.toList,
        noShadowHyps := shadowSyms.zip shadowVs.toList }
      let (prf, conds) ← replayProofConditional cfg tps cp justs rules
        depProofs [] equivRefls [] (congTrees := congTrees)
        (discharge := false)
      let prfI ← instantiateMVars prf
      let pinKept := (pins.zip pinVs.toList).filter
        fun (_, v) => prfI.containsFVar v.fvarId!
      let shadowKept := (shadowSyms.zip shadowVs.toList).filter
        fun (_, v) => prfI.containsFVar v.fvarId!
      let p ← mkLambdaFVars
        (#[wE] ++ (pinKept.map (·.2)).toArray ++ (shadowKept.map (·.2)).toArray) prfI
      return (p,
        pinKept.map (fun ((s, _, _), _) => s!"def:{s.name}")
        ++ shadowKept.map (fun (s, _) => s!"noshadow:{s.name}")
        ++ conds)


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
