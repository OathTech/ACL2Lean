import ACL2Lean.Replay.Driver.Core
import ACL2Lean.Replay.Driver.TpProver
import ACL2Lean.Replay.Driver.DevQuery

/-! Source-tree selection and discharge, extracted from Harness so the
conditional telescope can grow an explicit ordinary FC channel. -/
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
      else if c.startsWith "fc:" then
        let rn := (c.drop "fc:".length).toString
        match ctx.fcHyps.filter (fun (r, _) => r.name == rn) with
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
    let mut ctxD := ctx.clearEnvFacts
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
    let mut ctxD := ctx.clearEnvFacts
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
    let mut ctxD := ctx.clearEnvFacts
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
    let mut ctxD := ctx.clearEnvFacts
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
    let mut ctxD := ctx.clearEnvFacts
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
    let mut ctxD := ctx.clearEnvFacts
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

/-- Project a stored LINEAR or FC implication from its named defthm's
replayed statement. The two emitted artifacts must agree: strip IMPLIES,
flatten the AND antecedent, and compare every hypothesis and the conclusion
verbatim. Instantiation metadata belongs to the consuming rule class.
The premise proofs decode the antecedent; the dependency supplies the
implication. Divergence leaves the explicit dependency frontier. -/
def dischargeStoredImplication (cfg : ReplayConfig) (ctx : ReplayCtx)
    (label ruleClass name : String) (hyps : List SExpr) (conclusion : SExpr)
    (depProofs : List (String × ClauseProof)) (replayed : ReplayedRegistry := []) : MetaM Expr := do
  let route? : SExpr → Bool := fun formula =>
    let (hypsF, concl) := match formula with
      | .cons (.atom (.symbol impS)) (.cons h (.cons c .nil)) =>
        if impS.name == "IMPLIES" then (flattenAnd h, c) else ([], formula)
      | _ => ([], formula)
    hypsF == hyps && concl == conclusion
  let cands := depProofs.filterMap fun (n, c) =>
    if n != name then none else
    match c.root with
    | some r => match r.inputClause with
      | [f] => if route? f then some (r, f) else none
      | _ => none
    | none => none
  let some (depRoot, formula) := cands.head?
    | throwFrontier m!"{label}: no dependency proof whose \
        single-literal Goal recomputes to the stored {ruleClass} rule \
        {name} (:HYPS {repr hyps}, concl {repr conclusion}) — \
        frontier"
  unless cands.all (fun (_, f) => f == formula) do
    throwFrontier m!"{label}: several DISTINCT dependency Goals \
        named {name} recompute to the stored {ruleClass} rule — refuse to \
        guess (frontier)"
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let cfgD := { cfg with envExpr := envV }
    let mut ctxD := ctx.clearEnvFacts
    ctxD ← pinTermOpaques cfgD envV ctxD formula
    let premDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      (hyps.zipIdx.map fun (h, i) =>
        (Name.mkSimple s!"h{i}", BinderInfo.default,
         fun (_ : Array Expr) => do
           pure (← mkAppM ``EvTrue
             #[cfg.worldExpr, envV, reflectSExpr h]))).toArray
    let ctxDFixed := ctxD
    withLocalDecls premDecls fun premVs => do
      let pDep ← depReplayedProofAt cfg ctx name depRoot envV ctxDFixed
        replayed
      let convF ← ctxValProof cfgD ctxDFixed formula
      let hFne ← mkAppM ``ne_nil_of_evtrue_conv #[pDep, convF]
      let hvC ←
        if hyps.isEmpty then pure hFne
        else do
          let hvHs ← (hyps.zipIdx.toArray.mapM fun (h, i) => do
            let convH ← ctxValProof cfgD ctxDFixed h
            mkAppM ``ne_nil_of_evtrue_conv #[premVs[i]!, convH])
          let rec andNe (hs : List Expr) : MetaM Expr := do
            match hs with
            | [] => throwError "stored implication: internal — no hyps"
            | [h1] => pure h1
            | h1 :: rest => mkAppM ``and_value_ne_nil #[h1, ← andNe rest]
          let hvH ← andNe hvHs.toList
          mkAppM ``implies_value_mp #[hFne, hvH]
      let body ← mkAppM ``evtrue_of_conv_ne_nil
        #[← ctxValProof cfgD ctxDFixed conclusion, hvC]
      let pf ← mkLambdaFVars (#[envV] ++ premVs) body
      mkExpectedTypeHint pf (← mkStoredImplicationType cfg hyps conclusion)

def dischargeLinearHyp (cfg : ReplayConfig) (ctx : ReplayCtx)
    (spec : LinearRuleSpec) (depProofs : List (String × ClauseProof))
    (replayed : ReplayedRegistry := []) : MetaM Expr :=
  dischargeStoredImplication cfg ctx "dischargeLinearHyp" ":LINEAR"
    spec.name spec.hyps spec.concl depProofs replayed

/-- Decode an ordinary stored FC implication from its named source tree.
No ground-zero fallback or invented rule-class record is involved. -/
def dischargeFcHyp (cfg : ReplayConfig) (ctx : ReplayCtx)
    (spec : FcRuleSpec) (depProofs : List (String × ClauseProof))
    (replayed : ReplayedRegistry := []) : MetaM Expr := do
  let [concl] := spec.concls | throwFrontier m!"dischargeFcHyp: multiple conclusions"
  dischargeStoredImplication cfg ctx "dischargeFcHyp" ":FORWARD-CHAINING"
    spec.name spec.hyps concl depProofs replayed

end ACL2.Replay.Driver
