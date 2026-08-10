/-
  Driver/Preprocess — split from the monolithic Driver.lean (WP2 Stage 1,
  2026-07-17; see docs/plans/2026-07-18_driver-modular-refactor.md).

  Preprocess-chain replay and the clausify bridge (#53C).
-/
import ACL2Lean.Replay.Driver.Totality
import ACL2Lean.Replay.ClausifyBridgeCons

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-! ## Preprocess-chain replay (a clause discharged at PREPROCESS, formula → 't)

ACL2's preprocess (`final-implies/eval`, `preprocess/eval`, abbreviation
expansion, const-fold, equal-self) logs clause-level `:REWRITE-STEP`s with NO
`:PATH` — preprocess has no rewriter gstack. Each step's position is therefore
reconstructed DETERMINISTICALLY: the node's lhs must occur EXACTLY ONCE in the
current term; zero or multiple occurrences hard-fail (nothing is guessed — the
same inverse-discipline standard as clause-id lineage). -/

/-- All occurrences of `lhs` in `cur`, as congruence path-step descents.
    Quoted subterms are opaque (no descent). -/
partial def findOccurrences (cur lhs : SExpr) : List (List PathStep) :=
  let here : List (List PathStep) := if cur == lhs then [[]] else []
  let inside : List (List PathStep) :=
    match asApp cur with
    | some (fn, args) =>
      if fn.name == "QUOTE" then []
      else
        (args.zipIdx).flatMap fun (a, i) =>
          (findOccurrences a lhs).map fun p =>
            ({ fn, arity := args.length, argIdx := i,
               siblings := (args.zipIdx).filterMap fun (b, j) =>
                 if j == i then none else some b } : PathStep) :: p
    | none =>
      -- a translated `let` (S2b): descend into the ACTUALS with lamHead
      -- congruence steps (audit F8 — a pathless preprocess step whose redex
      -- sits in a lambda actual was reported "does not occur"). The BODY has
      -- no body-congruence PathStep (a rewrite inside an unopened body is
      -- the boundary-frame case), but it IS counted: a body occurrence
      -- POISONS uniqueness (re-audit F3 — a redex occurring in the body AND
      -- an actual read as a false unique and was silently lifted at the
      -- actual). The sentinel [] path is never liftable — a poisoned result
      -- either becomes count ≠ 1 (ambiguity hard-fail) or a [] path whose
      -- terminal redex check cannot match the whole term.
      match asLamApp cur with
      | some (head, lam, args) =>
        let inActuals := (args.zipIdx).flatMap fun (a, i) =>
          (findOccurrences a lhs).map fun p =>
            ({ fn := lam, arity := args.length, argIdx := i,
               siblings := (args.zipIdx).filterMap fun (b, j) =>
                 if j == i then none else some b,
               lamHead := some head } : PathStep) :: p
        let inBody :=
          match asLamHead head with
          | some (_, _, lamBody) =>
            (findOccurrences lamBody lhs).map fun _ => ([] : List PathStep)
          | none => []
        inActuals ++ inBody
      | none => []
  here ++ inside

/-- Replay one PREPROCESS node to its eval-equality `∃N∀f≥N, eval lhs = eval rhs`.
    `executable-counterpart` steps are GROUND computations: ACL2 ran the
    executable counterpart; the kernel re-checks the SAME computation by
    reduction of `evalOpt` at a sufficient concrete fuel (found by running the
    evaluator), lifted by fuel monotonicity. Other runes use their ordinary
    node recipes. -/
def replayPreprocessNode (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode) :
    MetaM Expr := do
  let rty := (runeOf n).ty
  let (lhs, rhs) := nodeLhsRhs n
  let .node _ _ _ _ prov := n
  -- a non-EQUAL preprocess rule application must route through the
  -- R-parameterized judgment (the if-iff shape is handled by the chain core;
  -- anything else is the G1 frontier)
  unless prov.equiv == "equal" || prov.origin == "preprocess/if-iff" do
    throwError "replayPreprocessNode: step under equivalence {prov.equiv} — \
                R-parameterized recipe pending (G1 frontier)"
  -- a verdict-only DISCHARGE node routes through the chain core's IFF lane
  -- (D10): its honest content is `EvTrue lhs`, an SIff step to 't — NOT an
  -- eval-equality (that strengthening held only for boolean-valued clauses)
  if dischargeOrigins.contains prov.origin then
    throwError "replayPreprocessNode: discharge node {prov.origin} must \
                compose via the chain core's SIff lane (D10) — direct \
                eval-equality replay is gone"
  match rty with
  | "executable-counterpart" =>
    let .cons (.atom (.symbol q)) (.cons v .nil) := rhs
      | throwError "executable-counterpart: rhs {repr rhs} is not a quoted constant"
    unless q.name == "QUOTE" do
      throwError "executable-counterpart: rhs {repr rhs} is not a quoted constant"
    let convLhs ← replayExecGround cfg lhs v
    let hq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr v]
    mkAppM ``fuel_eq_of_conv #[convLhs, hq, ← mkEqRefl (reflectSExpr v)]
  | "equal-self" =>
    let some X := asEqualSelf lhs
      | throwError "preprocess equal-self: lhs is not (equal X X): {repr lhs}"
    unless rhs == quoteT do
      throwError "preprocess equal-self: rhs {repr rhs} ≠ (quote t)"
    let hX ← proveConv cfg cfg.envExpr ctx X
    let hNoEqual ← proveNoShadow cfg { name := "EQUAL" }
    let closeProof ← mkAppM ``re_equal_self
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr X, hX, hNoEqual]
    let hq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
    mkAppM ``fuel_eq_of_conv #[closeProof, hq, ← mkEqRefl (reflectSExpr SExpr.t)]
  | _ => replayNode cfg ctx n

/-- The `PREPROCESS/IF-IFF` node: `(if A 't 'nil) ⇒ A` — IFF-only, NOT
    value-preserving (the chain runs under `*geneqv-iff*`). Returns
    `EvRel SIff w env lhs rhs`. -/
def replayIfIffNode (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode) :
    MetaM Expr := do
  let (lhs, rhs) := nodeLhsRhs n
  let expectedLhs : SExpr :=
    .cons (.atom (.symbol { name := "IF" }))
      (.cons rhs (.cons quoteT (.cons quoteNil .nil)))
  unless lhs == expectedLhs do
    throwError "preprocess/if-iff: lhs {repr lhs} is not (if rhs 't 'nil)"
  let vA ← ctxValExpr cfg ctx rhs
  let pA ← ctxValProof cfg ctx rhs
  mkAppM ``evrel_siff_if_t_nil
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr rhs, vA, pA]

/-! `applyStepSIff` — the one-step R congruence table — moved to
    `NodeCore.lean` (G1 rung 1, inc-2): the literal-chain walker
    (`replayRewritesWith`) lifts or-shape SIff payloads with it, and
    NodeCore is upstream of this module. -/

/-- The EQUIVALENCE-RUNE own-position congruence (the R-solidify lane,
    close-out Phase 3): `v(R …a…) = v(R …a'…)` where the parent
    application is the relation R ITSELF and the rewrite replaces the
    argument at `argIdx` (0-based) by an R-equivalent term (`hR : EvTrue
    env (R a a')`). ACL2's license is the :EQUIVALENCE rune — geneqv
    treats an equivalence rule as a congruence at its own argument
    positions, citing NO defcong — and the kernel content is the defequiv
    conjuncts, all value-level: conjunct 1 (booleanp) pins both parent
    applications two-valued (`booleanp_truthy_cases`); conjunct 3 (sym)
    turns `hR` around; conjunct 4 (trans) gives each direction of the
    mutual truthiness; `boolean_biimpl_eq` closes to the value equality.
    Every instantiation rides `instantiateEvTrueHypAt` on the offered
    whole-formula statement; the conjunct shapes were recompute-checked at
    offer time (`equivFullSpecOfGoal?`). -/
def equivOwnPosCongr (cfg : ReplayConfig) (ctx : ReplayCtx)
    (spec : EquivFullSpec) (hypV : Expr) (a a' other : SExpr)
    (argIdx : Nat) (hR : Expr) : MetaM (Expr × ReplayCtx) := do
  unless argIdx == 0 || argIdx == 1 do
    throwError "equivOwnPosCongr: arg index {argIdx} out of range for the \
                binary relation {spec.rel.name}"
  let rApp (p q : SExpr) : SExpr :=
    .cons (.atom (.symbol spec.rel)) (.cons p (.cons q .nil))
  let (parentL, parentR) :=
    if argIdx == 0 then (rApp a other, rApp a' other)
    else (rApp other a, rApp other a')
  let mut ctx := ctx
  for t in [a, a', other, parentL, parentR, rApp a a', rApp a' a] do
    ctx ← pinTermOpaques cfg cfg.envExpr ctx t
  -- project conjunct k (1-4) of an instantiated defequiv conjunction
  -- (IF c1 (IF c2 (IF c3 c4 'NIL) 'NIL) 'NIL) to its value-truthiness
  let project (ctx0 : ReplayCtx) (instF : SExpr) (inst : Expr) (k : Nat) :
      MetaM (Expr × ReplayCtx) := do
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx0 instF
    let mut cur := instF
    let mut curP := inst
    for _ in [0:(k - 1)] do
      let .cons _ (.cons c (.cons b _)) := cur
        | throwError "equivOwnPosCongr: conjunction shape mismatch at \
                      {repr cur} (internal — offer-time shape check missed)"
      let convC ← ctxValProof cfg ctx c
      let hne ← mkAppM ``evtrue_and_left #[convC, curP]
      let htb ← mkAppM ``toBool_true_of_ne_nil #[hne]
      curP ← mkAppM ``evtrue_and_right #[convC, htb, curP]
      cur := b
    if k == 4 then
      -- after three descents `cur` IS conjunct 4 and `curP` its EvTrue
      pure (← mkAppM ``ne_nil_of_evtrue_conv
        #[curP, ← ctxValProof cfg ctx cur], ctx)
    else
      let .cons _ (.cons c _) := cur
        | throwError "equivOwnPosCongr: conjunction shape mismatch at \
                      {repr cur} (internal)"
      pure (← mkAppM ``evtrue_and_left #[← ctxValProof cfg ctx c, curP], ctx)
  let instProject (ctx0 : ReplayCtx) (tx ty tz : SExpr) (k : Nat) :
      MetaM (Expr × ReplayCtx) := do
    let σv := [spec.vx, spec.vy, spec.vz]
    let σt := [tx, ty, tz]
    let (h, ctx1) ← instantiateEvTrueHypAt cfg ctx0 hypV σv σt spec.formula
    project ctx1 (ACL2.Replay.substTerm σv σt spec.formula) h k
  -- v(R a a') ≠ nil from hR
  let hRne ← mkAppM ``ne_nil_of_evtrue_conv
    #[hR, ← ctxValProof cfg ctx (rApp a a')]
  -- sym: conjunct 3 at (a, a') gives v(R a' a) ≠ nil
  let (hSymImp, ctx1) ← instProject ctx a a' other 3
  let hSymNe ← mkAppM ``implies_value_mp #[hSymImp, hRne]
  -- booleanp pins for both parent applications (conjunct 1)
  let (pL, qL) := if argIdx == 0 then (a, other) else (other, a)
  let (pR, qR) := if argIdx == 0 then (a', other) else (other, a')
  let (hbL, ctx2) ← instProject ctx1 pL qL other 1
  let (hbR, ctx3) ← instProject ctx2 pR qR other 1
  let pinL ← mkAppM ``booleanp_truthy_cases #[hbL]
  let pinR ← mkAppM ``booleanp_truthy_cases #[hbR]
  -- forward / backward truthiness implications via conjunct 4 (trans)
  let vParentL ← ctxValExpr cfg ctx3 parentL
  let vParentR ← ctxValExpr cfg ctx3 parentR
  -- λ (h : assumedV ≠ nil), implies_value_mp trans₄ (and …) — one direction
  -- of the mutual truthiness; `firstIsAssumed` orders the and-antecedent
  let mkDir (ctx0 : ReplayCtx) (assumedV : Expr)
      (txyz : SExpr × SExpr × SExpr) (hFirst : Expr)
      (firstIsAssumed : Bool) : MetaM (Expr × ReplayCtx) := do
    let (tx, ty, tz) := txyz
    let (hTrans, ctxN) ← instProject ctx0 tx ty tz 4
    let neTy ← mkAppM ``Ne #[assumedV, mkConst ``SExpr.nil]
    let lam ← withLocalDeclD `hass neTy fun hAss => do
      let hAnt ←
        if firstIsAssumed then mkAppM ``and_value_ne_nil #[hAss, hFirst]
        else mkAppM ``and_value_ne_nil #[hFirst, hAss]
      mkLambdaFVars #[hAss] (← mkAppM ``implies_value_mp #[hTrans, hAnt])
    pure (lam, ctxN)
  let (hFwd, hBwd, ctxF) ←
    if argIdx == 0 then do
      -- fwd: trans (a', a, other): (R a' a) ∧ (R a other) → (R a' other)
      let (f, ctxA) ← mkDir ctx3 vParentL (a', a, other) hSymNe false
      -- bwd: trans (a, a', other): (R a a') ∧ (R a' other) → (R a other)
      let (b, ctxB) ← mkDir ctxA vParentR (a, a', other) hRne false
      pure (f, b, ctxB)
    else do
      -- fwd: trans (other, a, a'): (R other a) ∧ (R a a') → (R other a')
      let (f, ctxA) ← mkDir ctx3 vParentL (other, a, a') hRne true
      -- bwd: trans (other, a', a): (R other a') ∧ (R a' a) → (R other a)
      let (b, ctxB) ← mkDir ctxA vParentR (other, a', a) hSymNe true
      pure (f, b, ctxB)
  let valueEq ← mkAppM ``boolean_biimpl_eq #[pinL, pinR, hFwd, hBwd]
  pure (valueEq, ctxF)

/-- The R-COLLAPSE step (G2 rung 2): a preprocess rewrite under a USER
    equivalence R (`:EQUIV perm` — qsort's ORDEREDP-QSORT applying
    PERM-QSORT at ALL-REL's arg 2). The R-payload lives for exactly ONE
    frame: the emitted :PATH's innermost frame is the congruence position,
    where the replayed defcong mirror converts it to an eval-EQUALITY of the
    parent applications — everything outward lifts as ordinary equality.
    Mechanism, all value-level and premise-free:
    - the stored R-rule's hypothesis (the interpreted-relation shape,
      `mkRuleHypType`) instantiated by the emitted :SUBST gives
      `EvTrue env (R lhsσ rhsσ)`;
    - the matching `cong:` hypothesis (indexed by fn/pos/R, exactly one)
      instantiated at the parent application's args gives
      `EvTrue env (IMPLIES (R lhsσ rhsσ) (EQUAL parentL parentR))`;
    - value-level MP + the two-valued EQUAL decode give
      `v(parentL) = v(parentR)`.
    Hyp-bearing R-rules and ambiguous congruence matches are loud
    frontiers. Returns the parent-level fuel-eq. -/
def replayCongCollapse (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode)
    (parentStep : PathStep) (citedCongs : List String)
    (citedEquivs : List String := []) : MetaM Expr := do
  let (lhs, rhs) := nodeLhsRhs n
  let .node _ _ _ children prov := n
  let rune := runeOf n
  unless prov.origin == "abbreviation-expansion" do
    throwError "replayCongCollapse: origin {prov.origin} under equivalence \
        {prov.equiv} (frontier — abbreviation-expansion only)"
  unless children.isEmpty do
    throwError "replayCongCollapse: rule {rune.name} step has \
        {children.length} children (frontier — hyp-free abbreviations only)"
  let σvars ← prov.subst.mapM fun (v, _) => do
    let .atom (.symbol s) := v
      | throwError "replayCongCollapse: :SUBST binds a non-variable {repr v}"
    pure s
  let σterms := prov.subst.map (·.2)
  let candidates := ctx.ruleHyps.filter fun (r, _) =>
    r.name == rune.name && r.idx == rune.idx && r.equiv == prov.equiv
  if candidates.isEmpty then
    throwError "replayCongCollapse: rule {rune.name} (equiv {prov.equiv}): no \
        stored-rule hypothesis in scope (no (:RULES …) entry — emission gap \
        or missing telescope)"
  let matched := candidates.filter fun (r, _) =>
    ACL2.Replay.substTerm σvars σterms r.lhs == lhs
  let (spec, hypV) ← match matched with
    | [m] => pure m
    | m :: restM =>
      if restM.all (fun (r, _) => r == m.1) then pure m
      else throwError "replayCongCollapse: rule {rune.name}: \
          {matched.length} DISTINCT stored rules match (need exactly 1)"
    | [] => throwError "replayCongCollapse: rule {rune.name}: 0 stored rules \
        match substTerm(:SUBST, lhs) == {repr lhs}"
  unless spec.hyps.isEmpty do
    throwError "replayCongCollapse: rule {rune.name} carries \
        {spec.hyps.length} hyps (frontier — hyp-free R-rules only)"
  unless ACL2.Replay.substTerm σvars σterms spec.rhs == rhs do
    throwError "replayCongCollapse: rule {rune.name}: node rhs {repr rhs} ≠ \
        substTerm(:SUBST, rule rhs {repr spec.rhs}) (emission gap)"
  let ruleFrees := ACL2.Replay.freeVars spec.lhs ++ ACL2.Replay.freeVars spec.rhs
  for s in ruleFrees do
    unless σvars.contains s do
      throwError "replayCongCollapse: rule {rune.name}: rule variable \
          {s.name} not bound by the emitted :SUBST (emission gap)"
  -- the interpreted-relation instance: EvTrue env (R lhsσ rhsσ)
  let rSym : Symbol := { name := spec.equiv.map Char.toUpper }
  let relApp : SExpr := .cons (.atom (.symbol rSym))
    (.cons spec.lhs (.cons spec.rhs .nil))
  let relAppσ := ACL2.Replay.substTerm σvars σterms relApp
  let (hRel, ctx1) ← instantiateEvTrueHypAt cfg ctx hypV σvars σterms relApp
  -- the congruence: indexed at (fn, pos, R) AND anchored to the EMITTED
  -- citation (pre-merge audit 2026-07-30, both auditors converged): the
  -- processor-level :RUNES name the licensing rule ((:CONGRUENCE <name>)),
  -- so the shape-index alone would be an INFERENCE — a congruence-shaped
  -- earlier theorem ACL2 never used as the license could match (BUG-023).
  -- The matched spec's name must be step-cited; exactly one must survive.
  let congMatches := ctx1.congHyps.filter fun (c, _) =>
    c.fn == parentStep.fn && c.pos == parentStep.argIdx && c.rel == rSym &&
    citedCongs.contains c.name
  if congMatches.isEmpty && parentStep.fn == rSym then
    -- EQUIVALENCE-RUNE own-position license (the R-solidify lane, Phase 3):
    -- the parent application is R ITSELF — no defcong exists for R's own
    -- argument positions; ACL2's geneqv built-in makes the :EQUIVALENCE
    -- rule the congruence there and the step cites the equivalence rune.
    -- Anchored exactly as BUG-023 demands: the matched equivfull spec must
    -- be STEP-CITED (citedEquivs), never shape-matched alone.
    let eqMatches := ctx1.equivFullHyps.filter fun (e, _) =>
      e.rel == rSym && citedEquivs.contains e.name
    let [(eSpec, eHyp)] := eqMatches
      | throwError "replayCongCollapse: own-position rewrite under \
          {rSym.name} at arg {parentStep.argIdx}: {eqMatches.length} \
          step-cited equivfull hypotheses (need exactly 1; cited \
          equivalence runes {citedEquivs}) (frontier)"
    let parentL := rebuild parentStep lhs
    let parentR := rebuild parentStep rhs
    let some pArgs := (match parentL with
        | .cons _ argsS => argsS.toList?
        | _ => none)
      | throwError "replayCongCollapse: parent {repr parentL} is not an \
          application"
    let [arg0, arg1] := pArgs
      | throwError "replayCongCollapse: own-position parent {repr parentL} \
          is not a binary application (frontier)"
    unless pArgs[parentStep.argIdx]? == some lhs do
      throwError "replayCongCollapse: the parent's arg at the rewrite \
          position is not the node lhs (internal)"
    let other := if parentStep.argIdx == 0 then arg1 else arg0
    let (valueEq, ctxE) ← equivOwnPosCongr cfg ctx1 eSpec eHyp lhs rhs other
      parentStep.argIdx hRel
    return ← mkAppM ``fuel_eq_of_conv
      #[← ctxValProof cfg ctxE parentL, ← ctxValProof cfg ctxE parentR,
        valueEq]
  let [(cSpec, cHyp)] := congMatches
    | throwError "replayCongCollapse: {congMatches.length} congruence \
        hypotheses match ({parentStep.fn.name} arg {parentStep.argIdx} under \
        {rSym.name}) among the step-cited congruence runes \
        {citedCongs} — need exactly 1 (frontier)"
  let parentL := rebuild parentStep lhs
  let parentR := rebuild parentStep rhs
  let some pArgs := (match parentL with
      | .cons _ argsS => argsS.toList?
      | _ => none)
    | throwError "replayCongCollapse: parent {repr parentL} is not an \
        application"
  unless pArgs.length == cSpec.argVars.length do
    throwError "replayCongCollapse: congruence {cSpec.name} arity \
        {cSpec.argVars.length} ≠ the parent's {pArgs.length}"
  unless pArgs[cSpec.pos]? == some lhs do
    throwError "replayCongCollapse: the parent's arg at the congruence \
        position is not the node lhs (internal)"
  let σcVars := cSpec.argVars ++ [cSpec.vy]
  let σcTerms := pArgs ++ [rhs]
  -- recompute-and-check the whole instance against the defcong pieces
  unless ACL2.Replay.substTerm σcVars σcTerms cSpec.lhsApp == parentL &&
         ACL2.Replay.substTerm σcVars σcTerms cSpec.rhsApp == parentR &&
         ACL2.Replay.substTerm σcVars σcTerms cSpec.hyp == relAppσ do
    throwError "replayCongCollapse: congruence {cSpec.name} instance does \
        not reconstruct the parent applications / the relation fact \
        (frontier)"
  unless (ACL2.Replay.freeVars cSpec.formula).all (σcVars.contains ·) do
    throwError "replayCongCollapse: congruence {cSpec.name} formula has \
        variables outside its arg/vy set (internal)"
  let (hImp, ctx2) ← instantiateEvTrueHypAt cfg ctx1 cHyp σcVars σcTerms
    cSpec.formula
  let implyσ := ACL2.Replay.substTerm σcVars σcTerms cSpec.formula
  -- value-level MP + the two-valued EQUAL decode
  let ctx3 ← pinTermOpaques cfg cfg.envExpr ctx2 implyσ
  let hFne ← mkAppM ``ne_nil_of_evtrue_conv
    #[hImp, ← ctxValProof cfg ctx3 implyσ]
  let hvH ← mkAppM ``ne_nil_of_evtrue_conv
    #[hRel, ← ctxValProof cfg ctx3 relAppσ]
  let hvC ← mkAppM ``implies_value_mp #[hFne, hvH]
  let hEq ← mkAppM ``Logic.eq_of_equal_ne_nil #[hvC]
  mkAppM ``fuel_eq_of_conv
    #[← ctxValProof cfg ctx3 parentL, ← ctxValProof cfg ctx3 parentR, hEq]

/-- Replay a preprocess chain's CORE: the composed relation between the
    formula and the final term — `(proof, isIff)` where the proof is the
    eval-equality `∃N∀f≥N, eval formula = eval final` when `isIff = false`,
    and `EvRel SIff w env formula final` when any step was IFF-only
    (`isIff = true`). `none` for an empty chain. R is threaded per the
    binding invariant L2: equal steps inject into the iff composite by
    refinement (`evrel_of_fuel_eq` + `siff_refl`). -/
def replayPreprocessChainCore (cfg : ReplayConfig) (ctx : ReplayCtx)
    (formula : SExpr) (nodes : List ProofNode)
    (citedCongs : List String := [])
    (citedEquivs : List String := []) :
    MetaM (Option (Expr × Bool) × SExpr) := do
  let mut cur := formula
  let mut acc : Option (Expr × Bool) := none
  for n in nodes do
    let (lhs, rhs) := nodeLhsRhs n
    let .node _ _ _ _ prov := n
    -- D10: a verdict-only discharge node is an SIff step `lhs ~iff~ 't`
    -- (its honest content is `EvTrue lhs`); if-iff nodes stay; everything
    -- else is an eval-equality step
    let isDischarge := dischargeOrigins.contains prov.origin
    let isIffNode := prov.origin == "preprocess/if-iff" || isDischarge
    -- G2 rung 2: a step under a USER equivalence R collapses at its
    -- congruence frame (`replayCongCollapse`); its payload is already the
    -- parent-level eval-equality, so the lift starts one frame out
    let isUserRel := !isIffNode && prov.equiv != "equal" && prov.equiv != "iff"
    let pathFor : SExpr → MetaM (List PathStep) := fun redex => do
      -- ONLY abbrev-path-rooted paths are rooted at the FORMULA this chain
      -- walks (infra/abbrev-path): abbreviation-expansion and the S2b
      -- expand-abbreviations/* emissions (their :PATH is
      -- (reverse *structured-abbrev-path*) — re-audit F2: discarding the
      -- emitted position in favour of occurrence search threw away exactly
      -- the data the fork records). Rewrite-side gstack paths that flushed
      -- into a preprocess chain are LITERAL-rooted (boundary frames,
      -- different origins) and must use the position fallback.
      if prov.path.isEmpty
          || !(prov.origin == "abbreviation-expansion"
               || prov.origin == "expand-abbreviations/lambda-body"
               || prov.origin == "expand-abbreviations/hide-subst"
               || prov.origin == "expand-abbreviations/nonrec-body") then
        match findOccurrences cur redex with
        | [p] => pure p
        | [] => throwError "replayPreprocessChain: node lhs {repr redex} does not occur \
                            in the current term {repr cur}"
        | ps => throwError "replayPreprocessChain: node lhs {repr redex} occurs \
                            {ps.length} times in {repr cur} — ambiguous position \
                            (needs :PATH emission at the preprocess site)"
      else
        -- the EMITTED :PATH (abbreviation-expansion frames, rooted at the
        -- formula this chain walks — infra/abbrev-path in the fork):
        -- navigate and VERIFY the redex; required when the lhs occurs more
        -- than once (msort HOW-MANY-MSORT's twice-occurring (ODDS X))
        match pathStepsFromFrames cur prov.path redex with
        | .ok p => pure p
        | .error e => throwError "replayPreprocessChain: emitted :PATH does \
            not navigate to the redex {repr redex}: {e}"
    let (nodeP, payloadIff, baseL, baseR, liftPath) ←
      if isUserRel then do
        let path ← pathFor lhs
        let some parentStep := path.getLast?
          | throwError "replayPreprocessChain: user-equivalence step \
              ({prov.equiv}) at the chain root — no congruence frame \
              (frontier)"
        let p ← replayCongCollapse cfg ctx n parentStep citedCongs citedEquivs
        pure (p, false, rebuild parentStep lhs, rebuild parentStep rhs,
              path.dropLast)
      else do
        let p ←
          if isDischarge then do
            unless rhs == quoteT do
              throwError "discharge node: rhs {repr rhs} ≠ (quote t)"
            let ev ← replayDischargeNode cfg
              { ctx with tauBasis := nodeTauBasis n } lhs
            mkAppM ``evrel_siff_qt_of_evtrue #[ev]
          else if isIffNode then replayIfIffNode cfg ctx n
          else replayPreprocessNode cfg ctx n
        let path ← pathFor lhs
        pure (p, isIffNode, lhs, rhs, path)
    -- lift innermost-out; iff payloads use the R congruence table and may
    -- COLLAPSE to an eval-equality at an if-test position
    let mut inner := nodeP
    let mut innerIff := payloadIff
    let mut curL := baseL
    let mut curR := baseR
    for st in liftPath.reverse do
      if innerIff then
        let (p, stillIff) ← applyStepSIff cfg ctx st inner
        inner := p
        innerIff := stillIff
      else
        inner ← applyStep cfg.worldExpr cfg.envExpr st curL curR inner
      curL := rebuild st curL
      curR := rebuild st curR
    unless curL == cur do
      throwError "replayPreprocessChain: reconstructed {repr curL} ≠ current {repr cur}"
    -- compose
    acc := some (← match acc, innerIff with
      | none, _ => pure (inner, innerIff)
      | some (a, false), false =>
        return (← mkAppM ``fuel_chain_eq #[a, inner], false)
      | some (a, aIff), _ => do
        -- iff composite: inject any eval-equality side via refinement
        let aS ← if aIff then pure a else do
          let pConv ← ctxValProof cfg ctx curL
          mkAppM ``evrel_of_fuel_eq #[mkConst ``siff_refl, a, pConv]
        let iS ← if innerIff then pure inner else do
          let pConv ← ctxValProof cfg ctx curR
          mkAppM ``evrel_of_fuel_eq #[mkConst ``siff_refl, inner, pConv]
        return (← mkAppM ``evrel_trans #[mkConst ``siff_trans, aS, iS], true))
    cur := curR
  return (acc, cur)

/-- Replay a clause discharged ENTIRELY by a preprocess chain: the step nodes
    compose the single-literal clause's formula to `(quote t)`. Returns
    `EvTrue w env formula` — an IFF chain ends by backward truth transport
    with NO boolean-valuedness side condition (the G1-interim
    `strengthenIffChain`/`formulaBooleanFact` pair is gone, G2). -/
def replayPreprocessChain (cfg : ReplayConfig) (ctx : ReplayCtx)
    (formula : SExpr) (nodes : List ProofNode)
    (citedCongs : List String := [])
    (citedEquivs : List String := []) : MetaM Expr := do
  let (acc, cur) ← replayPreprocessChainCore cfg ctx formula nodes citedCongs
    citedEquivs
  unless cur == quoteT do
    throwError "replayPreprocessChain: chain ended at {repr cur}, expected (quote t)"
  let some (chain, isIff) := acc
    | throwError "replayPreprocessChain: no step nodes"
  if isIff then
    let pEnd ← mkAppM ``evtrue_of_eq_t #[← quoteTFact cfg]
    mkAppM ``evtrue_of_evrel_siff #[chain, pEnd]
  else
    let hq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
    mkAppM ``evtrue_of_eq_t #[← mkAppM ``fuel_conv_of_eq #[chain, hq]]

/-! ## The clausify BRIDGE (#53C): proved child clause → the clausify input

`bridgeClausify` proves `EvTrue w env input` from the PROVED output
clause (`EvTrue w env (disjoinTerm cl)` — the pool-root/child replay), by
mirroring `clausify-input1`'s PURE if-recursion. The recorded checkpoints
validate every joint (recomputed neg-clause/split/out must equal the record;
an `expand-and-or` marker is a frontier — that expansion is ens-dependent and
not recomputable). Mechanism (G3
Fragment B): ONE `clausifyPure_sound` instantiation — the once-proved bridge
lemma over the pure recursion — replaces the per-leaf peel/walk proof
construction entirely; its premises are the Fragment-A bundle, the input's
lift fact (by reduction), and the opaque-key well-formedness (by kernel
decision). -/

/-- Consume an expansion's recorded DETAIL chain (2e, design ruled
    2026-08-10): stepwise from the registry form `r0` to the recorded
    `:TO`, each step by its own recipe — `preprocess/equal-self` at the
    whole term or a direct IF branch (liftability of the discarded side
    kernel-decided), and the `preprocess/if-iff` collapse at the whole
    term over an EQUAL-headed (boolean) carrier, where the recorded
    `:EQUIV IFF` step is a VALUE equality (`dpLiftF_if_t_nil_equal`) —
    the approved nilEquiv weakening stays the fallback for a non-boolean
    carrier (loud frontier until witnessed). Returns the final term and
    `dpLiftF vars opq r0 = dpLiftF vars opq final`. -/
def consumeExpandDetail (b : DpLiftBundle) (hwf : Expr)
    (r0 : SExpr) (detail : List TraceEvent) : MetaM (SExpr × Expr) := do
  let liftE : SExpr → Expr := fun t =>
    mkApp3 (mkConst ``dpLiftF) b.varsE b.opqE (reflectSExpr t)
  let mut cur := r0
  let mut prf? : Option Expr := none
  for ev in detail do
    let .rewriteStep st := ev
      | throwError "2e detail: non-step detail event (frontier)"
    let (next, step) ←
      if st.origin == "preprocess/equal-self" then do
        let .cons (.atom (.symbol es)) (.cons u (.cons u' .nil)) := st.lhs
          | throwError "2e detail: equal-self lhs {repr st.lhs} is not \
              binary (frontier)"
        unless es.name == "EQUAL" && u == u' && st.rhs == quoteT do
          throwError "2e detail: equal-self step shape mismatch at \
              {repr st.lhs} (frontier)"
        let hu ← mkDecideProof (← mkEq
          (← Lean.Meta.mkAppM ``Option.isSome #[liftE u])
          (mkConst ``Bool.true))
        let hSelf ← mkAppOptM ``dpLiftF_equal_self
          #[some b.varsE, some b.opqE, some hwf, some (reflectSExpr u),
            some hu]
        if cur == st.lhs then
          pure (quoteT, hSelf)
        else match cur with
          | .cons (.atom (.symbol ifs))
              (.cons c (.cons bb (.cons ee .nil))) =>
            if ifs.name == "IF" && bb == st.lhs then do
              let he ← Lean.Meta.mkEqRefl (liftE ee)
              let p ← mkAppOptM ``dpLiftF_ifT_congr
                #[some b.varsE, some b.opqE, some hwf,
                  some (reflectSExpr c), none, none, none, none,
                  some hSelf, some he]
              pure ((ifT c quoteT ee : SExpr), p)
            else if ifs.name == "IF" && ee == st.lhs then do
              let hb ← Lean.Meta.mkEqRefl (liftE bb)
              let p ← mkAppOptM ``dpLiftF_ifT_congr
                #[some b.varsE, some b.opqE, some hwf,
                  some (reflectSExpr c), none, none, none, none,
                  some hb, some hSelf]
              pure ((ifT c bb quoteT : SExpr), p)
            else throwError "2e detail: equal-self lhs {repr st.lhs} is \
                neither the current term nor a direct IF branch of \
                {repr cur} (frontier)"
          | _ => throwError "2e detail: equal-self lhs {repr st.lhs} \
              does not match the current term {repr cur} (frontier)"
      else if st.origin == "preprocess/if-iff" then do
        unless cur == st.lhs do
          throwError "2e detail: if-iff lhs {repr st.lhs} ≠ the current \
              term {repr cur} (frontier)"
        let .cons (.atom (.symbol ifs))
            (.cons tst (.cons th (.cons el .nil))) := st.lhs
          | throwError "2e detail: if-iff lhs {repr st.lhs} is not an IF \
              (frontier)"
        unless ifs.name == "IF" && th == quoteT && el == quoteNil &&
            st.rhs == tst do
          throwError "2e detail: if-iff step is not the (IF x 'T 'NIL) ⇒ x \
              collapse at {repr st.lhs} (frontier)"
        let .cons (.atom (.symbol es)) (.cons a (.cons bb .nil)) := tst
          | throwError "2e detail: if-iff collapse over the non-EQUAL \
              carrier {repr tst} — the value-equality recipe needs a \
              boolean carrier; the approved nilEquiv fallback has no \
              witness yet (frontier)"
        unless es.name == "EQUAL" do
          throwError "2e detail: if-iff collapse over the non-EQUAL \
              carrier {repr tst} — the value-equality recipe needs a \
              boolean carrier; the approved nilEquiv fallback has no \
              witness yet (frontier)"
        let p ← mkAppOptM ``dpLiftF_if_t_nil_equal
          #[some b.varsE, some b.opqE, some hwf, some (reflectSExpr a),
            some (reflectSExpr bb)]
        pure (tst, p)
      else
        throwError "2e detail: unrecognized detail origin {st.origin} \
            (frontier)"
    prf? := some (← match prf? with
      | none => pure step
      | some p => Lean.Meta.mkAppM ``Eq.trans #[p, step])
    cur := next
  let some prf := prf?
    | throwError "2e detail: empty detail chain (internal)"
  return (cur, prf)

/-- The CHECKED expansion walk for one clausify pass (expand-and-or plan
    S3): every recorded firing must be REGISTRY-SHAPED (NOT/ENDP/ATOM
    def-body expansions with the exact emitted if-form target — anything
    else is the S4 lemma-arm frontier) and fully consumed by `expandTerm`.
    Returns the expanded term t′ and the PROOF
    `dpLiftF vars opq t′ = dpLiftF vars opq input` (via the per-builtin
    registry lemmas + `expandTerm_liftEq`, with the walk itself
    kernel-decided). `none` expansions short-circuit to (input, rfl-free).
    An expansion carrying recorded DETAIL steps (2e) composes its registry
    identity with the stepwise detail chain (`consumeExpandDetail`). -/
def runCheckedExpand (b : DpLiftBundle) (hwf : Expr)
    (exps : List ClausifyExpansion) (input : SExpr) (pos : Bool) :
    MetaM (SExpr × Option Expr) := do
  if exps.isEmpty then return (input, none)
  -- registry shape validation (value-level, fail-closed); DETAIL-carrying
  -- expansions (2e) defer their :TO check to the stepwise consumption in
  -- the entry-proof pass — only the EQUAL lemma arm supports details
  -- (the recorded class); a detailed unary expansion stays a frontier
  let mkIfT (c : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := "IF" }))
      (.cons c (.cons quoteNil (.cons quoteT .nil)))
  let mkConspT (x : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := "CONSP" })) (.cons x .nil)
  for e in exps do
    match e.fromTerm with
    | .cons (.atom (.symbol h)) (.cons x .nil) =>
      unless e.detail.isEmpty do
        throwError "runCheckedExpand: unary expansion {repr e.fromTerm} \
            carries detail steps — only the EQUAL lemma arm's detail class \
            is recorded (frontier)"
      if h.name == "NOT" then
        unless e.toTerm == mkIfT x do
          throwError "runCheckedExpand: NOT expansion target {repr e.toTerm} \
              ≠ the registry if-form (frontier)"
      else if h.name == "ENDP" || h.name == "ATOM" then
        unless e.toTerm == mkIfT (mkConspT x) do
          throwError "runCheckedExpand: {h.name} expansion target \
              {repr e.toTerm} ≠ the registry if-form (frontier)"
      else
        throwError "runCheckedExpand: expansion head {h.name} not in the \
            def-body registry (frontier: the S4 and-or lemma arm)"
    | .cons (.atom (.symbol h)) (.cons a (.cons b .nil)) =>
      -- S4 LEMMA arm, as the census demands (ORDERED-PERMS Subgoal *1/7'4',
      -- rewrite:EQUAL-CONS): `(EQUAL (CONS x y) z)` expands to the exact
      -- cons-decomposition if-form — a primitive-level identity
      -- (`dpLiftF_equal_cons_expand`); any other binary shape or target
      -- stays a fail-closed frontier.
      let ok := h.name == "EQUAL" &&
        (match a with
         | .cons (.atom (.symbol cs)) (.cons _ (.cons _ .nil)) =>
           cs.name == "CONS"
         | _ => false)
      unless ok do
        throwError "runCheckedExpand: binary expansion FROM \
            {repr e.fromTerm} is not the (EQUAL (CONS x y) z) lemma-arm \
            shape (frontier)"
      let .cons _ (.cons x (.cons y .nil)) := a
        | throwError "runCheckedExpand: internal — shape re-check"
      -- CONS-CONS variant (equal-descent restructure arc — the
      -- ground-zero `(:REWRITE CONS-EQUAL)` fired as a clausify
      -- expansion, ORDEREDP-WHEN-BNEXT-CONSTANT *1/4.2'): when the
      -- OTHER side is itself a cons application the decomposition
      -- pairs components directly, no CONSP guard.
      let expected : SExpr :=
        match b with
        | .cons (.atom (.symbol bs)) (.cons x2 (.cons y2 .nil)) =>
          if bs.name == "CONS" then
            .cons (.atom (.symbol { name := "IF" }))
              (.cons (.cons (.atom (.symbol { name := "EQUAL" }))
                (.cons x (.cons x2 .nil)))
                (.cons (.cons (.atom (.symbol { name := "EQUAL" }))
                  (.cons y (.cons y2 .nil)))
                  (.cons quoteNil .nil)))
          else
            .cons (.atom (.symbol { name := "IF" }))
              (.cons (mkConspT b)
                (.cons (.cons (.atom (.symbol { name := "IF" }))
                  (.cons (.cons (.atom (.symbol { name := "EQUAL" }))
                    (.cons x (.cons (.cons (.atom (.symbol { name := "CAR" }))
                      (.cons b .nil)) .nil)))
                    (.cons (.cons (.atom (.symbol { name := "EQUAL" }))
                      (.cons y (.cons (.cons (.atom (.symbol { name := "CDR" }))
                        (.cons b .nil)) .nil)))
                      (.cons quoteNil .nil))))
                  (.cons quoteNil .nil)))
        | _ =>
          .cons (.atom (.symbol { name := "IF" }))
            (.cons (mkConspT b)
              (.cons (.cons (.atom (.symbol { name := "IF" }))
                (.cons (.cons (.atom (.symbol { name := "EQUAL" }))
                  (.cons x (.cons (.cons (.atom (.symbol { name := "CAR" }))
                    (.cons b .nil)) .nil)))
                  (.cons (.cons (.atom (.symbol { name := "EQUAL" }))
                    (.cons y (.cons (.cons (.atom (.symbol { name := "CDR" }))
                      (.cons b .nil)) .nil)))
                    (.cons quoteNil .nil))))
                (.cons quoteNil .nil)))
      if e.detail.isEmpty then
        unless e.toTerm == expected do
          throwError "runCheckedExpand: EQUAL-CONS expansion target \
              {repr e.toTerm} ≠ the registry decomposition form (frontier)"
    | _ =>
      throwError "runCheckedExpand: expansion FROM {repr e.fromTerm} is not \
          a registry application (frontier)"
  let cexps : List CExp := exps.map fun e => (e.fromTerm, e.toTerm, e.pos)
  let fuel := clausifyFuel cexps input
  let (t', leftover) ← match expandTerm fuel cexps input pos with
    | some r => pure r
    | none => throwError "runCheckedExpand: expansion walk ran out of fuel \
        (internal)"
  unless leftover.isEmpty do
    throwError "runCheckedExpand: {leftover.length} recorded expansion(s) \
        not consumed by the walk at {repr input} (order/position \
        divergence — frontier)"
  -- Expr-level: the walk as a kernel-decided fact + the hexp family
  let sexprTy := mkConst ``SExpr
  let boolTy := mkConst ``Bool
  let cexpTy ← mkAppM ``Prod #[sexprTy, ← mkAppM ``Prod #[sexprTy, boolTy]]
  let reflectCExp (e : ClausifyExpansion) : MetaM Expr := do
    mkAppM ``Prod.mk #[reflectSExpr e.fromTerm,
      ← mkAppM ``Prod.mk #[reflectSExpr e.toTerm,
        if e.pos then mkConst ``Bool.true else mkConst ``Bool.false]]
  let cexpEs ← exps.mapM reflectCExp
  let cexpsE ← mkListLit cexpTy cexpEs
  let fuelE := mkNatLit fuel
  let posE := if pos then mkConst ``Bool.true else mkConst ``Bool.false
  let t'E := reflectSExpr t'
  let nilE ← mkListLit cexpTy []
  let lhsE ← mkAppM ``expandTerm #[fuelE, cexpsE, reflectSExpr input, posE]
  let rhsE ← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[t'E, nilE]]
  unless ← isDefEq lhsE rhsE do
    throwError "runCheckedExpand: the reflected walk does not reduce to \
        the runtime result at {repr input} (internal)"
  let hcomp ← mkExpectedTypeHint (← mkEqRefl rhsE) (← mkEq lhsE rhsE)
  -- hexp : ∀ e ∈ cexps, dpLiftF vars opq e.1 = dpLiftF vars opq e.2.1
  let pFn ← withLocalDeclD `e cexpTy fun eV => do
    let fst ← mkAppM ``Prod.fst #[eV]
    let toFst ← mkAppM ``Prod.fst #[← mkAppM ``Prod.snd #[eV]]
    mkLambdaFVars #[eV] (← mkEq
      (mkApp3 (mkConst ``dpLiftF) b.varsE b.opqE fst)
      (mkApp3 (mkConst ``dpLiftF) b.varsE b.opqE toFst))
  let entryProofs ← exps.mapM fun e => do
    match e.fromTerm with
    | .cons (.atom (.symbol h)) (.cons x .nil) =>
      let lem :=
        if h.name == "NOT" then ``dpLiftF_not_expand
        else if h.name == "ENDP" then ``dpLiftF_endp_expand
        else ``dpLiftF_atom_expand
      mkAppOptM lem #[some b.varsE, some b.opqE, some hwf, some (reflectSExpr x)]
    | .cons _ (.cons (.cons _ (.cons x (.cons y .nil))) (.cons z .nil)) => do
      -- the (EQUAL (CONS x y) z) lemma arm (validated above); the
      -- CONS-CONS variant takes its own registry identity
      let (hReg, regForm) ←
        match z with
        | .cons (.atom (.symbol zs)) (.cons x2 (.cons y2 .nil)) =>
          if zs.name == "CONS" then do
            let p ← mkAppOptM ``dpLiftF_equal_cons_cons_expand
              #[some b.varsE, some b.opqE, some hwf, some (reflectSExpr x),
                some (reflectSExpr y), some (reflectSExpr x2),
                some (reflectSExpr y2)]
            let eqApp : SExpr → SExpr → SExpr := fun a bb =>
              .cons (.atom (.symbol { name := "EQUAL" }))
                (.cons a (.cons bb .nil))
            pure (p, (.cons (.atom (.symbol { name := "IF" }))
              (.cons (eqApp x x2) (.cons (eqApp y y2)
                (.cons quoteNil .nil))) : SExpr))
          else do
            unless e.detail.isEmpty do
              throwError "runCheckedExpand: detail steps on the \
                  CONSP-guard EQUAL-CONS variant have no witness (frontier)"
            let p ← mkAppOptM ``dpLiftF_equal_cons_expand
              #[some b.varsE, some b.opqE, some hwf, some (reflectSExpr x),
                some (reflectSExpr y), some (reflectSExpr z)]
            pure (p, e.toTerm)
        | _ => do
          unless e.detail.isEmpty do
            throwError "runCheckedExpand: detail steps on the CONSP-guard \
                EQUAL-CONS variant have no witness (frontier)"
          let p ← mkAppOptM ``dpLiftF_equal_cons_expand
            #[some b.varsE, some b.opqE, some hwf, some (reflectSExpr x),
              some (reflectSExpr y), some (reflectSExpr z)]
          pure (p, e.toTerm)
      if e.detail.isEmpty then
        pure hReg
      else do
        -- 2e: compose the registry identity with the stepwise detail chain
        let (finalT, hDet) ← consumeExpandDetail b hwf regForm e.detail
        unless finalT == e.toTerm do
          throwError "runCheckedExpand: detail chain from {repr regForm} \
              ends at {repr finalT} ≠ the recorded target {repr e.toTerm} \
              (frontier)"
        Lean.Meta.mkAppM ``Eq.trans #[hReg, hDet]
    | _ => throwError "runCheckedExpand: internal — shape re-check"
  let (_, hexpRaw) ← mkForallMemProof cexpTy pFn (cexpEs.zip entryProofs)
  let memTy ← withLocalDeclD `e cexpTy fun eV => do
    let mem ← mkAppM ``Membership.mem #[cexpsE, eV]
    mkForallFVars #[eV] (← mkArrow mem (mkApp pFn eV).headBeta)
  let hexpE ← mkExpectedTypeHint hexpRaw memTy
  let conj ← mkAppM ``expandTerm_liftEq
    #[hwf, fuelE, cexpsE, reflectSExpr input, posE, t'E, nilE, hexpE, hcomp]
  let heq ← mkAppM ``And.right #[conj]
  return (t', some heq)

/-- Bridge a clausify record: prove `EvTrue w env info.input` from
    `pOut : EvTrue w env (disjoinTerm cl₀)` (the proved single output clause).
    Validates the WHOLE record against the pure recomputation; any divergence
    (an `expand-and-or` expansion, a structured neg-clause, multiple outputs)
    is a hard frontier error. -/
def bridgeClausify (cfg : ReplayConfig) (ctx : ReplayCtx) (info : ClausifyInfo)
    (pOut? : Option Expr) (tautDropped : Bool := false) : MetaM Expr := do
  -- the lift bundle FIRST (the checked expansion walks need it)
  let vars := (ACL2.Replay.freeVars info.input).eraseDups
  let opaques := (collectOpaques info.input).eraseDups
  let pinned ← opaques.mapM fun op => do
    let some (v, p) := ctx.val? op
      | throwError "bridgeClausify: opaque {repr op} has no pinned value \
                    (frontier)"
    pure (op, v, p)
  let opqMap := pinned.map fun (op, v, _) => (op, v)
  let opqP := pinned.map fun (op, _, p) => (op, p)
  let b ← mkDpLiftBundle cfg cfg.envExpr vars opqMap opqP
  let hwf ← mkDecideProof
    (← mkEq (mkApp (mkConst ``dpOpqWF) b.opqE) (mkConst ``Bool.true))
  -- CHECKED recomputations (expand-and-or plan S3): consume the recorded
  -- firings; with none recorded these are exactly the pure recomputes
  let (tNeg, _) ← runCheckedExpand b hwf info.negExpands info.input false
  let negRecomputed := clausifyPure tNeg false
  unless negRecomputed == info.negClause do
    throwError "clausify bridge: recomputed neg-clause {repr negRecomputed} ≠ \
                recorded {repr info.negClause} (divergence: an unregistered \
                expansion, disjoin-clauses literal merging, or an unmirrored \
                dumb-negate-lit arm)"
  let [l0] := info.negClause
    | throwError "clausify bridge: structured (multi-literal) neg-clause — \
                  frontier: {repr info.negClause}"
  let [(splitLit, cl0)] := info.splits
    | throwError "clausify bridge: expected exactly one split (frontier)"
  unless splitLit == dumbNegateLit l0 do
    throwError "clausify bridge: split literal {repr splitLit} ≠ \
                (dumb-negate {repr l0})"
  unless dumbNegateLit l0 == info.input do
    throwError "clausify bridge: negation round-trip {repr (dumbNegateLit l0)} ≠ \
                input {repr info.input} (frontier)"
  unless info.splitExpands.all (·.1 == 0) do
    throwError "clausify bridge: split-expansion index beyond the single \
                split (internal)"
  let (t', heq?) ← runCheckedExpand b hwf (info.splitExpands.map (·.2))
    info.input true
  -- ACL2's `add-literal` DEDUP arm (S1 2026-07-23): a literal already
  -- present is dropped, so the recorded clause may be the recompute's
  -- eraseDups — accepted, with the proof routed through
  -- `clausifyPure_sound_dedup` (a true deduped disjunction trues the full
  -- one). Any other divergence still hard-fails.
  let recomputedSplit := clausifyPure t' true
  let dedupHit := recomputedSplit != cl0 && dedupClause recomputedSplit == cl0
  -- RECORDED-drop relaxation (2e + item E): add-literal's member-term
  -- drop removes a COMMUTED duplicate the exact-dup `dedupClause` cannot
  -- see; accepted ONLY when removing exactly the recorded (:DEDUP-DROP …)
  -- literals (this split's index) from the recompute reproduces the
  -- recorded clause — a read-off, and the proof needs only membership
  -- (`clausifyPure_sound_sub`).
  let removeOnce : List SExpr → SExpr → List SExpr := fun ls d =>
    match ls.findIdx? (· == d) with
    | some i => ls.eraseIdx i
    | none => ls
  let drops := (info.dedupDrops.filter (·.1 == 0)).map (·.2)
  let recordedDropHit := recomputedSplit != cl0 && !dedupHit &&
    !drops.isEmpty && drops.foldl removeOnce recomputedSplit == cl0
  -- TAUTOLOGY-DROPPED record (G1 inc-2c): if-interp folded the split
  -- clause's complementary pair to a 'T literal (the record shows ['T]) and
  -- remove-trivial-clauses dropped the output; the recompute keeps the full
  -- clause. Accepted with the taut relaxation — the proof is built OVER THE
  -- RECOMPUTED clause from its complementary pair below (the same
  -- tautologyp reasoning ACL2 used).
  let tautHit := tautDropped && info.out == [] && cl0 == [quoteT]
  unless recomputedSplit == cl0 || dedupHit || tautHit || recordedDropHit do
    throwError "clausify bridge: recomputed split clause \
                {repr recomputedSplit} ≠ recorded {repr cl0} \
                (divergence: an unregistered expansion, disjoin-clauses \
                literal merging, an unmirrored dumb-negate-lit arm, or a \
                dropped literal with no recorded :DEDUP-DROP)"
  unless info.out == [cl0] || (tautDropped && info.out == []) do
    throwError "clausify bridge: output set {repr info.out} ≠ [the split clause] \
                (multi-clause output — frontier)"
  -- G3 Fragment B: ONE clausifyPure_sound instantiation at the EXPANDED
  -- term t′, transported back to the input by the lift-equality when
  -- expansions fired (expand-and-or plan S3)
  let mkIsSome : SExpr → MetaM Expr := fun t => do
    let vE ← dpValExpr opqMap (dpConcVar cfg.envExpr) t
    let someV := mkApp2 (mkConst ``Option.some [0]) (mkConst ``SExpr) vE
    let liftApp := mkApp3 (mkConst ``dpLiftF) b.varsE b.opqE (reflectSExpr t)
    unless ← isDefEq liftApp someV do
      throwError "bridgeClausify: {repr t} does not lift to the walker's \
                  value (function/walker divergence — a defect)"
    let isSomeApp ← mkAppM ``Option.isSome #[liftApp]
    mkExpectedTypeHint (← mkEqRefl (mkConst ``Bool.true))
      (← mkEq isSomeApp (mkConst ``Bool.true))
  let hisSomeT' ← mkIsSome t'
  let pOut ← match pOut? with
    | some p => pure p
    | none => do
      unless tautHit do
        throwError "clausify bridge: no output-clause proof (internal)"
      -- the tautology proof of the RECOMPUTED split clause: its complementary
      -- pair's excluded middle (the shared `tautClauseClose`)
      tautClauseClose cfg ctx recomputedSplit
        "clausify bridge: taut-dropped output"
  let prfT' ←
    if recordedDropHit then do
      let cl0E ← mkListLit (mkConst ``SExpr) (cl0.map reflectSExpr)
      let cpE ← mkAppM ``clausifyPure #[reflectSExpr t', mkConst ``Bool.true]
      let f ← withLocalDeclD `l (mkConst ``SExpr) fun lV => do
        mkLambdaFVars #[lV] (← mkAppM ``List.contains #[cpE, lV])
      let hsub ← mkDecideProof
        (← mkEq (← mkAppM ``List.all #[cl0E, f]) (mkConst ``Bool.true))
      mkAppM ``clausifyPure_sound_sub
        #[cfg.worldExpr, cfg.envExpr, b.hvars, b.hopq, b.hns, hwf,
          reflectSExpr t', mkConst ``Bool.true, cl0E, hsub, hisSomeT', pOut]
    else
      mkAppM
        (if dedupHit then ``clausifyPure_sound_dedup else ``clausifyPure_sound)
        #[cfg.worldExpr, cfg.envExpr, b.hvars, b.hopq, b.hns, hwf,
          reflectSExpr t', mkConst ``Bool.true, hisSomeT', pOut]
  let prf ← match heq? with
    | none => pure prfT'
    | some heq => do
      let hisSomeIn ← mkIsSome info.input
      mkAppM ``ClausifyGoal_of_liftEq
        #[cfg.worldExpr, cfg.envExpr, b.hvars, b.hopq, b.hns, heq,
          hisSomeIn, mkConst ``Bool.true, prfT']
  -- `ClausifyGoal … true` IS `EvTrue …` definitionally; cast for consumers
  mkExpectedTypeHint prf
    (← mkAppM ``EvTrue #[cfg.worldExpr, cfg.envExpr, reflectSExpr info.input])

/-- The MULTI-clause clausify bridge: `EvTrue w env info.input` from one
    `EvTrue (disjoin outᵢ)` per output clause. The record is validated
    against the pure recomputation exactly as in the single case, extended:
    the neg-clause's literals L₁…Lₙ each split (`:CLAUSIFY-SPLIT`) into
    `clausifyPure (dumbNegateLit Lᵢ) true = outᵢ`; each proved outᵢ gives
    `EvTrue (¬Lᵢ)` (`clausifyPure_sound`), hence `eval Lᵢ → nil`
    (`sound_neg_leaf`); all neg-literals false gives the input's truth
    (`clausifyAllFalse_sound` — the conjunction lemma). -/
def bridgeClausifyMulti (cfg : ReplayConfig) (ctx : ReplayCtx)
    (info : ClausifyInfo) (pOuts : List Expr) : MetaM Expr := do
  -- never-ignore (fold-back audit F5a): the multi path has NO negExpands
  -- consumer — phase-1 expansions here would be silently dropped (their
  -- only backstop the incidental neg-clause recompute below). Hard-fail
  -- until the multi path consumes them.
  unless info.negExpands.isEmpty do
    throwError "clausify multi-bridge: {info.negExpands.length} phase-1         expansion(s) on a multi-clause clausify — the multi path does not         consume negExpands (frontier; never dropped)"
  let negRecomputed := clausifyPure info.input false
  unless negRecomputed == info.negClause do
    throwError "clausify multi-bridge: recomputed neg-clause                 {repr negRecomputed} ≠ recorded {repr info.negClause}"
  -- a TAUT-DROPPED split (G2 rung 2, p7's SAME-LN sym conjunct) is recorded
  -- with :CLAUSE ('T) — ACL2's type-set saw the split clause as trivially
  -- true (the commuted-equal pair) and replaced it; it contributes no out
  -- clause and no pushed child. Its EvTrue is proved from the RECOMPUTED
  -- clause by `tautClauseClose` in the loop below.
  unless info.splits.length == info.negClause.length &&
         pOuts.length == info.out.length &&
         info.out == (info.splits.map (·.2)).filter (· != [quoteT]) do
    throwError "clausify multi-bridge: splits/out/proofs mismatch at \
                {repr info.input} ({info.splits.length} split(s), \
                {info.negClause.length} neg literal(s), {info.out.length} \
                out clause(s), {pOuts.length} proof(s))"
  for (l, (lit, _)) in info.negClause.zip info.splits do
    unless lit == dumbNegateLit l do
      throwError "clausify multi-bridge: split literal {repr lit} ≠                   (dumb-negate {repr l})"
  -- per-split recompute happens in the proof loop below — it consumes the
  -- recorded per-split `expand-and-or` firings (sorting arc 2026-07-28,
  -- the admission-goal ENDP expansions), which need the lift bundle
  unless info.splitExpands.all (·.1 < info.splits.length) do
    throwError "clausify multi-bridge: split-expansion index beyond the \
                split list (internal)"
  -- the shared lift bundle (over the input's vars/opaques — every literal is
  -- built from the input's subterms, negations included)
  let vars := (ACL2.Replay.freeVars info.input).eraseDups
  let opaques := (collectOpaques info.input).eraseDups
  let pinned ← opaques.mapM fun op => do
    let some (v, p) := ctx.val? op
      | throwError "bridgeClausifyMulti: opaque {repr op} has no pinned value                     (frontier)"
    pure (op, v, p)
  let opqMap := pinned.map fun (op, v, _) => (op, v)
  let opqP := pinned.map fun (op, _, p) => (op, p)
  let b ← mkDpLiftBundle cfg cfg.envExpr vars opqMap opqP
  let hwf ← mkDecideProof
    (← mkEq (mkApp (mkConst ``dpOpqWF) b.opqE) (mkConst ``Bool.true))
  let mkIsSome : SExpr → MetaM Expr := fun t => do
    let vE ← dpValExpr opqMap (dpConcVar cfg.envExpr) t
    let someV := mkApp2 (mkConst ``Option.some [0]) (mkConst ``SExpr) vE
    let liftApp := mkApp3 (mkConst ``dpLiftF) b.varsE b.opqE (reflectSExpr t)
    unless ← isDefEq liftApp someV do
      throwError "bridgeClausifyMulti: {repr t} does not lift to the                   walker's value (function/walker divergence — a defect)"
    let isSomeApp ← mkAppM ``Option.isSome #[liftApp]
    mkExpectedTypeHint (← mkEqRefl (mkConst ``Bool.true))
      (← mkEq isSomeApp (mkConst ``Bool.true))
  -- per neg-literal: EvTrue(¬Lᵢ) from its proved clause, then eval Lᵢ → nil.
  -- The split recompute runs on the literal EXPANDED by its recorded
  -- `expand-and-or` firings (`runCheckedExpand` — registry-shaped,
  -- fail-closed); the soundness instance then applies at the expanded
  -- literal and transports back along the lift equality, exactly the
  -- single-clause bridge's route.
  let mut nilProofs : List Expr := []
  let mut pOutsRest := pOuts
  for ((l, (lit, cl)), k) in (info.negClause.zip info.splits).zipIdx do
    let expsK := (info.splitExpands.filter (·.1 == k)).map (·.2)
    let (lit', heqK?) ← runCheckedExpand b hwf expsK lit true
    let pOut ←
      if cl == [quoteT] then
        -- taut-dropped split: no out clause, no pushed child — prove the
        -- RECOMPUTED split clause by its complementary (possibly
        -- commuted-equal) pair, the single-bridge taut precedent
        tautClauseClose cfg ctx (clausifyPure lit' true)
          "clausify multi-bridge: taut-dropped split"
      else do
        unless clausifyPure lit' true == cl do
          throwError "clausify multi-bridge: recomputed split clause for                   {repr lit'} ≠ recorded {repr cl}"
        let p :: rest := pOutsRest
          | throwError "clausify multi-bridge: out-clause proofs exhausted \
              (internal)"
        pOutsRest := rest
        pure p
    let hlLit ← mkIsSome lit'
    let pLitTrue ← mkAppM ``clausifyPure_sound
      #[cfg.worldExpr, cfg.envExpr, b.hvars, b.hopq, b.hns, hwf,
        reflectSExpr lit', mkConst ``Bool.true, hlLit, pOut]
    let pLitTrue ← match heqK? with
      | none => pure pLitTrue
      | some heq => do
        let hisSomeLit ← mkIsSome lit
        mkAppM ``ClausifyGoal_of_liftEq
          #[cfg.worldExpr, cfg.envExpr, b.hvars, b.hopq, b.hns, heq,
            hisSomeLit, mkConst ``Bool.true, pLitTrue]
    -- ClausifyGoal … true IS EvTrue; and reflect(lit) is defeq to
    -- dumbNegateLit reflect(l) by computation
    let pLitTrue ← mkExpectedTypeHint pLitTrue
      (← mkAppM ``EvTrue #[cfg.worldExpr, cfg.envExpr,
        ← mkAppM ``ACL2.Replay.dumbNegateLit #[reflectSExpr l]])
    let hlL ← mkIsSome l
    nilProofs := nilProofs ++ [← mkAppM ``sound_neg_leaf
      #[cfg.worldExpr, cfg.envExpr, b.hvars, b.hopq, b.hns, hwf,
        reflectSExpr l, hlL, pLitTrue]]
  -- assemble ∀ L ∈ clausifyPure input false, eval L → nil
  let nilP ← withLocalDeclD `L (mkConst ``SExpr) fun lV => do
    let body ← withLocalDeclD `N (mkConst ``Nat) fun nV => do
      let inner ← withLocalDeclD `f (mkConst ``Nat) fun fV => do
        let ge ← mkAppM ``GE.ge #[fV, nV]
        let ev := mkAppN (mkConst ``evalOpt)
          #[fV, cfg.worldExpr, cfg.envExpr, lV]
        let nilE := mkApp2 (mkConst ``Option.some [0]) (mkConst ``SExpr)
          (mkConst ``SExpr.nil)
        mkForallFVars #[fV] (← mkArrow ge (← mkEq ev nilE))
      mkAppM ``Exists #[← mkLambdaFVars #[nV] inner]
    mkLambdaFVars #[lV] body
  let entries ← info.negClause.mapM fun l => pure (reflectSExpr l)
  let (_, hforallRaw) ← mkForallMemProof (mkConst ``SExpr) nilP
    (entries.zip nilProofs)
  let cpList ← mkAppM ``clausifyPure
    #[reflectSExpr info.input, mkConst ``Bool.false]
  let hforallTy ← withLocalDeclD `L (mkConst ``SExpr) fun lV => do
    let mem ← mkAppM ``Membership.mem #[cpList, lV]
    mkForallFVars #[lV] (← mkArrow mem (mkApp nilP lV).headBeta)
  let hforall ← mkExpectedTypeHint hforallRaw hforallTy
  let hisSome ← mkIsSome info.input
  let prf ← mkAppM ``clausifyAllFalse_sound
    #[cfg.worldExpr, cfg.envExpr, b.hvars, b.hopq, b.hns, hwf,
      reflectSExpr info.input, mkConst ``Bool.false, hisSome, hforall]
  mkExpectedTypeHint prf
    (← mkAppM ``EvTrue #[cfg.worldExpr, cfg.envExpr, reflectSExpr info.input])

end ACL2.Replay.Driver
