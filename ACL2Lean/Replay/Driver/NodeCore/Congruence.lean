/-
  Driver/NodeCore/Congruence — the R-PARAMETERIZED collapse (G1 lane,
  option M; ruled in docs/notes/2026-08-14_g1-design-brief.md).

  ACL2's rewriter is generic over equivalence relations: a step may be
  recorded under a USER equivalence R (`:EQUIV perm`) rather than `equal`,
  in which case the step carries NO eval-equality at all — only the
  relation fact `EvTrue w env (R a b)`. Such a payload cannot compose with
  anything until it is COLLAPSED to an equality at the enclosing
  congruence frame, which is exactly what ACL2's geneqv machinery licenses
  it to do. This module holds the collapse — shared by the PREPROCESS
  chain (`Driver/Preprocess.lean`'s `replayCongCollapse`) and the
  rewriter's literal-chain walker (`NodeCore/Rewrites.lean`) — plus the
  two recorded sources of an R-fact and the node dispatcher that carries
  the payload out.

  Scope (option M, deliberately minimal): the R payload lives for exactly
  ONE frame and its R-out is EQUAL. Everything else — a payload needing
  more than one frame, two composed R-steps, a multi-element geneqv, an
  R-step that is not the final step of its rhs block — hard-fails loudly
  here rather than being approximated.
-/
import ACL2Lean.Replay.Driver.NodeCore.Node

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- The node's emitted `:GENEQV` — the AMBIENT equivalence the rewriter
    was allowed to preserve at this redex. The R-collapse requires it to
    NAME the relation it collapses (fail-closed). -/
def nodeGeneqv : ProofNode → List String | .node _ _ _ _ p => p.geneqv

/-- The node's emitted `:RUNES` (the cumulative ttree set on entry — see
    `StepProvenance.runes`), used as the step-cited license anchor. -/
def nodeRunes : ProofNode → List Rune | .node _ _ _ _ p => p.runes

/-- Is this node an R-STEP — a recorded step under a USER equivalence
    (neither `equal` nor `iff`)? The COMPOSITE classes are exempt exactly
    as the frontier gate in `NodeCore/Node.lean` exempts them: a
    definition unfold / lambda beta labelled with the ambient geneqv makes
    an R-strength CLAIM about the whole composite, but the replay composes
    its recorded child chain and hard-checks the result, so what it proves
    is the kernel-checked EQUALITY. (Keep in sync with that gate.) -/
def isRStepNode (n : ProofNode) : Bool :=
  let e := nodeEquiv n
  let ty := (runeOf n).ty
  e != "equal" && e != "iff" && ty != "definition" && ty != "lambda-body"

/-- `∃N∀f≥N, eval t = eval t` — the trivial equality part of a node whose
    whole recorded content is a relation fact. -/
def mkIdFuelEq (cfg : ReplayConfig) (t : SExpr) : MetaM Expr := do
  let fn ← withLocalDeclD `f (mkConst ``Nat) fun fV =>
    mkLambdaFVars #[fV]
      (mkApp4 (mkConst ``evalOpt) fV cfg.worldExpr cfg.envExpr (reflectSExpr t))
  mkAppM ``fuel_eq_refl #[fn]

/-! ## The equivalence-rune own-position congruence

    (MOVED here from `Driver/Preprocess.lean` at the G1 lane, 2026-08-14 —
    unchanged; both lanes' collapse now consumes it.) -/

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

/-! ## The shared collapse -/

/-- The R-COLLAPSE at a congruence frame — FACTORED (G1 lane, 2026-08-14)
    out of `replayCongCollapse` so the preprocess chain and the rewriter's
    literal-chain walker share ONE collapse; the lanes differ only in
    where the relation fact came from.

    Given the enclosing frame `parentStep`, the relation `rel`, the
    R-step's sides `a ⇒ b`, and `hR : EvTrue w env (rel a b)`, produce the
    PARENT-level eval-equality `eval (parent[a]) = eval (parent[b])`.
    Two arms, both ANCHORED to the step's own citation (BUG-023 — a
    shape-index match alone would be an INFERENCE: a congruence-shaped
    earlier theorem ACL2 never used as the license could match):
    - the parent application is `rel` ITSELF — no defcong exists for a
      relation's own argument positions; ACL2's geneqv built-in makes the
      :EQUIVALENCE rule the congruence there, and the step cites the
      equivalence rune, so a STEP-CITED `equivfull:` offer supplies the
      defequiv conjuncts (`equivOwnPosCongr`);
    - otherwise a STEP-CITED `(:CONGRUENCE …)` defcong indexed at
      (fn, pos, rel), its whole instance recompute-and-checked.
    R-out is EQUAL in both arms (the equivalence rule's own geneqv entry;
    `congSpecOfFormula?` guards the defcong conclusion) — an R-out ≠ EQUAL
    license has no representation here and simply finds no match, which
    is the frontier below. -/
def collapseAtCongruenceFrame (cfg : ReplayConfig) (ctx : ReplayCtx)
    (what : String) (parentStep : PathStep) (rel : Symbol) (a b : SExpr)
    (hR : Expr) (citedCongs citedEquivs : List String) : MetaM Expr := do
  let relApp : SExpr := .cons (.atom (.symbol rel)) (.cons a (.cons b .nil))
  let parentL := rebuild parentStep a
  let parentR := rebuild parentStep b
  let some pArgs := (match parentL with
      | .cons _ argsS => argsS.toList?
      | _ => none)
    | throwError "{what}: parent {repr parentL} is not an application"
  unless pArgs[parentStep.argIdx]? == some a do
    throwError "{what}: the parent's arg at the rewrite position is not \
        the R-step's lhs (internal)"
  let congMatches := ctx.congHyps.filter fun (c, _) =>
    c.fn == parentStep.fn && c.pos == parentStep.argIdx && c.rel == rel &&
    citedCongs.contains c.name
  if congMatches.isEmpty && parentStep.fn == rel then
    let eqMatches := ctx.equivFullHyps.filter fun (e, _) =>
      e.rel == rel && citedEquivs.contains e.name
    let [(eSpec, eHyp)] := eqMatches
      | throwError "{what}: own-position rewrite under \
          {rel.name} at arg {parentStep.argIdx}: {eqMatches.length} \
          step-cited equivfull hypotheses (need exactly 1; cited \
          equivalence runes {citedEquivs}) (frontier)"
    let [arg0, arg1] := pArgs
      | throwError "{what}: own-position parent {repr parentL} \
          is not a binary application (frontier)"
    let other := if parentStep.argIdx == 0 then arg1 else arg0
    let (valueEq, ctxE) ← equivOwnPosCongr cfg ctx eSpec eHyp a b other
      parentStep.argIdx hR
    return ← mkAppM ``fuel_eq_of_conv
      #[← ctxValProof cfg ctxE parentL, ← ctxValProof cfg ctxE parentR,
        valueEq]
  let [(cSpec, cHyp)] := congMatches
    | throwError "{what}: {congMatches.length} congruence \
        hypotheses match ({parentStep.fn.name} arg {parentStep.argIdx} under \
        {rel.name}) among the step-cited congruence runes \
        {citedCongs} — need exactly 1 (frontier; the offered congruences \
        are R-out = EQUAL only — an R-out ≠ EQUAL licence has no \
        representation and matches nothing here)"
  unless pArgs.length == cSpec.argVars.length do
    throwError "{what}: congruence {cSpec.name} arity \
        {cSpec.argVars.length} ≠ the parent's {pArgs.length}"
  let σcVars := cSpec.argVars ++ [cSpec.vy]
  let σcTerms := pArgs ++ [b]
  -- recompute-and-check the whole instance against the defcong pieces
  unless ACL2.Replay.substTerm σcVars σcTerms cSpec.lhsApp == parentL &&
         ACL2.Replay.substTerm σcVars σcTerms cSpec.rhsApp == parentR &&
         ACL2.Replay.substTerm σcVars σcTerms cSpec.hyp == relApp do
    throwError "{what}: congruence {cSpec.name} instance does \
        not reconstruct the parent applications / the relation fact \
        (frontier)"
  unless (ACL2.Replay.freeVars cSpec.formula).all (σcVars.contains ·) do
    throwError "{what}: congruence {cSpec.name} formula has \
        variables outside its arg/vy set (internal)"
  let (hImp, ctx2) ← instantiateEvTrueHypAt cfg ctx cHyp σcVars σcTerms
    cSpec.formula
  let implyσ := ACL2.Replay.substTerm σcVars σcTerms cSpec.formula
  -- value-level MP + the two-valued EQUAL decode
  let ctx3 ← pinTermOpaques cfg cfg.envExpr ctx2 implyσ
  let hFne ← mkAppM ``ne_nil_of_evtrue_conv
    #[hImp, ← ctxValProof cfg ctx3 implyσ]
  let hvH ← mkAppM ``ne_nil_of_evtrue_conv
    #[hR, ← ctxValProof cfg ctx3 relApp]
  let hvC ← mkAppM ``implies_value_mp #[hFne, hvH]
  let hEq ← mkAppM ``Logic.eq_of_equal_ne_nil #[hvC]
  mkAppM ``fuel_eq_of_conv
    #[← ctxValProof cfg ctx3 parentL, ← ctxValProof cfg ctx3 parentR, hEq]

/-! ## The two recorded sources of an R-fact -/

/-- The R-SOLIDIFY fact: a `rewriting-equivalence` step recorded under a
    USER equivalence R is justified by a clause hypothesis — the
    (post-rewrite) literal `(NOT (R a b))` whose FALSITY in the spine
    branch IS the relation fact.

    This is the EQUAL-headed solidify decode of `NodeCore/Node.lean`
    (which turns a false `(NOT (EQUAL A B))` into the value equality
    `va = vb` via `logic_not_equal_nil_eq`) generalized to an arbitrary
    in-scope equivalence head: under a user R there is no value equality
    to extract, so the decode stops one step earlier — `logic_not_nil_ne`
    on the literal's falsity gives `v(R a b) ≠ nil`, and
    `evtrue_of_conv_ne_nil` at the relation application's pinned value
    gives `EvTrue w env (R a b)`. Nothing about R is assumed; the
    hypothesis is the clause's own literal.

    Only the `.literal` equivalence source is replayed — a branch-test /
    segment / type-set-derived R-hypothesis is a named frontier. -/
def solidifyRFact (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode) :
    MetaM (Symbol × SExpr × SExpr × Expr) := do
  let (lhs, rhs) := nodeLhsRhs n
  let .node _ _ _ _ prov := n
  let some eqTerm := prov.equivTerm
    | throwError "R-solidify: step under {prov.equiv} has no :EQUIV-TERM \
        (emission gap)"
  let .cons (.atom (.symbol rel)) (.cons a (.cons b .nil)) := eqTerm
    | throwError "R-solidify: :EQUIV-TERM {repr eqTerm} is not a binary \
        relation application (frontier)"
  unless (rel.name.map Char.toLower) == prov.equiv do
    throwError "R-solidify: :EQUIV-TERM head {rel.name} ≠ the step's \
        :EQUIV {prov.equiv} (emission divergence)"
  unless a == lhs && b == rhs do
    throwError "R-solidify: :EQUIV-TERM ({repr a} , {repr b}) does not name \
        the step's own sides ({repr lhs} ⇒ {repr rhs}) — the R lane \
        replays the recorded orientation only (frontier)"
  let some src := prov.equivSource
    | throwError "R-solidify: node has no equivSource (unlinked \
        rewriting-equivalence under {prov.equiv})"
  let .literal idx := src
    | throwError "R-solidify: equivalence source {repr src} under \
        {prov.equiv} — only a clause LITERAL hypothesis is replayed \
        (frontier)"
  let some (litTerm, hNil) := ctx.litFact? idx
    | throwError "R-solidify: no spine fact for literal {idx} (clause \
        context missing)"
  let expected : SExpr := .cons (.atom (.symbol { name := "NOT" }))
    (.cons eqTerm .nil)
  unless litTerm == expected do
    throwError "R-solidify: source literal {repr litTerm} is not \
        (not {repr eqTerm}) (frontier)"
  let vR ← ctxValExpr cfg ctx eqTerm
  -- hNil : Logic.not v(R a b) = nil  ⇒  v(R a b) ≠ nil  ⇒  EvTrue (R a b)
  let hNe ← mkAppM ``logic_not_nil_ne #[vR, hNil]
  let hR ← mkAppM ``evtrue_of_conv_ne_nil
    #[← ctxValProof cfg ctx eqTerm, hNe]
  pure (rel, a, b, hR)

/-- The R-RULE fact: a step that APPLIED a stored rule whose `:EQUIV` is a
    user equivalence R. The rule's own replayed statement (the
    interpreted-relation shape, the `rule:<thm>` hypothesis) instantiated
    by the step's emitted `:SUBST` gives `EvTrue w env (R lhsσ rhsσ)`,
    with `lhsσ`/`rhsσ` recompute-checked against the step's recorded
    sides. Hyp-bearing rules and ambiguous stored-rule matches are loud
    frontiers. (FACTORED out of `replayCongCollapse`, 2026-08-14.) -/
def ruleRFact (cfg : ReplayConfig) (ctx : ReplayCtx) (what : String)
    (n : ProofNode) : MetaM (Symbol × SExpr × SExpr × Expr × ReplayCtx) := do
  let (lhs, rhs) := nodeLhsRhs n
  let .node _ _ _ _ prov := n
  let rune := runeOf n
  let σvars ← prov.subst.mapM fun (v, _) => do
    let .atom (.symbol s) := v
      | throwError "{what}: :SUBST binds a non-variable {repr v}"
    pure s
  let σterms := prov.subst.map (·.2)
  let candidates := ctx.ruleHyps.filter fun (r, _) =>
    r.name == rune.name && r.idx == rune.idx && r.equiv == prov.equiv
  if candidates.isEmpty then
    throwError "{what}: rule {rune.name} (equiv {prov.equiv}): no \
        stored-rule hypothesis in scope (no (:RULES …) entry — emission gap \
        or missing telescope)"
  let matched := candidates.filter fun (r, _) =>
    ACL2.Replay.substTerm σvars σterms r.lhs == lhs
  let (spec, hypV) ← match matched with
    | [m] => pure m
    | m :: restM =>
      if restM.all (fun (r, _) => r == m.1) then pure m
      else throwError "{what}: rule {rune.name}: \
          {matched.length} DISTINCT stored rules match (need exactly 1)"
    | [] => throwError "{what}: rule {rune.name}: 0 stored rules \
        match substTerm(:SUBST, lhs) == {repr lhs}"
  unless spec.hyps.isEmpty do
    throwError "{what}: rule {rune.name} carries \
        {spec.hyps.length} hyps (frontier — hyp-free R-rules only)"
  unless ACL2.Replay.substTerm σvars σterms spec.rhs == rhs do
    throwError "{what}: rule {rune.name}: node rhs {repr rhs} ≠ \
        substTerm(:SUBST, rule rhs {repr spec.rhs}) (emission gap)"
  let ruleFrees := ACL2.Replay.freeVars spec.lhs ++ ACL2.Replay.freeVars spec.rhs
  for s in ruleFrees do
    unless σvars.contains s do
      throwError "{what}: rule {rune.name}: rule variable \
          {s.name} not bound by the emitted :SUBST (emission gap)"
  -- the interpreted-relation instance: EvTrue env (R lhsσ rhsσ)
  let rSym : Symbol := { name := spec.equiv.map Char.toUpper }
  let relApp : SExpr := .cons (.atom (.symbol rSym))
    (.cons spec.lhs (.cons spec.rhs .nil))
  let (hRel, ctx1) ← instantiateEvTrueHypAt cfg ctx hypV σvars σterms relApp
  pure (rSym, lhs, rhs, hRel, ctx1)

/-- The R-fact of an R-STEP node, dispatched on the recorded rune class:
    a `rewriting-equivalence` solidify is justified by a clause literal,
    anything else by the stored rule it applied.

    NOTE (unexercised path): the rule arm's returned ctx carries the
    instantiation's opaque PINS, and `replayNodeR` cannot thread them out
    through `NodeRec.node` — so a rule-sourced R-fact whose pins the
    collapse does not itself re-derive will hard-fail there on a value
    mismatch (fail-closed, never silent). No corpus record reaches it:
    the only class-D book (`cov-cong-consume`) stops earlier at the
    SYNP-guarded-rule frontier. Thread the ctx when one does. -/
def rStepFact (cfg : ReplayConfig) (ctx : ReplayCtx) (what : String)
    (n : ProofNode) : MetaM (Symbol × SExpr × SExpr × Expr × ReplayCtx) := do
  if (runeOf n).ty == "rewriting-equivalence" then
    let (rel, a, b, hR) ← solidifyRFact cfg ctx n
    pure (rel, a, b, hR, ctx)
  else
    ruleRFact cfg ctx what n

/-! ## The node dispatcher that carries the payload out -/

/-- The per-node dispatcher WITH the R-payload (option M). Two recorded
    shapes carry one (the whole corpus census, brief §1.2):

    - the node's OWN step is under R (class D — a with-lemma R-rule in a
      literal chain, or a solidify reached at a chain root): its equality
      content is nil, so the returned `Expr` is reflexivity at the node's
      lhs and the payload is the whole step;
    - the node's recorded RHS BLOCK ENDS in an R-step (class C —
      PERM-TLFIX's `CDR-CONS` whose rhs continuation is the
      IH solidify under `perm`): the node's recorded chain SPLITS at that
      step. The equality part is the same node with its rhs read at the
      split point (the R-step's own recorded lhs) and the R-step dropped
      from its children — a projection of the recorded node, replayed by
      the ordinary recipe, which still hard-checks that its chain reaches
      the split point. The R-step is the payload.

    Everything else routes to `replayNodeWith` unchanged, and every R-step
    the two shapes do not cover still meets that dispatcher's frontier
    gate — fail-closed. -/
partial def replayNodeR (rec : NodeRec) (cfg : ReplayConfig) (ctx : ReplayCtx)
    (n : ProofNode) : MetaM (Expr × Option RPayload) := do
  let .node rune lhs rhs children prov := n
  let rKids := children.filter isRStepNode
  if isRStepNode n then
    unless rKids.isEmpty do
      throwError "R-step: {rune.tag} under {prov.equiv} also has \
          {rKids.length} R-step child(ren) — two composed R-steps in one \
          node (frontier)"
    unless children.isEmpty do
      throwError "R-step: {rune.tag} under {prov.equiv} has \
          {children.length} children (frontier — hyp-free R-steps only)"
    let (rel, a, b, hR, _) ← rStepFact cfg ctx "R-step" n
    return (← mkIdFuelEq cfg lhs, some ⟨rel, a, b, hR⟩)
  match rKids with
  | [] => return (← replayNodeWith rec cfg ctx n, none)
  | [k] =>
    let (kl, kr) := nodeLhsRhs k
    -- the sole R-step child must be the block's LAST node (with exactly
    -- one R kid, "the last child is an R-step" says exactly that)
    unless (children.getLast?.map isRStepNode) == some true do
      throwError "R-block: {rune.tag}'s R-step ({(runeOf k).tag} under \
          {nodeEquiv k}) is not the FINAL step of its rhs block \
          (frontier)"
    unless innerKindOf k == "rhs" do
      throwError "R-block: {rune.tag}'s R-step arrived in block kind \
          '{innerKindOf k}', not the rule's RHS continuation (frontier)"
    unless kr == rhs do
      throwError "R-block: {rune.tag}'s R-step ends at {repr kr}, the \
          node's recorded rhs is {repr rhs} (frontier)"
    let (rel, a, b, hR, _) ← rStepFact cfg ctx "R-block" k
    -- the equality part: the SAME recorded node read up to the split
    let (e, inner?) ←
      replayNodeR rec cfg ctx (.node rune lhs kl children.dropLast prov)
    unless inner?.isNone do
      throwError "R-block: internal — the split node produced a second \
          R payload"
    return (e, some ⟨rel, a, b, hR⟩)
  | _ =>
    throwError "R-block: {rune.tag} has {rKids.length} R-step children — \
        two composed R-steps (frontier)"

/-- Replay a node where ONLY an eval-equality composes — every consumer
    that has no congruence frame to collapse an `RPayload` at. A payload
    here means the recorded step is not an equality at all, so the
    composition would be unsound: name the frontier instead. -/
def recNodeEq (rec : NodeRec) (cfg : ReplayConfig) (ctx : ReplayCtx)
    (n : ProofNode) (site : String) : MetaM Expr := do
  let (e, pay?) ← rec.node cfg ctx n
  if let some pay := pay? then
    throwError "{site}: node {(runeOf n).tag} carries an R payload under \
        {pay.rel.name} — this site composes eval-equalities only, and the \
        R-collapse has no congruence frame here (frontier)"
  pure e

/-- The walker's R-COLLAPSE (option M): a chain node that produced an
    `RPayload` is lifted by collapsing the payload at the node's OWN
    innermost congruence frame — the position ACL2's `:PATH` records —
    after which everything outward composes as ordinary equality.

    Composition, mirroring the node's recorded content 1:1:
    1. `nodeEq : eval lhs = eval a` — the node's equality part (the rule
       instance plus whatever of its rhs block preceded the R-step);
    2. lifted through the congruence frame by ordinary congruence, giving
       `eval parent[lhs] = eval parent[a]`;
    3. `collapseAtCongruenceFrame` turns the relation fact into
       `eval parent[a] = eval parent[b]`;
    4. (2)∘(3), then the REMAINING frames outward as usual.

    The licence anchor is the node's own emitted citation: `:GENEQV` must
    NAME the relation (fail-closed — the honest net-step relation, which
    the rule's own `:EQUIV` under-reports at exactly this shape), and the
    step's `:RUNES` must cite the `(:EQUIVALENCE …)` / `(:CONGRUENCE …)`
    licence. That rune set is the step's CUMULATIVE ttree (see
    `StepProvenance.runes`) — a weaker anchor than a per-step
    `:CR-RUNE` would be; emitting one at `find-rewriting-equivalence`'s
    push site is the queued tightening (brief §Q2), not a prerequisite. -/
def replayRCollapse (cfg : ReplayConfig) (ctx : ReplayCtx) (start : SExpr)
    (n : ProofNode) (nodeEq : Expr) (pay : RPayload) :
    MetaM (Expr × SExpr) := do
  let (lhs, rhs) := nodeLhsRhs n
  let what := "replayRewrites: R-collapse"
  match nodeGeneqv n with
  | [g] =>
    unless g == (pay.rel.name.map Char.toLower) do
      throwError "{what}: the step's :GENEQV ({g}) does not name the \
          R-step's relation {pay.rel.name} — the emitted ambient \
          equivalence does not licence this collapse (frontier)"
  | [] =>
    throwError "{what}: the step under {pay.rel.name} carries NO :GENEQV — \
        the ambient equivalence that licences the R-step is unrecorded \
        (emission gap; recapture with the R-lane emission)"
  | gq =>
    throwError "{what}: MULTI-ELEMENT :GENEQV {gq} — a generated \
        equivalence of ≥2 relations is not replayed (frontier)"
  unless pay.b == rhs do
    throwError "{what}: the R-step's rhs {repr pay.b} is not the node's \
        recorded rhs {repr rhs} (frontier)"
  let steps ← ofExcept
    (pathStepsFromFrames start (relativizeFrames (nodePath n)) lhs)
  let some parentStep := steps.getLast?
    | throwError "{what}: the R-step's node sits at the chain ROOT — no \
        congruence frame to collapse at (frontier — an R payload that must \
        cross more than one frame)"
  let citedCongs := (nodeRunes n).filterMap
    (fun r => if r.ty == "congruence" then some r.name else none)
  let citedEquivs := (nodeRunes n).filterMap
    (fun r => if r.ty == "equivalence" then some r.name else none)
  let inner0 ← applyStep cfg.worldExpr cfg.envExpr parentStep lhs pay.a nodeEq
  let congEq ← collapseAtCongruenceFrame cfg ctx what parentStep pay.rel
    pay.a pay.b pay.hR citedCongs citedEquivs
  let mut inner ← mkAppM ``fuel_chain_eq #[inner0, congEq]
  let mut curL := rebuild parentStep lhs
  let mut curR := rebuild parentStep rhs
  for st in steps.dropLast.reverse do
    inner ← applyStep cfg.worldExpr cfg.envExpr st curL curR inner
    curL := rebuild st curL
    curR := rebuild st curR
  unless curL == start do
    throwError "{what}: lift reconstructed {repr curL} ≠ running \
        {repr start}"
  pure (inner, curR)

end ACL2.Replay.Driver
