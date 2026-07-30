/-
  Driver/Preprocess — split from the monolithic Driver.lean (WP2 Stage 1,
  2026-07-17; see docs/plans/2026-07-18_driver-modular-refactor.md).

  Preprocess-chain replay and the clausify bridge (#53C).
-/
import ACL2Lean.Replay.Driver.Totality

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
  | _ => replayNode cfg ctx n 0

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

/-- Replay a preprocess chain's CORE: the composed relation between the
    formula and the final term — `(proof, isIff)` where the proof is the
    eval-equality `∃N∀f≥N, eval formula = eval final` when `isIff = false`,
    and `EvRel SIff w env formula final` when any step was IFF-only
    (`isIff = true`). `none` for an empty chain. R is threaded per the
    binding invariant L2: equal steps inject into the iff composite by
    refinement (`evrel_of_fuel_eq` + `siff_refl`). -/
def replayPreprocessChainCore (cfg : ReplayConfig) (ctx : ReplayCtx)
    (formula : SExpr) (nodes : List ProofNode) :
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
    let nodeP ←
      if isDischarge then do
        unless rhs == quoteT do
          throwError "discharge node: rhs {repr rhs} ≠ (quote t)"
        let ev ← replayDischargeNode cfg ctx lhs
        mkAppM ``evrel_siff_qt_of_evtrue #[ev]
      else if isIffNode then replayIfIffNode cfg ctx n
      else replayPreprocessNode cfg ctx n
    let path ←
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
        match findOccurrences cur lhs with
        | [p] => pure p
        | [] => throwError "replayPreprocessChain: node lhs {repr lhs} does not occur \
                            in the current term {repr cur}"
        | ps => throwError "replayPreprocessChain: node lhs {repr lhs} occurs \
                            {ps.length} times in {repr cur} — ambiguous position \
                            (needs :PATH emission at the preprocess site)"
      else
        -- the EMITTED :PATH (abbreviation-expansion frames, rooted at the
        -- formula this chain walks — infra/abbrev-path in the fork):
        -- navigate and VERIFY the redex; required when the lhs occurs more
        -- than once (msort HOW-MANY-MSORT's twice-occurring (ODDS X))
        match pathStepsFromFrames cur prov.path lhs with
        | .ok p => pure p
        | .error e => throwError "replayPreprocessChain: emitted :PATH does \
            not navigate to the redex {repr lhs}: {e}"
    -- lift innermost-out; iff payloads use the R congruence table and may
    -- COLLAPSE to an eval-equality at an if-test position
    let mut inner := nodeP
    let mut innerIff := isIffNode
    let mut curL := lhs
    let mut curR := rhs
    for st in path.reverse do
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
    (formula : SExpr) (nodes : List ProofNode) : MetaM Expr := do
  let (acc, cur) ← replayPreprocessChainCore cfg ctx formula nodes
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

/-- The CHECKED expansion walk for one clausify pass (expand-and-or plan
    S3): every recorded firing must be REGISTRY-SHAPED (NOT/ENDP/ATOM
    def-body expansions with the exact emitted if-form target — anything
    else is the S4 lemma-arm frontier) and fully consumed by `expandTerm`.
    Returns the expanded term t′ and the PROOF
    `dpLiftF vars opq t′ = dpLiftF vars opq input` (via the per-builtin
    registry lemmas + `expandTerm_liftEq`, with the walk itself
    kernel-decided). `none` expansions short-circuit to (input, rfl-free). -/
def runCheckedExpand (b : DpLiftBundle) (hwf : Expr)
    (exps : List ClausifyExpansion) (input : SExpr) (pos : Bool) :
    MetaM (SExpr × Option Expr) := do
  if exps.isEmpty then return (input, none)
  -- registry shape validation (value-level, fail-closed)
  let mkIfT (c : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := "IF" }))
      (.cons c (.cons quoteNil (.cons quoteT .nil)))
  let mkConspT (x : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := "CONSP" })) (.cons x .nil)
  for e in exps do
    match e.fromTerm with
    | .cons (.atom (.symbol h)) (.cons x .nil) =>
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
    | _ =>
      throwError "runCheckedExpand: expansion FROM {repr e.fromTerm} is not \
          a unary application (frontier)"
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
    let .cons (.atom (.symbol h)) (.cons x .nil) := e.fromTerm
      | throwError "runCheckedExpand: internal — shape re-check"
    let lem :=
      if h.name == "NOT" then ``dpLiftF_not_expand
      else if h.name == "ENDP" then ``dpLiftF_endp_expand
      else ``dpLiftF_atom_expand
    mkAppOptM lem #[some b.varsE, some b.opqE, some hwf, some (reflectSExpr x)]
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
  -- TAUTOLOGY-DROPPED record (G1 inc-2c): if-interp folded the split
  -- clause's complementary pair to a 'T literal (the record shows ['T]) and
  -- remove-trivial-clauses dropped the output; the recompute keeps the full
  -- clause. Accepted with the taut relaxation — the proof is built OVER THE
  -- RECOMPUTED clause from its complementary pair below (the same
  -- tautologyp reasoning ACL2 used).
  let tautHit := tautDropped && info.out == [] && cl0 == [quoteT]
  unless recomputedSplit == cl0 || dedupHit || tautHit do
    throwError "clausify bridge: recomputed split clause \
                {repr recomputedSplit} ≠ recorded {repr cl0} \
                (divergence: an unregistered expansion, disjoin-clauses \
                literal merging, or an unmirrored dumb-negate-lit arm)"
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
  let prfT' ← mkAppM
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
  let negRecomputed := clausifyPure info.input false
  unless negRecomputed == info.negClause do
    throwError "clausify multi-bridge: recomputed neg-clause                 {repr negRecomputed} ≠ recorded {repr info.negClause}"
  unless info.splits.length == info.negClause.length &&
         pOuts.length == info.out.length &&
         info.out == info.splits.map (·.2) do
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
  for ((l, ((lit, cl), pOut)), k) in
      (info.negClause.zip (info.splits.zip pOuts)).zipIdx do
    let expsK := (info.splitExpands.filter (·.1 == k)).map (·.2)
    let (lit', heqK?) ← runCheckedExpand b hwf expsK lit true
    unless clausifyPure lit' true == cl do
      throwError "clausify multi-bridge: recomputed split clause for                   {repr lit'} ≠ recorded {repr cl}"
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
