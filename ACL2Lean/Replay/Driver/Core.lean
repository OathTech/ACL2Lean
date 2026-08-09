/-
  Driver/CoreSpine + Core — positional slice split of the former Core
  monolith (Phase 3 re-slice, 2026-08-08: Core regrew past its
  shrink-only baseline with the R7b FI arm; MOVE-ONLY — CoreSpine keeps
  the file head (replaceTermOcc + replayClauseSpineWith), Core keeps
  replayClauseWith + the recursion knot. The two big defs recurse
  through the `rec : ClauseRec` parameter, so the cut is at a plain
  def boundary).
-/
import ACL2Lean.Replay.Driver.CoreSpine

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- Replay a clause node: prove `EvTrue w env (disjoinTerm inputClause)`
    (for a single-literal clause this IS the literal/formula statement).
    Induction nodes hard-fail (the scaffold lands next); a pushed clause delegates
    to its pool-root child when the clauses coincide. -/
partial def replayClauseWith (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (cn : ClauseNode) : MetaM Expr := do
  -- never-silently-skip (R7a audit F4, the F12 class): a :USE-HINT
  -- payload is consumed ONLY by the apply-top-hints arm (the no-clausify
  -- branch below) — any node routed to another processor arm with a
  -- payload aboard must hard-fail, not drop it.
  let hasUseHint := (cn.steps.flatMap (·.items)).any fun
    | .useHint .. => true | _ => false
  let guardNoUseHint (arm : String) : MetaM Unit := do
    if hasUseHint then
      throwError "replayClause: a :USE-HINT payload on a {arm} node at \
                  {cn.idStr} (frontier — the payload would be dropped)"
  if cn.induction.isSome then
    guardNoUseHint "induction"
    return ← replayInduction rec cfg ctx cn
  -- EFFECTIVE clausify records: clausify-input emits its checkpoints on every
  -- preprocess pass, including 'miss passes (whose events flush into the NEXT
  -- step's :REWRITES) and identity re-clausifications — a record whose single
  -- output clause disjoins back to exactly its input, or whose input is the
  -- trivially-true `(quote t)` with an EMPTY output set, certifies that the
  -- pass changed nothing the replay must mirror.
  let isNoopClausify : ClausifyInfo → Bool := fun i =>
    -- DETAIL-emptiness (fold-back audit F5b, refined): a noop-SHAPED record
    -- whose expansions carry recorded DETAIL steps must NOT be filtered —
    -- filtering would take the detail out of the pipeline entirely,
    -- bypassing runCheckedExpand's never-ignore guard. Plain registry
    -- expansions on a net-zero record ARE still filtered: the walk has no
    -- net effect on the output clause (the long-validated pre-2e behavior —
    -- the auditor's blanket expansion-emptiness variant regressed 34 sweep
    -- rows, every trivial clausify carrying a NOT/ENDP registry expansion).
    (i.negExpands ++ i.splitExpands.map (·.2)).all (·.detail.isEmpty) &&
    match i.out with
    | [cl] => disjoinTerm cl == i.input
    | [] => i.input == quoteT
    | _ => false
  let clausifyInfos := ((cn.steps.flatMap (·.items)).filterMap fun
    | .clausify i => some i | _ => none).filter (fun i => !(isNoopClausify i))
  -- a push-clause node defers to its pool-root child (same clause) — UNLESS an
  -- effective clausify record changed the clause first (the clausify path
  -- below replays the chain + split and consumes the child itself)
  if clausifyInfos.isEmpty && cn.steps.any (fun s => s.processor.toLower == "push-clause") then
    guardNoUseHint "push-clause"
    match cn.children with
    | [child] =>
      unless child.inputClause == cn.inputClause do
        throwError "replayClause: pushed clause ≠ pool-root clause at {cn.idStr}"
      return ← replayClauseWith rec cfg ctx child
    | _ => throwError "replayClause: push-clause with {cn.children.length} children at {cn.idStr}"
  -- a POOL-SUBSUMED root (synthetic; from (:POOL-SUBSUMED …)): its clause is
  -- an instance-superset of the MORE GENERAL pool root attached as its child
  if cn.steps.any (fun s => s.processor.toLower == "pool-subsumed") then
    guardNoUseHint "pool-subsumed"
    return ← replaySubsumed rec cfg ctx cn
  -- a DESTRUCTOR-ELIMINATION node: the child clause is over the elim's fresh
  -- variables; replayElim bridges it back through the emitted ELIMSEQUENCE
  if let some st := cn.steps.find? (fun s => s.processor.toLower == "eliminate-destructors-clause") then
    guardNoUseHint "eliminate-destructors"
    unless clausifyInfos.isEmpty do
      throwError "replayClause: elim step alongside an effective clausify \
                  record at {cn.idStr} (frontier)"
    return ← replayElim rec cfg ctx cn st
  -- a FERTILIZE node (cross-fertilization): the emitted :FERTILIZE detail
  -- links the substitution to its justifying clause literal; replayFertilize
  -- byCases the literal, transports the disjunction onto the substituted
  -- clause, and closes via the child (emission arc, 2026-07-21). The step's
  -- items are the PRECEDING simplify miss's flushed events — not this
  -- transformation's record — and are deliberately not consumed.
  if let some st := cn.steps.find? (fun s => s.processor.toLower == "fertilize-clause") then
    guardNoUseHint "fertilize"
    unless clausifyInfos.isEmpty do
      throwError "replayClause: fertilize step alongside an effective \
                  clausify record at {cn.idStr} (frontier)"
    return ← replayFertilize rec cfg ctx cn st
  -- a GENERALIZE node: the child clause abstracts the emitted :TERMS by fresh
  -- :VARS; replayGeneralize replays the child at the env binding the fresh
  -- vars to the terms' values and substN-bridges back
  if let some st := cn.steps.find? (fun s => s.processor.toLower == "generalize-clause") then
    guardNoUseHint "generalize"
    unless clausifyInfos.isEmpty do
      throwError "replayClause: generalize step alongside an effective \
                  clausify record at {cn.idStr} (frontier)"
    return ← replayGeneralize rec cfg ctx cn st
  -- an ELIMINATE-IRRELEVANCE node: the child clause is an order-preserving
  -- SUBSET of this clause (irrelevant literals dropped) — the child's truth
  -- closes the parent disjunction through whichever literal is truthy
  if cn.steps.any (fun s => s.processor.toLower == "eliminate-irrelevance-clause") then
    guardNoUseHint "eliminate-irrelevance"
    unless clausifyInfos.isEmpty do
      throwError "replayClause: eliminate-irrelevance step alongside an \
                  effective clausify record at {cn.idStr} (frontier)"
    return ← replayEliminateIrrelevance rec cfg ctx cn
  -- pin every user-fn application in this clause's subtree from the totality/TP
  -- hypotheses (idempotent — already-pinned terms are skipped), so the value
  -- layer can lift opaque subterms under a quantified env
  let mut ctx := ctx
  for tm in (clauseSubtreeTerms cn).eraseDups do
    ctx ← pinTermOpaques cfg cfg.envExpr ctx tm
  -- the clause's emitted FC-derivation records enter the ctx here
  -- (final-closeout item C): clause DATA, consumed by the
  -- marker-relief arm's fc-derivations anchor — never a spine step
  ctx := { ctx with fcDerivs := ctx.fcDerivs ++
    ((cn.steps.flatMap (·.items)).filterMap
      (fun | .fcDerivations d => some d | _ => none)).flatten }
  let lits := flattenLiterals (cn.steps.flatMap (·.items))
  -- a preprocess CLAUSIFY split: chain to the recorded input, bridge the proved
  -- output clause (the pushed/pool-root child) back through the if-recursion
  match clausifyInfos with
  | [info] =>
    -- never-silently-skip (fold-back audit F12): a :USE-HINT payload on a
    -- clausify-bearing node was DISCARDED here (useHints is consumed only
    -- by the no-clausify arm), and the constraint chain then walked the
    -- GOAL — failing only incidentally on an lhs mismatch
    -- (BSORT-IS-ISORT). Hard-fail precisely: the composition (constraint
    -- chain on CONSTRAINT-CL, clausify on the application side) is the R7
    -- work.
    let useHs := (cn.steps.flatMap (·.items)).filterMap fun
      | .useHint h c a l => some (h, c, a, l) | _ => none
    unless useHs.isEmpty do
      throwError "replayClause: a :USE-HINT payload alongside an effective \
          clausify record at {cn.idStr} — the useHint/clausify composition \
          awaits functional-instantiation/:use soundness (R7 frontier; the \
          constraint chain must walk CONSTRAINT-CL, not the goal)"
    -- literal items on the same (merged) node: from a PUSH step's
    -- per-literal scan they are identity displays only; from a merged
    -- SAME-CLAUSE-ID SIMPLIFY step they are the REAL walk of a clausify
    -- output clause (CLASSIFY-POS shape) — consumed below via the spine.
    -- The identity guard applies only when nothing consumes them.
    -- steps BEFORE the clausify record chain the formula to its input; steps
    -- AFTER it discharge dropped output clauses (tau/type-set verdicts on
    -- trivially-true conjuncts — the ratified DP carve-out)
    let allItems := cn.steps.flatMap (·.items)
    let clausifyIdx := allItems.findIdx (fun | .clausify _ => true | _ => false)
    let preSteps := (allItems.take clausifyIdx).filterMap fun
      | .step n => some n | _ => none
    let postSteps := (allItems.drop (clausifyIdx + 1)).filterMap fun
      | .step n => some n | _ => none
    -- the formula is the clause's DISJUNCTION; for a multi-literal clause the
    -- preprocess steps rewrite individual literals, lifted into the disjunction
    -- by path-directed congruence (including the lazy `if`'s then/else branches,
    -- sound here because each step's eval-equality is unconditional)
    let formula := disjoinTerm cn.inputClause
    let (chainOpt, finalT) ← replayPreprocessChainCore cfg ctx formula preSteps
      ((cn.steps.flatMap (·.runes)).filterMap
        (fun r => if r.ty == "congruence" then some r.name else none))
      ((cn.steps.flatMap (·.runes)).filterMap
        (fun r => if r.ty == "equivalence" then some r.name else none))
    unless finalT == info.input do
      throwError "replayClause: preprocess chain reached {repr finalT}, the \
                  clausify input is {repr info.input}"
    -- one proof per output clause: a CHILD subgoal, or a post-clausify
    -- DISCHARGE node on a singleton clause
    let mut usedChildren : List String := []
    let mut pOuts : List Expr := []
    let mut spineConsumed := false
    for cl in info.out do
      match cn.children.find? (·.inputClause == cl) with
      | some child =>
        usedChildren := usedChildren ++ [child.idStr]
        -- litFacts are INDEX-keyed and clause-scoped — clear at every
        -- child-CLAUSE descent (stale parent entries collide with the
        -- child's numbering); term-keyed channels flow through
        pOuts := pOuts ++ [← replayClauseWith rec cfg { ctx with litFacts := [] } child]
      | none =>
        -- (a) the out clause proved IN-NODE by a merged same-clause-id
        -- SIMPLIFY step's literal walk (preprocess split + simplify without
        -- an intervening push — CLASSIFY-POS shape): route the post-clausify
        -- items through the SPINE walker (itself fail-closed per literal)
        let postItems := (allItems.drop (clausifyIdx + 1)).filter fun
          | .clausify i => !(isNoopClausify i)
          | _ => true
        let hasWalk := postItems.any fun | .literal _ => true | _ => false
        if hasWalk && info.out.length == 1 then
          let litsIdx := cl.zipIdx.map fun (l, i) => (i + 1, l)
          spineConsumed := true
          pOuts := pOuts ++ [← replayClauseSpineWith rec cfg
            { ctx with litFacts := [] } cn.idStr litsIdx postItems [] cn.children]
        else
        -- (b') a MULTI-literal clause discharged WHOLE by a verdict node on
        -- its disjunction (LINEAR-CHAIN's linear-arithmetic Goal; the
        -- ratified DP carve-out — replayDischargeNode splits the spine)
        if cl.length > 1 then
          let dTerm := disjoinTerm cl
          let some n := postSteps.find? (fun n =>
              dischargeOrigins.contains (nodeOrigin n) && (nodeLhsRhs n).1 == dTerm)
            | throwError "replayClause: clausify output {repr cl} has no child \
                          subgoal, no in-node walk, and no whole-clause \
                          discharge node at {cn.idStr} (frontier)"
          unless (nodeLhsRhs n).2 == quoteT do
            throwError "replayClause: whole-clause discharge node rhs \
                        {repr (nodeLhsRhs n).2} ≠ (quote t) at {cn.idStr}"
          pOuts := pOuts ++ [← replayDischargeNode cfg ctx dTerm]
        else do
        -- (b) a singleton clause discharged by a post-clausify verdict node
        -- (the ratified DP carve-out)
        let [lit] := cl
          | throwError "replayClause: clausify output {repr cl} has no child \
                        subgoal and is not a singleton dischargeable clause \
                        at {cn.idStr} (frontier)"
        let some n := postSteps.find? (fun n =>
            dischargeOrigins.contains (nodeOrigin n) && (nodeLhsRhs n).1 == lit)
          | throwError "replayClause: clausify output {repr cl} has no child \
                        subgoal and no post-clausify discharge node at \
                        {cn.idStr} (emission gap)"
        unless (nodeLhsRhs n).2 == quoteT do
          throwError "replayClause: discharge node for {repr lit} has rhs \
                      {repr (nodeLhsRhs n).2} ≠ (quote t) at {cn.idStr}"
        pOuts := pOuts ++ [← replayDischargeNode cfg ctx lit]
    -- when NOTHING consumed the literal items (the push-scan case), they
    -- must be identity displays — real rewriting there is a frontier
    unless spineConsumed do
      for (_, lp) in lits do
        unless lp.nodes.isEmpty && lp.result == lp.literal do
          throwError "replayClause: non-identity literal item alongside a \
                      clausify record at {cn.idStr} (frontier): {repr lp.literal}"
    -- the SPINE route consumes children itself (residual pushes,
    -- fail-closed inside); the completeness check applies otherwise
    unless spineConsumed do
      for child in cn.children do
        unless usedChildren.contains child.idStr do
          throwError "replayClause: child {child.idStr} matches no clausify \
                      output at {cn.idStr} (linking gap)"
    let pInput ←
      match pOuts with
      | [pOut] =>
        if info.out.length == 1 then bridgeClausify cfg ctx info (some pOut)
        else bridgeClausifyMulti cfg ctx info pOuts
      | [] =>
        -- TAUTOLOGY-DROPPED output (G1 inc-2c, p3-conj *1/2.4.2): ACL2's
        -- remove-trivial-clauses dropped the single split clause (if-interp
        -- folded its complementary pair to 'T) — :CLAUSIFY-OUT is honestly
        -- empty and the clause is PROVED. The bridge builds the tautology
        -- proof over its own recomputed split clause.
        if info.out.isEmpty then
          bridgeClausify cfg ctx info none (tautDropped := true)
        else bridgeClausifyMulti cfg ctx info pOuts
      | _ => bridgeClausifyMulti cfg ctx info pOuts
    match chainOpt with
    | none => return pInput
    | some (ch, false) => return ← mkAppM ``evtrue_of_fuel_eq #[ch, pInput]
    | some (ch, true) => return ← mkAppM ``evtrue_of_evrel_siff #[ch, pInput]
  | _ :: _ :: _ =>
    throwError "replayClause: multiple clausify records at {cn.idStr} (frontier)"
  | [] =>
  let stepNodes := (cn.steps.flatMap (·.items)).filterMap fun
    | .step n => some n | _ => none
  -- :USE hint (apply-top-hints-clause; sorts-equivalent Class B): the
  -- step's rewrite chain walks the emitted CONSTRAINT-CL — the
  -- instantiation obligations — not the goal clause (the fork's
  -- emit/use-hint payload carries the chain's true root). Validate the
  -- recorded chain composes constraint-cl to 't, then stop at the honest
  -- frontier: adding the instantiated lemma as a hypothesis is
  -- functional-instantiation/:use soundness (R7 — the following arc).
  let useHints := (cn.steps.flatMap (·.items)).filterMap fun
    | .useHint h c a l => some (h, c, a, l) | _ => none
  -- never-silently-skip (R7a audit F3, the F12 class): a node with
  -- SEVERAL payloads must not fall through to the ordinary arms below
  -- (they would chain against the goal with an unrelated failure), and
  -- literal items alongside the payload have no consumer in this arm.
  if useHints.length > 1 then
    throwError "replayClause: {useHints.length} :USE-HINT payloads at \
                {cn.idStr} (frontier — one payload per apply-top-hints \
                node)"
  if let [(hyps, constraintCl, appClauses, lmis)] := useHints then
    unless lits.isEmpty do
      throwError "use-hint: literal items alongside the :USE-HINT payload \
                  at {cn.idStr} (frontier — no consumer in this arm)"
    -- PLAIN :use (R7a, close-out Phase 2): the recorded chain walks the
    -- emitted CONSTRAINT-CL (trivial `('T)` for a plain :use — a
    -- NON-trivial constraint clause is a functional instance, R7b); each
    -- `:LMI-LST` instance's truth comes from the cited theorem's
    -- whole-formula replayed statement (`use:` hypothesis) transported
    -- under the lmi's σ (`instantiateEvTrueHypAt`), recompute-checked
    -- against the emitted `:HYPS` entry; the application clause
    -- `(¬L₁ … ¬Lₙ G-lits)` is proved by its child subgoal and each `¬Lᵢ`
    -- head is peeled along `Lᵢ`'s truthiness (`evtrue_extract_else`) —
    -- exactly ACL2's apply-top-hints-clause composition, read off the
    -- emission with every piece cross-checked.
    let cFormula := disjoinTerm constraintCl
    let (chainOpt, finalT) ← replayPreprocessChainCore cfg ctx cFormula stepNodes
      ((cn.steps.flatMap (·.runes)).filterMap
        (fun r => if r.ty == "congruence" then some r.name else none))
      ((cn.steps.flatMap (·.runes)).filterMap
        (fun r => if r.ty == "equivalence" then some r.name else none))
    -- ROUTE NOTE (close-out audit O-1/m1, disclosed): the recorded
    -- chain is VALIDATED (it must compose the constraint clause to 'T
    -- against the offered rules) but its proof term is NOT part of the
    -- row proof — the obligations' semantic content enters premise-wise
    -- through the usefi discharge (the parametric rebuild at the alias
    -- world discharges each constraint premise from its own recorded
    -- tree). Whether the chain proof should instead be consumed here is
    -- an open ratification question (compositional-replay note).
    let _ := chainOpt
    unless finalT == quoteT do
      throwError "use-hint: the constraint chain reached {repr finalT}, \
                  not 't at {cn.idStr} (frontier)"
    -- R7b (Phase 3 2a): a NON-trivial :CONSTRAINT-CL is legal iff every
    -- LMI is a FUNCTIONAL-INSTANCE (its constraint obligations) AND the
    -- recorded chain above composed it to 't (checked) — the chain IS
    -- ACL2's in-place discharge of the obligations, replayed against the
    -- offered concrete rules. A non-trivial clause on a PLAIN :use stays
    -- the honest frontier.
    let allFi := lmis.all (fun l => (lmiFnInstance? l).isSome)
    unless constraintCl == [quoteT] || allFi do
      throwError "use-hint: non-trivial :CONSTRAINT-CL {repr constraintCl} \
                  at {cn.idStr} with a non-functional-instance LMI \
                  (frontier)"
    unless lmis.length == hyps.length do
      throwError "use-hint: {lmis.length} :LMI-LST entries ≠ {hyps.length} \
                  :HYPS at {cn.idStr} (emission misalignment — pre-cluster \
                  log?)"
    -- each lmi: resolve the use:<thm> offer, transport its statement
    -- under σ, cross-check the emitted instance verbatim
    let mut hLs : List (SExpr × Expr) := []
    let mut ctxU := ctx
    for (lmi, hypI) in lmis.zip hyps do
      -- FUNCTIONAL-INSTANCE (R7b 2a): the offer's formula IS the
      -- substituted instance (recomputed + verbatim-checked against this
      -- very :HYPS entry at offer derivation), so the hypothesis applies
      -- at the node's env directly — no further transport. Consumed
      -- offers stay KEPT conditions until the a1 alias-world composition
      -- (2c) discharges them.
      if let some (thmName, σ) := lmiFnInstance? lmi then
        let [(spec, hypV)] := ctxU.useFiHyps.filter
            (fun (u, _) => u.name == thmName && u.subst == σ
              && u.formula == hypI)
          | throwError "use-hint: no usefi:{thmName} hypothesis matching \
              this substitution in scope at {cn.idStr} (offer derivation \
              declined — dependency surface or substitution recompute \
              mismatch; frontier)"
        let (hL, ctxU') ← instantiateEvTrueHypAt cfg ctxU hypV [] []
          spec.formula
        ctxU := ctxU'
        hLs := hLs ++ [(hypI, hL)]
      else
      let some (thmName, σpairs) := lmiInstance? lmi
        | throwError "use-hint: LMI {repr lmi} at {cn.idStr} is not a bare \
            theorem name, (:INSTANCE thm (var term)…), or \
            (:FUNCTIONAL-INSTANCE thm (fn (LAMBDA …))…) — frontier"
      let [(spec, hypV)] := ctxU.useHyps.filter (fun (u, _) => u.name == thmName)
        | throwError "use-hint: no use:{thmName} hypothesis in scope at \
            {cn.idStr} (the cited theorem is outside the dependency \
            surface — frontier)"
      let σvars := σpairs.map (·.1)
      let σterms := σpairs.map (·.2)
      unless ACL2.Replay.substTerm σvars σterms spec.formula == hypI do
        throwError "use-hint: substTerm(σ, {thmName}) ≠ the emitted :HYPS \
            instance {repr hypI} at {cn.idStr} (emission divergence)"
      let (hL, ctxU') ← instantiateEvTrueHypAt cfg ctxU hypV σvars σterms
        spec.formula
      ctxU := ctxU'
      hLs := hLs ++ [(hypI, hL)]
    -- the surviving application clause: read off and shape-checked as
    -- (¬hyps ++ input clause); its proof is the child subgoal's replay
    -- R7b capstone shape: NO application clause — ACL2 tautology-drops
    -- `(¬hyps ++ goal)` when the goal IS the (single) instance; the
    -- node's conclusion is then the instance's truth directly. Checked
    -- verbatim (hyps == the input clause), no children expected.
    if appClauses.isEmpty then
      unless hyps == cn.inputClause do
        throwError "use-hint: no application clause at {cn.idStr} but \
            :HYPS ≠ the input clause (shape divergence)"
      unless cn.children.isEmpty do
        throwError "use-hint: children under a tautology-dropped \
            application clause at {cn.idStr} (linking gap)"
      let [(hypI, hL)] := hLs
        | throwError "use-hint: tautology-dropped shape with \
            {hLs.length} instances at {cn.idStr} (frontier — single \
            instance only)"
      ctxU ← pinTermOpaques cfg cfg.envExpr ctxU hypI
      let conv ← ctxValProof cfg ctxU hypI
      let hNe ← mkAppM ``ne_nil_of_evtrue_conv #[hL, conv]
      let p ← mkAppM ``evtrue_of_conv_ne_nil #[conv, hNe]
      return ← mkExpectedTypeHint p
        (← mkAppM ``EvTrue
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr (disjoinTerm cn.inputClause)])
    let [appCl] := appClauses
      | throwError "use-hint: {appClauses.length} application clause(s) at \
          {cn.idStr} (frontier — the single-surviving-clause composition)"
    let negs : List SExpr := hyps.map fun h =>
      .cons (.atom (.symbol { name := "NOT" })) (.cons h .nil)
    unless appCl == negs ++ cn.inputClause do
      throwError "use-hint: application clause {repr appCl} ≠ ¬hyps ++ the \
          input clause at {cn.idStr} (shape divergence)"
    let some child := cn.children.find? (·.inputClause == appCl)
      | throwError "use-hint: no child subgoal matches the application \
          clause at {cn.idStr} (linking gap)"
    for c in cn.children do
      unless c.idStr == child.idStr do
        throwError "use-hint: child {c.idStr} matches no application \
            clause at {cn.idStr} (linking gap)"
    let pApp ← replayClauseWith rec cfg { ctxU with litFacts := [] } child
    -- peel each ¬Lᵢ head: Lᵢ truthy (its instantiated statement) makes
    -- (NOT Lᵢ) nil, and evtrue_extract_else drops it from the disjunction
    let mut p := pApp
    for (hypI, hL) in hLs do
      let negL : SExpr := .cons (.atom (.symbol { name := "NOT" }))
        (.cons hypI .nil)
      ctxU ← pinTermOpaques cfg cfg.envExpr ctxU negL
      let hNe ← mkAppM ``ne_nil_of_evtrue_conv
        #[hL, ← ctxValProof cfg ctxU hypI]
      let hfNot ← mkAppM ``not_nil_of_truthy #[hNe]
      p ← mkAppM ``evtrue_extract_else
        #[← castConvToNil cfg ctxU negL hfNot, p]
    return p
  if lits.isEmpty && cn.inputClause.length == 1 then
    -- a SINGLE-literal clause discharged entirely at PREPROCESS: clause-level
    -- step nodes chain the formula to 't (no literal bracketing is emitted at
    -- preprocess sites). A MULTI-literal clause with only step items falls
    -- through to the SPINE — clause-level branch-substitution/equal-self
    -- steps are spine shapes (comm-rm's *1/1.2).
    if stepNodes.isEmpty then
      throwError "replayClause: no literal or step items in clause {cn.idStr} \
                  (discharge composition frontier)"
    let [formula] := cn.inputClause
      | throwError "replayClause: internal — single-literal guard"
    -- SINGLE-child continuation (S2 2026-07-24, cov-let-lambda's Goal: the
    -- defun unfold rewrote the formula, clausify was a no-op, the result
    -- continues as Goal'): chain this formula to the child's clause and
    -- compose — the single-literal instance of the multi-literal
    -- one-child arm below. Any other child shape is still the frontier.
    if let [child] := cn.children then
      let (chainOpt, finalT) ← replayPreprocessChainCore cfg ctx formula stepNodes
        ((cn.steps.flatMap (·.runes)).filterMap
          (fun r => if r.ty == "congruence" then some r.name else none))
        ((cn.steps.flatMap (·.runes)).filterMap
          (fun r => if r.ty == "equivalence" then some r.name else none))
      unless finalT == disjoinTerm child.inputClause do
        throwError "replayClause: preprocess chain reached {repr finalT}, the \
                    single child's clause disjoins to \
                    {repr (disjoinTerm child.inputClause)} at {cn.idStr}"
      let pChild ← replayClauseWith rec cfg { ctx with litFacts := [] } child
      match chainOpt with
      | none => return pChild
      | some (ch, false) => return ← mkAppM ``evtrue_of_fuel_eq #[ch, pChild]
      | some (ch, true) => return ← mkAppM ``evtrue_of_evrel_siff #[ch, pChild]
    unless cn.children.isEmpty do
      throwError "replayClause: preprocess chain with {cn.children.length} child \
                  clauses at {cn.idStr} (clausify-split frontier)"
    return ← replayPreprocessChain cfg ctx formula stepNodes
      ((cn.steps.flatMap (·.runes)).filterMap
        (fun r => if r.ty == "congruence" then some r.name else none))
      ((cn.steps.flatMap (·.runes)).filterMap
        (fun r => if r.ty == "equivalence" then some r.name else none))
  -- a MULTI-literal PREPROCESS node whose step chain rewrote the clause and
  -- whose clausify was a NO-OP relative to its own input (filtered above),
  -- continuing in a single child (msort *1/3'': the (ODDS X) ⇒
  -- (EVENS (CDR X)) definition pass): replay the chain over the DISJUNCTION
  -- from this clause to the child's, then compose with the child's proof.
  -- Dispatch is on recorded data only — the preprocess processor and the
  -- one-child shape; spine-shaped clause-level steps (comm-rm's *1/1.2)
  -- are simplify nodes with no children and still fall through below.
  if lits.isEmpty && cn.inputClause.length > 1 && !stepNodes.isEmpty
      && cn.steps.any (fun s => s.processor.toLower == "preprocess-clause") then
    if let [child] := cn.children then
      let formula := disjoinTerm cn.inputClause
      let (chainOpt, finalT) ← replayPreprocessChainCore cfg ctx formula stepNodes
        ((cn.steps.flatMap (·.runes)).filterMap
          (fun r => if r.ty == "congruence" then some r.name else none))
        ((cn.steps.flatMap (·.runes)).filterMap
          (fun r => if r.ty == "equivalence" then some r.name else none))
      unless finalT == disjoinTerm child.inputClause do
        throwError "replayClause: preprocess chain reached {repr finalT}, the \
                    single child's clause disjoins to \
                    {repr (disjoinTerm child.inputClause)} at {cn.idStr}"
      let pChild ← replayClauseWith rec cfg { ctx with litFacts := [] } child
      match chainOpt with
      | none => return pChild
      | some (ch, false) => return ← mkAppM ``evtrue_of_fuel_eq #[ch, pChild]
      | some (ch, true) => return ← mkAppM ``evtrue_of_evrel_siff #[ch, pChild]
    -- PROVED at preprocess with NO children: the recorded chain discharges
    -- the whole DISJOINED formula to 't (msort TRUE-LISTP-MSORT *1.1/5's
    -- type-set-fc verdict leaf spans the full clause) — the same chain
    -- composition as the single-literal case, over the disjunction
    if cn.children.isEmpty &&
        cn.steps.any (fun s =>
          s.processor.toLower == "preprocess-clause" && s.result == .proved) then
      let formula := disjoinTerm cn.inputClause
      return ← replayPreprocessChain cfg ctx formula stepNodes
        ((cn.steps.flatMap (·.runes)).filterMap
          (fun r => if r.ty == "congruence" then some r.name else none))
        ((cn.steps.flatMap (·.runes)).filterMap
          (fun r => if r.ty == "equivalence" then some r.name else none))
  rec.clauseSpine cfg ctx cn.idStr (cn.inputClause.zipIdx.map fun (l, i) => (i + 1, l))
    ((cn.steps.flatMap (·.items)).filter fun
      | .clausify _ => false | _ => true)
    [] cn.children

/- The tied clause-level knot — the ONLY remaining mutual at this layer.
   Public names/signatures identical to the pre-WP2 mutual members. -/
mutual

partial def replayClause (cfg : ReplayConfig) (ctx : ReplayCtx) (cn : ClauseNode) :
    MetaM Expr :=
  replayClauseWith ⟨replayClause, replayClauseSpine⟩ cfg ctx cn

partial def replayClauseSpine (cfg : ReplayConfig) (ctx : ReplayCtx) (idStr : String)
    (clauseLits : List (Nat × SExpr)) (items : List ClauseItem)
    (accClause : List SExpr) (children : List ClauseNode) : MetaM Expr :=
  replayClauseSpineWith ⟨replayClause, replayClauseSpine⟩ cfg ctx idStr
    clauseLits items accClause children

end

/-- The tied record itself (recipes outside this file recurse through it). -/
def clauseRec : ClauseRec := ⟨replayClause, replayClauseSpine⟩

end ACL2.Replay.Driver
