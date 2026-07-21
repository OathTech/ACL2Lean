/-
  Driver/Core — split from Driver/Core (WP2 Stage 3a, 2026-07-17;
  see docs/plans/2026-07-18_driver-modular-refactor.md).

  The clause-level walkers (replayClauseSpineWith/replayClauseWith) and the
  tied knot (replayClause/replayClauseSpine + clauseRec).
-/
import ACL2Lean.Replay.Driver.Waterfall.Compose
import ACL2Lean.Replay.Driver.Waterfall.Elim
import ACL2Lean.Replay.Driver.Waterfall.Generalize
import ACL2Lean.Replay.Driver.Waterfall.Subsumed
import ACL2Lean.Replay.Driver.Waterfall.EliminateIrrelevance
import ACL2Lean.Replay.Driver.Waterfall.Induction

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- Replay a clause as its LITERAL SPINE: prove `EvTrue w env (disjoinTerm
    clauseLits)`. Items are walked STRUCTURALLY: each non-closing literal is
    followed by its case BRANCHES (`.branch seg items` — the clause scan
    continues INSIDE them). A literal with a trivial clausify trace (no
    split-verdict tests) has exactly one branch, the plain continuation,
    entered via `evtrue_dp_if_split` (truth closes the clause; falsity
    descends with the value fact in `ctx.litFacts`). A literal whose trace
    SPLITS enters `composeSplit` (the W3 assume-true-false composer).
    `accClause` mirrors ACL2's `new-clause` (surviving segment literals, for
    residual-child matching); `children` are the clause node's pushed
    subgoals. -/
partial def replayClauseSpineWith (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (idStr : String)
    (clauseLits : List (Nat × SExpr)) (items : List ClauseItem)
    (accClause : List SExpr) (children : List ClauseNode) :
    MetaM Expr := do
  match items with
  | [] => throwError "replayClauseSpine: ran out of items with no closer \
                      at {idStr}"
  | .clausify _ :: _ =>
    throwError "replayClauseSpine: clausify record in the spine at {idStr} \
                (frontier)"
  | .step n :: rest =>
    -- a :CONTEXT-SUBST decoration (clausify-branch segment hypothesis): its
    -- equation is consumed by solidify `.segment` nodes from the in-scope
    -- segFacts — no separate proof obligation here
    if (runeOf n).ty == "context-subst" then
      return ← replayClauseSpineWith rec cfg ctx idStr clauseLits rest accClause children
    -- a :BRANCH-SUBSTITUTION (remove-trivial-equivalences): ACL2 substitutes
    -- `var := val` THROUGHOUT the clause, justified by the clause's own
    -- `(not (equal var val))` literal, and scans the SUBSTITUTED literals.
    -- Mirror: byCases on that literal's value — truthy closes the clause;
    -- nil gives the value equality, `diffCollapse` transports the whole
    -- disjunction to the substituted clause, and the walk continues there.
    if (runeOf n).ty == "branch-substitution" then
      let .node _ varT valT _ prov := n
      -- :EQUIVALENCE is the RELATION name; only `equal` is supported
      unless prov.equivTerm == some (.atom (.symbol { name := "EQUAL" })) do
        throwError "replayClauseSpine: branch-substitution under equivalence \
                    {repr prov.equivTerm} at {idStr} (frontier — equal only)"
      let .atom (.symbol varSym) := varT
        | throwError "replayClauseSpine: branch-substitution variable \
                      {repr varT} is not a variable at {idStr}"
      -- the justifying clause literal `(not (equal … …))`, either orientation
      let mkNegEq (x y : SExpr) : SExpr :=
        .cons (.atom (.symbol { name := "NOT" }))
          (.cons (.cons (.atom (.symbol { name := "EQUAL" }))
            (.cons x (.cons y .nil))) .nil)
      let inClause? : Option ((SExpr × SExpr) × Nat) :=
        match clauseLits.find? (fun (_, l) => l == mkNegEq varT valT) with
        | some (i, _) => some ((varT, valT), i)
        | none =>
          (clauseLits.find? (fun (_, l) => l == mkNegEq valT varT)).map
            (fun (i, _) => ((valT, varT), i))
      -- SEGMENT-justified substitution (observed: ALL-REL-RM-1, Subgoal *1/3):
      -- inside a clausify-branch continuation the justifying
      -- `(not (equal var val))` is a SEGMENT literal of the child clause —
      -- its FALSITY is already proved (segFacts), so no case split: derive
      -- `var = val`, transport the remaining disjunction, and walk the
      -- substituted literals. Nothing to delete — the used literal is not
      -- part of this disjunction.
      if inClause?.isNone then
        let segEq? : Option ((SExpr × SExpr) × Expr) :=
          match ctx.segFacts.find? (fun (st, _) => st == mkNegEq varT valT) with
          | some (_, hf) => some ((varT, valT), hf)
          | none =>
            (ctx.segFacts.find? (fun (st, _) => st == mkNegEq valT varT)).map
              (fun (_, hf) => ((valT, varT), hf))
        let ctx1 ← pinTermOpaques cfg cfg.envExpr ctx valT
        -- hVeq : v(varT) = v(valT), from either justification shape
        let hVeq ←
          match segEq? with
          | some ((ta, tb), hNil) => do
            let va ← ctxValExpr cfg ctx1 ta
            let vb ← ctxValExpr cfg ctx1 tb
            let hEq ← mkAppM ``logic_not_equal_nil_eq #[va, vb, hNil]  -- va = vb
            if ta == varT then pure hEq else mkAppM ``Eq.symm #[hEq]
          | none =>
            -- remove-trivial-equivalences' OTHER justification: the segment
            -- literal IS the variable — `var` false means v(var) = nil =
            -- v('NIL), justifying `var := 'NIL` directly (observed: APP-NIL
            -- Subgoal *1/3, segment `(X)`, X ⇒ 'NIL)
            match (if valT == quoteNil then
                     (ctx.segFacts.find? (fun (st, _) => st == varT)).map (·.2)
                   else none) with
            | some hNil => pure hNil
            | none =>
              throwError "replayClauseSpine: branch-substitution literal \
                          (not (equal {repr varT} {repr valT})) is neither in \
                          the clause nor a segment fact at {idStr}"
        let pVar ← ctxValProof cfg ctx1 varT
        let pVal ← ctxValProof cfg ctx1 valT
        let nodeEq ← mkAppM ``fuel_eq_of_conv #[pVar, pVal, hVeq]
        let substLits := clauseLits.map fun (i, l) =>
          (i, ACL2.Replay.substTerm [varSym] [valT] l)
        let mut ctx2 ← pinTermOpaques cfg cfg.envExpr ctx1
          (disjoinTerm (substLits.map (·.2)))
        let chainOpt ← diffCollapse cfg.worldExpr cfg.envExpr varT valT nodeEq
          (disjoinTerm (clauseLits.map (·.2))) (disjoinTerm (substLits.map (·.2)))
        -- TRANSPORT the in-scope falsity facts across the substitution: ACL2
        -- scans the substituted clause under the substituted assumptions, so
        -- its type-alist consults the `var := val` form of each fact. Each
        -- transported entry is APPENDED (originals first — index lookups keep
        -- their original binding) with the fact bridged along the same
        -- var≡val chain; a fact diffCollapse cannot bridge hard-fails.
        for (i, l, h) in ctx2.litFacts do
          let l' := ACL2.Replay.substTerm [varSym] [valT] l
          if l' != l then
            ctx2 ← pinTermOpaques cfg cfg.envExpr ctx2 l'
            let some chL ← diffCollapse cfg.worldExpr cfg.envExpr varT valT nodeEq l l'
              | throwError "replayClauseSpine: branch-substitution fact \
                            transport of {repr l} produced no chain at {idStr}"
            let vEq ← mkAppM ``val_eq_of_eval_eq
              #[chL, ← ctxValProof cfg ctx2 l, ← ctxValProof cfg ctx2 l']
            let h' ← mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[vEq], h]
            ctx2 := { ctx2 with litFacts := ctx2.litFacts ++ [(i, l', h')] }
        for (st, h) in ctx2.segFacts do
          let st' := ACL2.Replay.substTerm [varSym] [valT] st
          if st' != st then
            ctx2 ← pinTermOpaques cfg cfg.envExpr ctx2 st'
            let some chL ← diffCollapse cfg.worldExpr cfg.envExpr varT valT nodeEq st st'
              | throwError "replayClauseSpine: branch-substitution fact \
                            transport of {repr st} produced no chain at {idStr}"
            let vEq ← mkAppM ``val_eq_of_eval_eq
              #[chL, ← ctxValProof cfg ctx2 st, ← ctxValProof cfg ctx2 st']
            let h' ← mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[vEq], h]
            ctx2 := { ctx2 with segFacts := ctx2.segFacts ++ [(st', h')] }
        let p ← replayClauseSpineWith rec cfg ctx2 idStr substLits rest accClause children
        return ← match chainOpt with
          | none => pure p
          | some ch => mkAppM ``evtrue_of_fuel_eq #[ch, p]
      let some ((ta, tb), kIdx) := inClause?
        | throwError "replayClauseSpine: internal — inClause? vanished"
      let negEq : SExpr := mkNegEq ta tb
      let mut ctx := ctx
      ctx ← pinTermOpaques cfg cfg.envExpr ctx valT
      let vK ← ctxValExpr cfg ctx negEq
      let pK ← ctxValProof cfg ctx negEq
      let nilC := mkConst ``SExpr.nil
      let negL ← withLocalDeclD `hnil (← mkEq vK nilC) fun hNil => do
        let va ← ctxValExpr cfg ctx ta
        let vb ← ctxValExpr cfg ctx tb
        let hEq ← mkAppM ``logic_not_equal_nil_eq #[va, vb, hNil]  -- va = vb
        -- orient var ⇒ val
        let hVeq ← if ta == varT then pure hEq else mkAppM ``Eq.symm #[hEq]
        let pVar ← ctxValProof cfg ctx varT
        let pVal ← ctxValProof cfg ctx valT
        let nodeEq ← mkAppM ``fuel_eq_of_conv #[pVar, pVal, hVeq]
        let substLits := clauseLits.map fun (i, l) =>
          (i, ACL2.Replay.substTerm [varSym] [valT] l)
        -- the SUBSTITUTED literals are new terms — pin their user-fn opaques
        -- before any value construction over them
        let ctx ← pinTermOpaques cfg cfg.envExpr ctx
          (disjoinTerm (substLits.map (·.2)))
        let chainOpt ← diffCollapse cfg.worldExpr cfg.envExpr varT valT nodeEq
          (disjoinTerm (clauseLits.map (·.2))) (disjoinTerm (substLits.map (·.2)))
        -- remove-trivial-equivalences also DELETES the used literal — now the
        -- trivial `(not (equal v v))` — from the clause it scans; collapse its
        -- if-frame out of the disjunction (its value is nil by reflexivity)
        let kPos := clauseLits.findIdx (fun (i, _) => i == kIdx)
        if kPos + 1 == clauseLits.length then
          -- the used literal is LAST: deleting it changes nothing any later
          -- record references (there are none after it) — keep the trivial
          -- literal in the walked clause and continue on the substituted
          -- literals directly (EQUAL-CONS Subgoal 4, chained substitutions)
          let pRest ← replayClauseSpineWith rec cfg ctx idStr substLits rest
            accClause children
          let p ← match chainOpt with
            | none => pure pRest
            | some ch => mkAppM ``evtrue_of_fuel_eq #[ch, pRest]
          mkLambdaFVars #[hNil] p
        else do
        unless kPos + 1 < clauseLits.length do
          throwError "replayClauseSpine: branch-substitution literal is the \
                      clause's LAST literal at {idStr} (frontier)"
        let shortened := (substLits.eraseIdx kPos).zipIdx.map fun ((_, l), j) =>
          (j + 1, l)
        let some (_, trivLit) := substLits[kPos]?
          | throwError "replayClauseSpine: internal — kPos out of range"
        let .cons _ (.cons trivEq .nil) := trivLit
          | throwError "replayClauseSpine: substituted equality literal \
                        {repr trivLit} is not (not …) at {idStr}"
        let .cons _ (.cons tx (.cons ty .nil)) := trivEq
          | throwError "replayClauseSpine: substituted equality \
                        {repr trivEq} shape at {idStr}"
        unless tx == ty do
          throwError "replayClauseSpine: substituted equality {repr trivEq} \
                      is not reflexive at {idStr}"
        let vx ← ctxValExpr cfg ctx tx
        let hEqT ← mkAppM ``Logic.equal_self #[vx]
        let hNotNil ← mkAppM ``Eq.trans
          #[← mkAppM ``congrArg #[mkConst ``Logic.not, hEqT],
            mkConst ``logic_not_t_nil]
        let pTriv ← ctxValProof cfg ctx trivLit
        let hcNil ← mkAppM ``re_val_cast
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr trivLit,
            ← ctxValExpr cfg ctx trivLit, nilC, pTriv, hNotNil]
        -- (if triv 't tail) ≡ tail, lifted through the k-1 else-descents
        let tailLits := (substLits.drop (kPos + 1)).map (·.2)
        let tailTerm := disjoinTerm tailLits
        let vTail ← ctxValExpr cfg ctx tailTerm
        let hTail ← ctxValProof cfg ctx tailTerm
        let _ := vTail
        let mut inner ← mkAppM ``re_if_false
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr trivLit, reflectSExpr quoteT,
            reflectSExpr tailTerm, vTail, hcNil, hTail]
        let mut curL : SExpr := .cons (.atom (.symbol { name := "IF" }))
          (.cons trivLit (.cons quoteT (.cons tailTerm .nil)))
        let mut curR : SExpr := tailTerm
        for (_, l) in (substLits.take kPos).reverse do
          let st : PathStep := { fn := { name := "IF" }, arity := 3, argIdx := 2,
                                 siblings := [l, quoteT] }
          inner ← applyStep cfg.worldExpr cfg.envExpr st curL curR inner
          curL := rebuild st.fn st.arity st.argIdx curL st.siblings
          curR := rebuild st.fn st.arity st.argIdx curR st.siblings
        unless curL == disjoinTerm (substLits.map (·.2)) &&
               curR == disjoinTerm (shortened.map (·.2)) do
          throwError "replayClauseSpine: branch-substitution shortening lift \
                      reconstructed {repr curL} / {repr curR} at {idStr}"
        let chainAll ← match chainOpt with
          | none => pure inner
          | some ch => mkAppM ``fuel_chain_eq #[ch, inner]
        let pRest ← replayClauseSpineWith rec cfg ctx idStr shortened rest accClause children
        let p ← mkAppM ``evtrue_of_fuel_eq #[chainAll, pRest]
        mkLambdaFVars #[hNil] p
      let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[vK, nilC]) fun hNe => do
        let p ← evtrueOfLitTrue cfg ctx (clauseLits.map (·.2)) (kIdx - 1) negEq hNe
        mkLambdaFVars #[hNe] p
      let _ := pK
      return ← mkAppM ``Classical.byCases #[negL, posL]
    -- a clause-level EQUAL-SELF step: the literal (equal X X) is TRUE by
    -- reflexivity and closes the whole disjunction (comm-rm's *1/1.2 after
    -- its branch-substitution trivializes the conclusion)
    if (runeOf n).ty == "equal-self" then
      -- this step CLOSES the clause; trailing spine items would be silently
      -- unreplayed — fail closed (audit #3 hardening)
      unless rest.isEmpty do
        throwError "replayClauseSpine: {rest.length} spine item(s) after a \
                    closing clause-level equal-self at {idStr} (frontier)"
      let (lhs, rhs) := nodeLhsRhs n
      unless rhs == quoteT do
        throwError "replayClauseSpine: clause-level equal-self with rhs \
                    {repr rhs} at {idStr} (frontier)"
      let some X := asEqualSelf lhs
        | throwError "replayClauseSpine: clause-level equal-self lhs \
                      {repr lhs} is not (equal X X) at {idStr}"
      let some k := clauseLits.findIdx? (·.2 == lhs)
        | throwError "replayClauseSpine: equal-self literal {repr lhs} not \
                      in the clause at {idStr}"
      let ctx ← pinTermOpaques cfg cfg.envExpr ctx lhs
      let vX ← ctxValExpr cfg ctx X
      let hEqT ← mkAppM ``Logic.equal_self #[vX]
      let tNeNil ← proveByDecide
        (← mkAppM ``Ne #[mkConst ``SExpr.t, mkConst ``SExpr.nil]) "t ≠ nil"
      let hne ← mkAppM ``ne_of_eq_of_ne #[hEqT, tNeNil]
      return ← evtrueOfLitTrue cfg ctx (clauseLits.map (·.2)) k lhs hne
    -- a clause-level EXECUTABLE-COUNTERPART step: remove-trivial-equivalences'
    -- scan evaluates a GROUND application in the substituted clause literals
    -- (APP-NIL Subgoal *1/3: (APP 'NIL 'NIL) ⇒ 'NIL after X ⇒ 'NIL). Mirror:
    -- re-run the same closed computation (the exec-counterpart carve-out),
    -- rewrite every occurrence across the disjunction (diffCollapse), and
    -- continue the walk on the evaluated literals.
    if (runeOf n).ty == "executable-counterpart" then
      let (lhs, rhs) := nodeLhsRhs n
      let .cons (.atom (.symbol q)) (.cons v .nil) := rhs
        | throwError "replayClauseSpine: clause-level exec-counterpart rhs \
                      {repr rhs} is not a quoted constant at {idStr}"
      unless q.name == "QUOTE" do
        throwError "replayClauseSpine: clause-level exec-counterpart rhs \
                    {repr rhs} is not a quoted constant at {idStr}"
      let conv1 ← replayExecGround cfg lhs v
      let conv2 ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr v]
      let nodeEq ← mkAppM ``fuel_eq_of_conv #[conv1, conv2, ← mkEqRefl (reflectSExpr v)]
      let rec replaceAll (t : SExpr) : SExpr :=
        if t == lhs then rhs
        else match t with
          | .cons a b => .cons (replaceAll a) (replaceAll b)
          | _ => t
      let newLits := clauseLits.map fun (i, l) => (i, replaceAll l)
      if newLits == clauseLits then
        -- the evaluated subterm is not in the REMAINING literals (it lived in
        -- an already-walked or dropped one) — the step is a no-op here
        return ← replayClauseSpineWith rec cfg ctx idStr clauseLits rest accClause children
      let ctx ← pinTermOpaques cfg cfg.envExpr ctx (disjoinTerm (newLits.map (·.2)))
      let chainOpt ← diffCollapse cfg.worldExpr cfg.envExpr lhs rhs nodeEq
        (disjoinTerm (clauseLits.map (·.2))) (disjoinTerm (newLits.map (·.2)))
      let p ← replayClauseSpineWith rec cfg ctx idStr newLits rest accClause children
      return ← match chainOpt with
        | none => pure p
        | some ch => mkAppM ``evtrue_of_fuel_eq #[ch, p]
    throwError "replayClauseSpine: clause-level step item (rune \
                {repr (runeOf n)}) in the spine at {idStr} (frontier)"
  | .branch seg _ :: _ =>
    throwError "replayClauseSpine: branch item with no preceding literal at \
                {idStr} (frontier): segment {repr seg}"
  | .literal lp :: rest =>
    -- this literal's case branches. Clause-level steps emitted BETWEEN the
    -- literal and a `┌ branch` (rewrite-clause emits each new clause's
    -- post-split steps — remove-trivial-equivalences, its evaluations —
    -- before that clause's BEGIN-BRANCH) belong to the FOLLOWING branch's
    -- continuation: regroup each maximal `.step` run into the next branch.
    -- Nothing else may follow at this level; trailing steps with no branch
    -- hard-fail.
    let rec regroup : List ClauseItem → Except String (List (SExpr × List ClauseItem))
      | [] => pure []
      | items => do
        let pre := items.takeWhile (fun | .step _ => true | _ => false)
        match items.drop pre.length with
        | .branch seg its :: tail => pure ((seg, pre ++ its) :: (← regroup tail))
        | [] => throw s!"replayClauseSpine: {pre.length} clause-level step(s) \
                         after literal {lp.index} with no following branch at \
                         {idStr} (frontier)"
        | it :: _ =>
          let tag := match it with
            | .literal l => s!"literal {l.index}"
            | .clausify _ => "clausify"
            | _ => "step"
          throw s!"replayClauseSpine: non-branch item ({tag}) after literal \
                   {lp.index}'s branches at {idStr} (frontier)"
    let branchSegs ← ofExcept (regroup rest)
    let idx := lp.index
    let (cidx, clit) :: restLits := clauseLits
      | throwError "replayClauseSpine: literal item {idx} beyond the clause's \
                    literals at {idStr} (item/clause walk divergence)"
    unless idx == cidx && lp.literal == clit do
      -- a SKIPPED literal whose falsity is already an in-scope hypothesis —
      -- chiefly a DUPLICATE (ACL2's add-literal drops a literal identical to
      -- an earlier one; branch-substitution creates these), but sound for
      -- ANY literal with a genuine falsity fact: collapsing its if-frame by
      -- the fact preserves the disjunction. A spurious fire (e.g. on a
      -- hoisted later-literal fact) misaligns the walk and hard-fails
      -- downstream — never a wrong proof (audit 2026-07-06).
      if lp.literal != clit then
        if let some hNil := ctx.litFactByTerm? clit then
          let restTerm := disjoinTerm (restLits.map (·.2))
          let vC ← ctxValExpr cfg ctx clit
          let pC ← ctxValProof cfg ctx clit
          let hcNil ← mkAppM ``re_val_cast
            #[cfg.worldExpr, cfg.envExpr, reflectSExpr clit, vC,
              mkConst ``SExpr.nil, pC, hNil]
          let hRest ← ctxValProof cfg ctx restTerm
          let vRest ← ctxValExpr cfg ctx restTerm
          let hIf ← mkAppM ``re_if_false
            #[cfg.worldExpr, cfg.envExpr, reflectSExpr clit, reflectSExpr quoteT,
              reflectSExpr restTerm, vRest, hcNil, hRest]
          let restLits' := restLits.map fun (i, l) => (i - 1, l)
          let p ← replayClauseSpineWith rec cfg ctx idStr restLits' items accClause children
          return ← mkAppM ``evtrue_of_fuel_eq #[hIf, p]
      throwError "replayClauseSpine: literal item {idx} {repr lp.literal} does \
                  not walk the clause at {idStr} (next clause literal is {cidx} \
                  {repr clit})"
    -- HOIST later-literal facts demanded by SILENT hyp reliefs in this
    -- literal's chain (the emitted relieve-hyp/* markers): ACL2 rewrites
    -- literal i under the falsity of ALL other clause literals, but the walk
    -- holds only the earlier ones. For each marker hyp whose complement IS a
    -- later clause literal with no fact in scope, case-split on that literal
    -- FIRST — its truth closes the whole disjunction; its falsity joins
    -- litFacts and the walk re-enters (one fewer demand each time).
    let demanded := (lp.nodes.flatMap collectContextDemands).eraseDups
    for notH in demanded do
      if (ctx.litFactByTerm? notH).isSome then continue
      let some (k, _) := restLits.find? (fun (_, l) => l == notH)
        | continue  -- not a later literal: the consumer fails precisely if missing
      let ctx ← pinTermOpaques cfg cfg.envExpr ctx notH
      let vL ← ctxValExpr cfg ctx notH
      let pL ← ctxValProof cfg ctx notH
      let _ := pL
      let nilC := mkConst ``SExpr.nil
      let allLits := clauseLits.map (·.2)
      let some pos := clauseLits.findIdx? (fun (i, _) => i == k)
        | throwError "replayClauseSpine: internal — hoisted literal {k} not \
                      in the clause at {idStr}"
      let negL ← withLocalDeclD `hnil (← mkEq vL nilC) fun hNil => do
        let ctx' := { ctx with litFacts := ctx.litFacts ++ [(k, notH, hNil)] }
        let p ← replayClauseSpineWith rec cfg ctx' idStr clauseLits items accClause children
        mkLambdaFVars #[hNil] p
      let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[vL, nilC]) fun hNe => do
        let p ← evtrueOfLitTrue cfg ctx allLits pos notH hNe
        mkLambdaFVars #[hNe] p
      return ← mkAppM ``Classical.byCases #[negL, posL]
    -- a literal that IS the ground constant 't (post-substitution ground
    -- evaluation reduced it), reported true by rewrite-atm's type-set
    -- (ATM/TYPE-SET-TRUE, :RESULT :TRUE — APP-NIL Subgoal *1/3): the clause
    -- closes on the literally-true literal, no chain to replay.
    if lp.literal == quoteT && lp.result == .atom (.keyword "TRUE") then
      let pclose ← quoteTFact cfg
      if restLits.isEmpty then
        return ← mkAppM ``evtrue_of_eq_t #[pclose]
      else
        let restTerm := disjoinTerm (restLits.map (·.2))
        let hq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
        let hcv ← proveByDecide
          (← mkEq (mkApp (mkConst ``Logic.toBool) (mkConst ``SExpr.t)) (mkConst ``Bool.true))
          "toBool t"
        let hIf ← mkAppM ``conv_if_true
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr lp.literal, reflectSExpr quoteT,
            reflectSExpr restTerm, mkConst ``SExpr.t, mkConst ``SExpr.t, pclose, hcv, hq]
        return ← mkAppM ``evtrue_of_eq_t #[hIf]
    if lp.result == quoteT then
      -- the closer: its chain proves it `t`; any later literals (scanned or
      -- not) are short-circuited by the true test.
      unless branchSegs.isEmpty do
        throwError "replayClauseSpine: branches after the closing literal \
                    {idx} at {idStr} (frontier)"
      let pclose ← replayLiteral cfg ctx lp
      if restLits.isEmpty then
        mkAppM ``evtrue_of_eq_t #[pclose]
      else
        -- `(if litᵢ 't rest)` with the test KNOWN `t`
        let restTerm := disjoinTerm (restLits.map (·.2))
        let hq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
        let hcv ← proveByDecide
          (← mkEq (mkApp (mkConst ``Logic.toBool) (mkConst ``SExpr.t)) (mkConst ``Bool.true))
          "toBool t"
        let hIf ← mkAppM ``conv_if_true
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr lp.literal, reflectSExpr quoteT,
            reflectSExpr restTerm, mkConst ``SExpr.t, mkConst ``SExpr.t, pclose, hcv, hq]
        mkAppM ``evtrue_of_eq_t #[hIf]
    else
      -- the literal's rewrite chain: literal ⇒ result
      let (chainOpt, finalT) ← replayLiteralChain cfg ctx lp
      let chainOpt ← do
        if finalT == lp.result then pure chainOpt else
        -- rewrite-equal's unrecorded NIL normalization at the chain end
        match ← bridgeEqualNilNorm cfg ctx finalT lp.result with
        | some br => match chainOpt with
          | none => pure (some br)
          | some ch => pure (some (← mkAppM ``fuel_chain_eq #[ch, br]))
        | none =>
          throwError "replayClauseSpine: literal {idx} chain reached {repr finalT} \
                      at {idStr}, recorded result is {repr lp.result}"
      -- does the clausify decision trace SPLIT?
      let hasSplit := lp.splitTrace.any fun
        | .test _ v _ _ => v == "split"
        | _ => false
      if hasSplit then
        -- W3: the assume-true-false composer. Post-pass reshaping (the
        -- Satriani REPLACEMENT, the subsumption loop) is transparent to the
        -- LEAF-driven composer: branch selection is by derivable segment
        -- falsity with a uniqueness requirement, so a redistributed literal
        -- set still links each leaf to its branch, and a missing or
        -- ambiguous link fails closed at selection. A SUBSUMED-dropped new
        -- clause leaves its leaf unlinkable — still a clean failure there.
        unless lp.splitReshaped.all
            (fun r => r == "satriani-replaced" || r == "subsumption-loop") do
          throwError "replayClauseSpine: literal {idx}'s segment set was \
                      reshaped ({lp.splitReshaped}) at {idStr} (frontier)"
        let (tree, restTrace) ← ofExcept (parseTraceTree [] lp.splitTrace)
        unless restTrace.isEmpty do
          throwError "replayClauseSpine: trailing decision-trace events on \
                      literal {idx} at {idStr}: {repr restTrace.head?}"
        -- pin the trace leaf values' opaques (collapse intermediates live
        -- inside them)
        let mut ctx := ctx
        for d in lp.splitTrace do
          if let .leaf v _ _ _ := d then
            ctx ← pinTermOpaques cfg cfg.envExpr ctx v
        return ← composeSplit rec cfg ctx idStr lp chainOpt clit restLits branchSegs
          accClause children [] tree
      -- TRIVIAL continuation: exactly one branch, its segment matching the
      -- single trace leaf's clause segment
      let (contItems, segLits) ← match branchSegs with
        | [(seg, cont)] => do
          let some segL := seg.toList?
            | throwError "replayClauseSpine: literal {idx}'s branch segment \
                          {repr seg} is not a list at {idStr}"
          match lp.splitTrace.filter (fun | .leaf .. => true | _ => false) with
          | [.leaf lv outcome _ _] =>
            if outcome == "dropped" then
              throwError "replayClauseSpine: single DROPPED leaf on the \
                          non-closing literal {idx} at {idStr} (frontier)"
            let expectedSeg : SExpr :=
              if outcome == "segment-open" then .cons lp.result .nil else .nil
            unless seg == expectedSeg &&
                   (outcome == "segment-false" || lv == lp.result) do
              throwError "replayClauseSpine: literal {idx}'s branch segment \
                          {repr seg} does not match its trace leaf \
                          ({outcome}, {repr lv}) at {idStr}"
          | [] => pure ()  -- no trace (synthetic/legacy log): tolerated
          | leaves =>
            throwError "replayClauseSpine: literal {idx} has {leaves.length} \
                        trace leaves but no split test at {idStr}"
          pure (cont, segL)
        | [] =>
          throwError "replayClauseSpine: non-closing literal {idx} with no \
                      continuation branch at {idStr} (frontier)"
        | _ =>
          throwError "replayClauseSpine: {branchSegs.length} branches on \
                      literal {idx} without a split trace at {idStr} (frontier)"
      if contItems.isEmpty && restLits.isEmpty then
        -- LAST literal, non-closing, trivial trace: the SURVIVING clause was
        -- PUSHED as the sibling subgoal (composeSplit's empty-cont residual,
        -- on the trivial path). The spine's goal here is the BARE literal
        -- (singleton disjunction) — no case split: replay the child, peel it
        -- down to this literal's survivor, and bridge back along the chain.
        let accClause' := accClause ++ segLits.filter (!accClause.contains ·)
        let some child := children.find? (·.inputClause == accClause')
          | throwError "replayClauseSpine: no child clause matches the \
                        residual {repr accClause'} at {idStr}"
        -- VACUOUS path (segment-false leaf, empty segment — observed:
        -- ALL-REL-RM-2, Subgoal *1/3'): the literal collapsed to 'nil and
        -- contributed nothing, so the pushed child IS accClause — whose
        -- every literal has an in-scope falsity fact. The child's proof
        -- then CONTRADICTS this path's assumptions: peel to any literal
        -- and refute — the spine's goal follows ex falso, exactly the
        -- clause-level composition (this case of the parent is impossible).
        if lp.result == quoteNil && segLits.isEmpty then
          unless !accClause'.isEmpty do
            throwError "replayClauseSpine: vacuous residual with an EMPTY \
                        child clause at {idStr} (frontier)"
          let pChild ← rec.clause cfg { ctx with litFacts := [] } child
          let mut p := pChild
          for L in accClause'.dropLast do
            let some hf := ctx.litFactByTerm? L
              | throwError "replayClauseSpine: no falsity fact for the residual \
                            literal {repr L} at {idStr}"
            let pNil ← mkAppM ``re_val_cast
              #[cfg.worldExpr, cfg.envExpr, reflectSExpr L,
                ← ctxValExpr cfg ctx L, mkConst ``SExpr.nil,
                ← ctxValProof cfg ctx L, hf]
            p ← mkAppM ``evtrue_extract_else #[pNil, p]
          let some lastL := accClause'.getLast?
            | throwError "replayClauseSpine: internal — empty accClause'"
          let some hfLast := ctx.litFactByTerm? lastL
            | throwError "replayClauseSpine: no falsity fact for the residual \
                          literal {repr lastL} at {idStr}"
          -- p : EvTrue(lastL) vs hfLast : v(lastL) = nil — absurd
          let hNe ← mkAppM ``ne_nil_of_evtrue_conv #[p, ← ctxValProof cfg ctx lastL]
          let goalTy ← mkAppM ``EvTrue
            #[cfg.worldExpr, cfg.envExpr, reflectSExpr lp.literal]
          return ← mkAppOptM ``absurd #[none, some goalTy, some hfLast, some hNe]
        unless accClause'.getLast? == some lp.result do
          throwError "replayClauseSpine: residual's surviving literal is not \
                      literal {idx}'s result at {idStr} (frontier)"
        let pChild ← rec.clause cfg { ctx with litFacts := [] } child
        let mut p := pChild
        for L in accClause'.dropLast do
          let some hf := ctx.litFactByTerm? L
            | throwError "replayClauseSpine: no falsity fact for the residual \
                          literal {repr L} at {idStr}"
          let pNil ← mkAppM ``re_val_cast
            #[cfg.worldExpr, cfg.envExpr, reflectSExpr L,
              ← ctxValExpr cfg ctx L, mkConst ``SExpr.nil,
              ← ctxValProof cfg ctx L, hf]
          p ← mkAppM ``evtrue_extract_else #[pNil, p]
        -- p : EvTrue(lp.result) — bridge to the pre-rewrite literal
        match chainOpt with
        | none => return p
        | some ch => return ← mkAppM ``evtrue_of_fuel_eq #[ch, p]
      -- split on the literal's value
      let vLit ← ctxValExpr cfg ctx lp.literal
      let pLit ← ctxValProof cfg ctx lp.literal
      let restTerm := disjoinTerm (restLits.map (·.2))
      let neTy ← mkAppM ``Ne #[vLit, mkConst ``SExpr.nil]
      let hthen ← withLocalDeclD `h neTy fun h => do
        let p ← mkAppM ``evtrue_of_eq_t #[← quoteTFact cfg]
        let _ := h
        mkLambdaFVars #[h] p
      let eqTy ← mkEq vLit (mkConst ``SExpr.nil)
      let helse ← withLocalDeclD `h eqTy fun h => do
        let (factTerm, factProof) ←
          match chainOpt with
          | none => pure (lp.literal, h)
          | some ch => do
            -- bridge the falsity to the post-rewrite literal
            let _vLit' ← ctxValExpr cfg ctx lp.result
            let pLit' ← ctxValProof cfg ctx lp.result
            let vEq ← mkAppM ``val_eq_of_eval_eq #[ch, pLit, pLit']
            pure (lp.result, ← mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[vEq], h])
        let ctx' := { ctx with litFacts := ctx.litFacts ++ [(idx, factTerm, factProof)] }
        let accClause' := accClause ++ segLits.filter (!accClause.contains ·)
        let p ← replayClauseSpineWith rec cfg ctx' idStr restLits contItems accClause' children
        mkLambdaFVars #[h] p
      mkAppM ``evtrue_dp_if_split
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr lp.literal, reflectSExpr quoteT,
          reflectSExpr restTerm, vLit, pLit, hthen, helse]

/-- Replay a clause node: prove `EvTrue w env (disjoinTerm inputClause)`
    (for a single-literal clause this IS the literal/formula statement).
    Induction nodes hard-fail (the scaffold lands next); a pushed clause delegates
    to its pool-root child when the clauses coincide. -/
partial def replayClauseWith (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (cn : ClauseNode) : MetaM Expr := do
  if cn.induction.isSome then
    return ← replayInduction rec cfg ctx cn
  -- EFFECTIVE clausify records: clausify-input emits its checkpoints on every
  -- preprocess pass, including 'miss passes (whose events flush into the NEXT
  -- step's :REWRITES) and identity re-clausifications — a record whose single
  -- output clause disjoins back to exactly its input, or whose input is the
  -- trivially-true `(quote t)` with an EMPTY output set, certifies that the
  -- pass changed nothing the replay must mirror.
  let isNoopClausify : ClausifyInfo → Bool := fun i =>
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
    match cn.children with
    | [child] =>
      unless child.inputClause == cn.inputClause do
        throwError "replayClause: pushed clause ≠ pool-root clause at {cn.idStr}"
      return ← replayClauseWith rec cfg ctx child
    | _ => throwError "replayClause: push-clause with {cn.children.length} children at {cn.idStr}"
  -- a POOL-SUBSUMED root (synthetic; from (:POOL-SUBSUMED …)): its clause is
  -- an instance-superset of the MORE GENERAL pool root attached as its child
  if cn.steps.any (fun s => s.processor.toLower == "pool-subsumed") then
    return ← replaySubsumed rec cfg ctx cn
  -- a DESTRUCTOR-ELIMINATION node: the child clause is over the elim's fresh
  -- variables; replayElim bridges it back through the emitted ELIMSEQUENCE
  if let some st := cn.steps.find? (fun s => s.processor.toLower == "eliminate-destructors-clause") then
    unless clausifyInfos.isEmpty do
      throwError "replayClause: elim step alongside an effective clausify \
                  record at {cn.idStr} (frontier)"
    return ← replayElim rec cfg ctx cn st
  -- a GENERALIZE node: the child clause abstracts the emitted :TERMS by fresh
  -- :VARS; replayGeneralize replays the child at the env binding the fresh
  -- vars to the terms' values and substN-bridges back
  if let some st := cn.steps.find? (fun s => s.processor.toLower == "generalize-clause") then
    unless clausifyInfos.isEmpty do
      throwError "replayClause: generalize step alongside an effective \
                  clausify record at {cn.idStr} (frontier)"
    return ← replayGeneralize rec cfg ctx cn st
  -- an ELIMINATE-IRRELEVANCE node: the child clause is an order-preserving
  -- SUBSET of this clause (irrelevant literals dropped) — the child's truth
  -- closes the parent disjunction through whichever literal is truthy
  if cn.steps.any (fun s => s.processor.toLower == "eliminate-irrelevance-clause") then
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
  let lits := flattenLiterals (cn.steps.flatMap (·.items))
  -- a preprocess CLAUSIFY split: chain to the recorded input, bridge the proved
  -- output clause (the pushed/pool-root child) back through the if-recursion
  match clausifyInfos with
  | [info] =>
    -- literal items on the same (merged) node come from the PUSH step's
    -- per-literal scan — identity displays only; real rewriting here is a
    -- frontier
    for (_, lp) in lits do
      unless lp.nodes.isEmpty && lp.result == lp.literal do
        throwError "replayClause: non-identity literal item alongside a \
                    clausify record at {cn.idStr} (frontier): {repr lp.literal}"
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
    unless finalT == info.input do
      throwError "replayClause: preprocess chain reached {repr finalT}, the \
                  clausify input is {repr info.input}"
    -- one proof per output clause: a CHILD subgoal, or a post-clausify
    -- DISCHARGE node on a singleton clause
    let mut usedChildren : List String := []
    let mut pOuts : List Expr := []
    for cl in info.out do
      match cn.children.find? (·.inputClause == cl) with
      | some child =>
        usedChildren := usedChildren ++ [child.idStr]
        -- litFacts are INDEX-keyed and clause-scoped — clear at every
        -- child-CLAUSE descent (stale parent entries collide with the
        -- child's numbering); term-keyed channels flow through
        pOuts := pOuts ++ [← replayClauseWith rec cfg { ctx with litFacts := [] } child]
      | none =>
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
    for child in cn.children do
      unless usedChildren.contains child.idStr do
        throwError "replayClause: child {child.idStr} matches no clausify \
                    output at {cn.idStr} (linking gap)"
    let pInput ←
      match pOuts with
      | [pOut] =>
        if info.out.length == 1 then bridgeClausify cfg ctx info pOut
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
  if lits.isEmpty && cn.inputClause.length == 1 then
    -- a SINGLE-literal clause discharged entirely at PREPROCESS: clause-level
    -- step nodes chain the formula to 't (no literal bracketing is emitted at
    -- preprocess sites). A MULTI-literal clause with only step items falls
    -- through to the SPINE — clause-level branch-substitution/equal-self
    -- steps are spine shapes (comm-rm's *1/1.2).
    if stepNodes.isEmpty then
      throwError "replayClause: no literal or step items in clause {cn.idStr} \
                  (discharge composition frontier)"
    unless cn.children.isEmpty do
      throwError "replayClause: preprocess chain with child clauses at {cn.idStr} \
                  (clausify-split frontier)"
    let [formula] := cn.inputClause
      | throwError "replayClause: internal — single-literal guard"
    return ← replayPreprocessChain cfg ctx formula stepNodes
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
