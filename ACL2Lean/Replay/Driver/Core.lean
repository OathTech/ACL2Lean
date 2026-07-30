/-
  Driver/Core — split from Driver/Core (WP2 Stage 3a, 2026-07-17;
  see docs/plans/2026-07-18_driver-modular-refactor.md).

  The clause-level walkers (replayClauseSpineWith/replayClauseWith) and the
  tied knot (replayClause/replayClauseSpine + clauseRec).
-/
import ACL2Lean.Replay.Driver.Waterfall.Compose
import ACL2Lean.Replay.Driver.Waterfall.Fertilize
import ACL2Lean.Replay.Driver.Waterfall.Elim
import ACL2Lean.Replay.Driver.Waterfall.Generalize
import ACL2Lean.Replay.Driver.Waterfall.Subsumed
import ACL2Lean.Replay.Driver.Waterfall.EliminateIrrelevance
import ACL2Lean.Replay.Driver.Waterfall.Induction

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- Replace every occurrence of a TERM by another (quote-opaque) — ACL2's
    `subst-expr` for remove-trivial-equivalences' NON-VARIABLE lhs (the
    `(CDR IT) := 'JUNK` class, G1 inc-2c). On a variable lhs this agrees
    with `substTerm`. -/
partial def replaceTermOcc (src dst : SExpr) (t : SExpr) : SExpr :=
  if t == src then dst
  else match t with
    | .cons h args =>
      match h with
      | .atom (.symbol q) =>
        if q.name == "QUOTE" then t
        else .cons h (replaceArgs args)
      | _ => .cons (replaceTermOcc src dst h) (replaceArgs args)
    | _ => t
where
  replaceArgs : SExpr → SExpr
    | .cons a rest => .cons (replaceTermOcc src dst a) (replaceArgs rest)
    | e => e

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
  | [] =>
    -- SILENT TAUTOLOGY close (G2 rung 2): a branch-substitution can create a
    -- complementary literal pair (qsort's PERM-IMPLIES-EQUAL-ALL-REL-2
    -- *1.5/2.2: X1 := (CAR X-EQUIV) turns (LEXORDER E X1) into the
    -- complement of (NOT (LEXORDER E (CAR X-EQUIV)))); ACL2 recognizes the
    -- taut clause as *t* and closes with NO further records or children.
    -- Gated: only with no pushed children, and only when a pair exists.
    let lits := clauseLits.map (·.2)
    let notOfL : SExpr → SExpr := fun t =>
      .cons (.atom (.symbol { name := "NOT" })) (.cons t .nil)
    if children.isEmpty && lits.any (fun l => lits.contains (notOfL l)) then
      return ← tautClauseClose cfg ctx lits s!"replayClauseSpine at {idStr}"
    throwError "replayClauseSpine: ran out of items with no closer \
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
    -- a WHOLE-CLAUSE verdict discharge at SIMPLIFY time (S1.3 2026-07-23:
    -- the simplify-clause/fc-contradiction and rewrite-clause/type-alist-
    -- contradiction emitters — forward chaining or type-alist construction
    -- over the negated literals reached a contradiction; verdict-only, no
    -- recorded derivation). The node's lhs is the clause's own disjunction,
    -- rhs 't — the ratified DP carve-out discharges the leaf.
    if dischargeOrigins.contains (nodeOrigin n) then
      let dTerm := disjoinTerm (clauseLits.map (·.2))
      unless (nodeLhsRhs n).1 == dTerm do
        throwError "replayClauseSpine: whole-clause discharge node lhs \
                    {repr (nodeLhsRhs n).1} ≠ the clause disjunction \
                    {repr dTerm} at {idStr}"
      unless (nodeLhsRhs n).2 == quoteT do
        throwError "replayClauseSpine: whole-clause discharge node rhs \
                    {repr (nodeLhsRhs n).2} ≠ (quote t) at {idStr}"
      unless rest.isEmpty do
        throwError "replayClauseSpine: items remain after a whole-clause \
                    discharge at {idStr}"
      return ← replayDischargeNode cfg ctx dTerm
    -- a :BRANCH-SUBSTITUTION (remove-trivial-equivalences): ACL2 substitutes
    -- `var := val` THROUGHOUT the clause, justified by the clause's own
    -- `(not (equal var val))` literal, and scans the SUBSTITUTED literals.
    -- Mirror: byCases on that literal's value — truthy closes the clause;
    -- nil gives the value equality, `diffCollapse` transports the whole
    -- disjunction to the substituted clause, and the walk continues there.
    if (runeOf n).ty == "branch-substitution" then
      let .node _ varT valT _ prov := n
      -- :EQUIVALENCE is the RELATION the substitution is justified under.
      -- NON-EQUAL relation (perm — G2 rung 2): remove-trivial-equivalences
      -- substitutes var := val at congruence-admissible positions and deletes
      -- the used `(not (R var val))` literal. The OBSERVED class (qsort's
      -- PERM-IMPLIES-EQUAL-ALL-REL-2, 10 sites) has the variable occurring
      -- ONLY in the justifying literal — the substitution elsewhere is
      -- vacuous, so the mirror is pure clause structure: byCases on the
      -- literal; truthy closes the disjunction (the literal is true), falsity
      -- collapses its if-frame out (exactly ACL2's case analysis — under
      -- (R var val) the used literal is dropped; no R-facts are consumed
      -- because nothing else changes). An occurrence OUTSIDE the justifying
      -- literal needs the R-congruence transport — a named frontier.
      if prov.equivTerm != some (.atom (.symbol { name := "EQUAL" })) then
        let some (.atom (.symbol rSym)) := prov.equivTerm
          | throwError "replayClauseSpine: branch-substitution :EQUIVALENCE \
              {repr prov.equivTerm} is not a symbol at {idStr}"
        let mkNegRel (x y : SExpr) : SExpr :=
          .cons (.atom (.symbol { name := "NOT" }))
            (.cons (.cons (.atom (.symbol rSym))
              (.cons x (.cons y .nil))) .nil)
        let some (negLit, kIdx) :=
          (match clauseLits.find? (fun (_, l) => l == mkNegRel varT valT) with
           | some (i, l) => some (l, i)
           | none =>
             (clauseLits.find? (fun (_, l) => l == mkNegRel valT varT)).map
               (fun (i, l) => (l, i)) : Option (SExpr × Nat))
          | throwError "replayClauseSpine: branch-substitution under \
              {rSym.name} — justifying literal (not ({rSym.name} \
              {repr varT} {repr valT})) is not a clause literal at {idStr} \
              (frontier — in-clause only for non-equal relations)"
        let substNE : SExpr → SExpr :=
          match varT with
          | .atom (.symbol varSym) => ACL2.Replay.substTerm [varSym] [valT]
          | _ => replaceTermOcc varT valT
        for (i, l) in clauseLits do
          if i != kIdx && substNE l != l then
            throwError "replayClauseSpine: branch-substitution under \
                {rSym.name} — {repr varT} occurs outside the justifying \
                literal (in {repr l}) at {idStr} (frontier — congruence \
                transport pending)"
        let kPos := clauseLits.findIdx (fun (i, _) => i == kIdx)
        unless kPos + 1 < clauseLits.length do
          throwError "replayClauseSpine: branch-substitution under \
              {rSym.name} with the justifying literal LAST at {idStr} \
              (frontier)"
        let ctx1 ← pinTermOpaques cfg cfg.envExpr ctx
          (disjoinTerm (clauseLits.map (·.2)))
        let vK ← ctxValExpr cfg ctx1 negLit
        let pK ← ctxValProof cfg ctx1 negLit
        let nilC := mkConst ``SExpr.nil
        let negL ← withLocalDeclD `hnil (← mkEq vK nilC) fun hNil => do
          -- the literal's if-frame collapses out of the disjunction by its
          -- own falsity, lifted through the kPos else-descents above it
          let hcNil ← mkAppM ``re_val_cast
            #[cfg.worldExpr, cfg.envExpr, reflectSExpr negLit, vK, nilC,
              pK, hNil]
          let tailTerm := disjoinTerm ((clauseLits.drop (kPos + 1)).map (·.2))
          let vTail ← ctxValExpr cfg ctx1 tailTerm
          let hTail ← ctxValProof cfg ctx1 tailTerm
          let mut inner ← mkAppM ``re_if_false
            #[cfg.worldExpr, cfg.envExpr, reflectSExpr negLit,
              reflectSExpr quoteT, reflectSExpr tailTerm, vTail, hcNil, hTail]
          let mut curL : SExpr := .cons (.atom (.symbol { name := "IF" }))
            (.cons negLit (.cons quoteT (.cons tailTerm .nil)))
          let mut curR : SExpr := tailTerm
          for (_, l) in (clauseLits.take kPos).reverse do
            let st : PathStep := { fn := { name := "IF" }, arity := 3,
                                   argIdx := 2, siblings := [l, quoteT] }
            inner ← applyStep cfg.worldExpr cfg.envExpr st curL curR inner
            curL := rebuild st curL
            curR := rebuild st curR
          let shortened := (clauseLits.eraseIdx kPos).zipIdx.map
            fun ((_, l), j) => (j + 1, l)
          unless curL == disjoinTerm (clauseLits.map (·.2)) &&
                 curR == disjoinTerm (shortened.map (·.2)) do
            throwError "replayClauseSpine: branch-substitution ({rSym.name}) \
                deletion lift reconstructed {repr curL} / {repr curR} at \
                {idStr}"
          let pRest ← replayClauseSpineWith rec cfg ctx1 idStr shortened rest
            accClause children
          let p ← mkAppM ``evtrue_of_fuel_eq #[inner, pRest]
          mkLambdaFVars #[hNil] p
        let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[vK, nilC]) fun hNe => do
          -- kPos, not kIdx-1: recorded indices are not positions once the
          -- walk has descended past earlier literals (audit F2 — the
          -- branch-descent continuations keep ORIGINAL indices)
          let p ← evtrueOfLitTrue cfg ctx1 (clauseLits.map (·.2)) kPos
            negLit hNe
          mkLambdaFVars #[hNe] p
        return ← (try mkAppM ``Classical.byCases #[negL, posL]
          catch e => throwError "byCases compose failed at {idStr}:\n{e.toMessageData}")
      -- the substitution: a VARIABLE lhs uses substTerm; a non-variable
      -- lhs (the `(CDR IT) := 'JUNK` class) replaces occurrences of the
      -- TERM — ACL2's subst-expr (G1 inc-2c)
      let substL : SExpr → SExpr :=
        match varT with
        | .atom (.symbol varSym) => ACL2.Replay.substTerm [varSym] [valT]
        | _ => replaceTermOcc varT valT
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
          (i, substL l)
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
          let l' := substL l
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
          let st' := substL st
          if st' != st then
            ctx2 ← pinTermOpaques cfg cfg.envExpr ctx2 st'
            let some chL ← diffCollapse cfg.worldExpr cfg.envExpr varT valT nodeEq st st'
              | throwError "replayClauseSpine: branch-substitution fact \
                            transport of {repr st} produced no chain at {idStr}"
            let vEq ← mkAppM ``val_eq_of_eval_eq
              #[chL, ← ctxValProof cfg ctx2 st, ← ctxValProof cfg ctx2 st']
            let h' ← mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[vEq], h]
            ctx2 := { ctx2 with segFacts := ctx2.segFacts ++ [(st', h')] }
        -- ACL2's subst-equiv-expr CONS-TERM-FOLDS during substitution; the
        -- fork records each fold as an SCONS-TERM/EXEC step (G1 inc-2c:
        -- (ORDD 'JUNK) ⇒ 'T under (CDR IT) := 'JUNK). Consume the leading
        -- fold records — each is an exec-ground fact applied to the
        -- substituted literals — then DROP any literal folded to 'NIL
        -- (ACL2's add-literal drops nils), collapsing its if-frame out of
        -- the disjunction, and RENUMBER (deletion shifts later indices).
        let mut curLits := substLits
        let mut extraChains : List Expr := []
        let mut restI := rest
        repeat
          match restI with
          | .step nf :: restT =>
            if nodeOrigin nf == "scons-term/exec" then
              let (fLhs, fRhs) := nodeLhsRhs nf
              let .cons (.atom (.symbol q)) (.cons fv .nil) := fRhs
                | throwError "replayClauseSpine: scons-term/exec rhs \
                    {repr fRhs} is not a quoted constant at {idStr}"
              unless q.name == "QUOTE" do
                throwError "replayClauseSpine: scons-term/exec rhs \
                    {repr fRhs} is not a quoted constant at {idStr}"
              let conv ← replayExecGround cfg fLhs fv
              let hq ← mkAppM ``re_val_quote
                #[cfg.worldExpr, cfg.envExpr, reflectSExpr fv]
              let foldEq ← mkAppM ``fuel_eq_of_conv
                #[conv, hq, ← mkEqRefl (reflectSExpr fv)]
              let nextLits := curLits.map fun (i, l) =>
                (i, replaceTermOcc fLhs fRhs l)
              -- consume the LEADING RUN of folds that change the clause,
              -- stopping at the first that does not — it and everything
              -- after stay in the item stream for their own consumers
              -- (APP-NIL's (CONSP 'NIL); audit Q3: prefix consumption,
              -- not a filter)
              if nextLits == curLits then break
              let some fc ← diffCollapse cfg.worldExpr cfg.envExpr fLhs fRhs
                  foldEq (disjoinTerm (curLits.map (·.2)))
                  (disjoinTerm (nextLits.map (·.2)))
                | throwError "replayClauseSpine: scons-term/exec fold \
                    {repr fLhs} produced no chain at {idStr} (internal)"
              extraChains := extraChains ++ [fc]
              curLits := nextLits
              restI := restT
            else break
          | _ => break
        repeat
          let some pos := (curLits.map (·.2)).idxOf? quoteNil | break
          let before := curLits.take pos
          let after := curLits.drop (pos + 1)
          if after.isEmpty then
            throwError "replayClauseSpine: literal folded to 'NIL in LAST \
                position at {idStr} (frontier)"
          let afterT := disjoinTerm (after.map (·.2))
          let (dropEq, _) ← mkConstTestCollapse cfg ctx1 quoteNil SExpr.nil
            quoteT afterT
          let mut inner := dropEq
          let mut curL : SExpr := .cons (.atom (.symbol { name := "IF" }))
            (.cons quoteNil (.cons quoteT (.cons afterT .nil)))
          let mut curR : SExpr := afterT
          for l in (before.map (·.2)).reverse do
            let stp : PathStep := { fn := { name := "IF" }, arity := 3,
                                    argIdx := 2, siblings := [l, quoteT] }
            inner ← applyStep cfg.worldExpr cfg.envExpr stp curL curR inner
            curL := rebuild stp curL
            curR := rebuild stp curR
          unless curL == disjoinTerm (curLits.map (·.2)) do
            throwError "replayClauseSpine: nil-literal drop reconstructed \
                {repr curL} ≠ the folded clause at {idStr}"
          extraChains := extraChains ++ [inner]
          -- renumber: deletion shifts the LATER literals' indices down
          curLits := before ++ after.map (fun (i, l) => (i - 1, l))
        let chainAll ← extraChains.foldlM (init := chainOpt) fun acc c => do
          match acc with
          | none => pure (some c)
          | some a => pure (some (← mkAppM ``fuel_chain_eq #[a, c]))
        ctx2 ← pinTermOpaques cfg cfg.envExpr ctx2
          (disjoinTerm (curLits.map (·.2)))
        -- the substituted continuation may sit INSIDE a branch item whose
        -- segment is the JUSTIFYING equality literal itself (its falsity is
        -- the segEq fact already in scope) — enter it, joining the segment
        -- to the residual clause exactly as ACL2's new-clause does
        let (curItems, accClause') ←
          match restI with
          | [.branch seg items] => do
            let some segL := seg.toList?
              | throwError "replayClauseSpine: post-substitution branch \
                  segment {repr seg} is not a list at {idStr}"
            unless segL == [mkNegEq varT valT] || segL == [mkNegEq valT varT] do
              throwError "replayClauseSpine: post-substitution branch segment \
                  {repr segL} is not the justifying equality at {idStr} \
                  (frontier)"
            pure (items, accClause ++ segL.filter (!accClause.contains ·))
          | _ => pure (restI, accClause)
        if curItems.isEmpty && curLits.isEmpty then
          -- VACUOUS (G1 inc-2c): the substitution closed the branch — the
          -- pushed child is the SUBSTITUTED accumulated clause, every
          -- literal of which has an in-scope (transported) falsity fact;
          -- ex falso closes the empty disjunction (the composer's vacuous
          -- residual pattern; p3-conj *1/2.2).
          -- the justifying equality literal itself stays UNSUBSTITUTED
          -- (remove-trivial-equivalences substitutes the OTHER literals)
          let expected := accClause'.map fun L =>
            if L == mkNegEq varT valT || L == mkNegEq valT varT then L
            else substL L
          let some child := children.find? (·.inputClause == expected)
            | throwError "replayClauseSpine: post-substitution vacuous \
                residual — no child matches {repr expected} at {idStr} \
                (frontier)"
          let mut ctxV := ctx2
          for L in expected do
            ctxV ← pinTermOpaques cfg cfg.envExpr ctxV L
          let pChild ← rec.clause cfg { ctxV with litFacts := [] } child
          let ctxF := ctxV
          return ← vacuousResidualClose cfg ctxV expected pChild
            (disjoinTerm []) fun L => do
              match ctxF.litFactByTerm? L with
              | some hf => pure hf
              | none => throwError "replayClauseSpine: no falsity fact for \
                  the vacuous-residual literal {repr L} at {idStr}"
        if curItems.isEmpty && !curLits.isEmpty then
          -- RESIDUAL: no continuation items — the substituted clause was
          -- pushed as a child subgoal (the composer's empty-cont pattern):
          -- match it, replay, peel the accumulated segments down to the
          -- surviving literal, bridge back along the substitution chain
          let expected := accClause' ++
            (curLits.map (·.2)).filter (!accClause'.contains ·)
          let some child := children.find? (·.inputClause == expected)
            | throwError "replayClauseSpine: post-substitution residual — no \
                child clause matches {repr expected} at {idStr} (frontier)"
          unless curLits.length == 1 &&
              expected.getLast? == some (curLits.head!.2) do
            throwError "replayClauseSpine: post-substitution residual with \
                {curLits.length} surviving literal(s) at {idStr} (frontier)"
          let pChild ← rec.clause cfg { ctx2 with litFacts := [] } child
          let p ← peelToLast cfg ctx2 expected pChild fun L => do
            match ctx2.litFactByTerm? L with
            | some hf => pure hf
            | none => throwError "replayClauseSpine: no falsity fact for the \
                post-substitution residual literal {repr L} at {idStr}"
          return ← evtrueWith chainAll p
        let p ← replayClauseSpineWith rec cfg ctx2 idStr curLits curItems accClause' children
        return ← evtrueWith chainAll p
      let some ((ta, tb), kIdx) := inClause?
        | throwError "replayClauseSpine: internal — inClause? vanished"
      let negEq : SExpr := mkNegEq ta tb
      let mut ctx := ctx
      ctx ← pinTermOpaques cfg cfg.envExpr ctx valT
      let vK ← ctxValExpr cfg ctx negEq
      let pK ← ctxValProof cfg ctx negEq
      let nilC := mkConst ``SExpr.nil
      let kPos := clauseLits.findIdx (fun (i, _) => i == kIdx)
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
          (i, substL l)
        -- the SUBSTITUTED literals are new terms — pin their user-fn opaques
        -- before any value construction over them
        let ctx ← pinTermOpaques cfg cfg.envExpr ctx
          (disjoinTerm (substLits.map (·.2)))
        let chainOpt ← diffCollapse cfg.worldExpr cfg.envExpr varT valT nodeEq
          (disjoinTerm (clauseLits.map (·.2))) (disjoinTerm (substLits.map (·.2)))
        -- remove-trivial-equivalences also DELETES the used literal — now the
        -- trivial `(not (equal v v))` — from the clause it scans; collapse its
        -- if-frame out of the disjunction (its value is nil by reflexivity)
        if kPos + 1 == clauseLits.length then
          -- the used literal is LAST: deleting it changes nothing any later
          -- record references (there are none after it) — keep the trivial
          -- literal in the walked clause and continue on the substituted
          -- literals directly (EQUAL-CONS Subgoal 4, chained substitutions)
          let pRest ← replayClauseSpineWith rec cfg ctx idStr substLits rest
            accClause children
          let p ← evtrueWith chainOpt pRest
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
          curL := rebuild st curL
          curR := rebuild st curR
        unless curL == disjoinTerm (substLits.map (·.2)) &&
               curR == disjoinTerm (shortened.map (·.2)) do
          throwError "replayClauseSpine: branch-substitution shortening lift \
                      reconstructed {repr curL} / {repr curR} at {idStr}"
        let chainAll ← chainAfter chainOpt inner
        let pRest ← replayClauseSpineWith rec cfg ctx idStr shortened rest accClause children
        let p ← mkAppM ``evtrue_of_fuel_eq #[chainAll, pRest]
        mkLambdaFVars #[hNil] p
      let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[vK, nilC]) fun hNe => do
        -- kPos, not kIdx-1 (audit F2 — same coordinate fix as the R arm)
        let p ← evtrueOfLitTrue cfg ctx (clauseLits.map (·.2)) kPos negEq hNe
        mkLambdaFVars #[hNe] p
      let _ := pK
      return ← (try mkAppM ``Classical.byCases #[negL, posL]
        catch e => throwError "byCases compose failed at {idStr}:\nnegL : {← Lean.Meta.inferType negL}\nposL : {← Lean.Meta.inferType posL}\n{e.toMessageData}")
    -- a clause-level EQUAL-SELF step: the literal (equal X X) is TRUE by
    -- reflexivity and closes the whole disjunction (comm-rm's *1/1.2 after
    -- its branch-substitution trivializes the conclusion)
    if (runeOf n).ty == "equal-self" then
      -- this step CLOSES the clause; trailing spine items would be silently
      -- unreplayed — fail closed (audit #3 hardening). (An S1.3 interim
      -- verify-then-drop for a trailing discharge item was REMOVED, MDD
      -- 2026-07-23: the item was the fc-contradiction emitter firing
      -- degenerately on the settled-down pass's residual *true-clause* —
      -- fixed at the EMITTER with a *true-clause* gate, no walker epicycle.)
      unless rest.isEmpty do
        throwError "replayClauseSpine: {rest.length} spine item(s) after a \
                    closing clause-level equal-self at {idStr} (frontier); \
                    first: {match rest.head? with
                            | some (.step m) => s!"step {(runeOf m).ty}/{nodeOrigin m}"
                            | some (.literal lp) => s!"literal {lp.index}"
                            | some (.clausify _) => "clausify"
                            | some (.branch ..) => "branch"
                            | none => "none"}"
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
      return ← evtrueWith chainOpt p
    -- a clause-level HYP-RELIEF marker (`:ORIGIN RELIEVE-HYP/TYPE-ALIST`,
    -- sorting arc 2026-07-28): the FOLLOWING step's rule hypothesis was
    -- silently relieved from the type-alist — no term change (lhs == rhs,
    -- enforced), and the relieved fact's effect on that step's rhs is
    -- carried by the step's own recorded children (recognizer/true +
    -- if-simplification resolving the unfolded body). Consume as a spine
    -- no-op; any shape with lhs ≠ rhs stays a loud frontier.
    if (runeOf n).ty == "hyp-relief" then
      let (lhs, rhs) := nodeLhsRhs n
      unless lhs == rhs do
        throwError "replayClauseSpine: clause-level hyp-relief with lhs \
                    {repr lhs} ≠ rhs {repr rhs} at {idStr} (frontier)"
      return ← replayClauseSpineWith rec cfg ctx idStr clauseLits rest accClause children
    -- clause-level SETUP-phase rewriter memos (sorting arc 2026-07-28): the
    -- linear-pot/type-alist setup rewrites terms BEFORE the literal walk
    -- (emitted between CLAUSIFY-OUT and the first BEGIN-LITERAL — e.g.
    -- (ACL2-COUNT X2)'s unfold under the relieved (CONSP X2) in admission
    -- waterfalls). They do NOT transform the clause: the literal chains
    -- RE-RECORD and validate the same rewrites where they act (qsort *1/4's
    -- literal 4 carries its own definition:ACL2-COUNT step). Consume as a
    -- no-op — if a memo's effect were real and un-re-recorded, the spine's
    -- end validation against the recorded child clauses fails loudly.
    if (runeOf n).ty == "definition" then
      -- POSITIONAL gate (audit F2): the setup-phase claim is enforced, not
      -- assumed — these memos precede the first literal item; a clause-level
      -- definition step appearing mid-walk stays a loud frontier.
      unless accClause.isEmpty do
        throwError "replayClauseSpine: clause-level definition step after \
                    literal items at {idStr} (not a setup-phase memo — \
                    frontier)"
      return ← replayClauseSpineWith rec cfg ctx idStr clauseLits rest accClause children
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
    let demanded := (lp.nodes.flatMap collectContextDemands ++
      lp.nodes.flatMap (collectDefBodyDemands cfg)).eraseDups
    -- "fact in scope" must mean a WELL-TYPED fact (sorting-completion-2
    -- class A: an env-crossed segFact leaked from a parent elim walk
    -- satisfies the UNCHECKED lookup, suppressing the hoist — and then the
    -- consumer's CHECKED lookup rightly refuses the same entry, stranding
    -- the replay. The unchecked/checked asymmetry is the same class the
    -- perm-lane audit's F8 fixed at the eqSources loop.)
    let inScopeChecked : SExpr → MetaM Bool := fun t => do
      let ctxT ← pinTermOpaques cfg cfg.envExpr ctx t
      let vT ← ctxValExpr cfg ctxT t
      pure (← ctxT.litFactByTermChecked? t
        (← mkEq vT (mkConst ``SExpr.nil))).isSome
    for dem in demanded do
      -- resolve the demand to a LATER clause literal (index, term) with no
      -- fact in scope; anything else is skipped — the consumer fails
      -- precisely if the fact is genuinely missing
      let resolved : Option (Nat × SExpr) ←
        match dem with
        | .term t => do
          if ← inScopeChecked t then pure none
          else pure ((restLits.find? (fun (_, l) => l == t)).map fun (i, _) => (i, t))
        | .litIdx k =>
          -- by-INDEX facts come from the same walk (never env-crossed)
          if (ctx.litFact? k).isSome then pure none
          else pure (restLits.find? (fun (i, _) => i == k))
        | .equivClass a b => do
          -- the connected component of {a, b} over ALL the clause's equality
          -- literals (grown to fixpoint), then the first LATER equality
          -- literal in it lacking a WELL-TYPED in-scope fact — one hoist
          -- per re-entry
          let eqLits := clauseLits.filterMap fun (i, l) =>
            (notEqualSides? l).map fun (u, v) => (i, l, u, v)
          let comp := Id.run do
            let mut comp : List SExpr := [a, b]
            for _ in List.range (eqLits.length + 1) do
              for (_, _, u, v) in eqLits do
                if comp.contains u || comp.contains v then
                  if !comp.contains u then comp := comp ++ [u]
                  if !comp.contains v then comp := comp ++ [v]
            return comp
          let mut found : Option (Nat × SExpr) := none
          for (i, l) in restLits do
            if found.isNone then
              if let some (u, v) := notEqualSides? l then
                if (comp.contains u || comp.contains v) &&
                    (ctx.litFact? i).isNone then
                  unless ← inScopeChecked l do
                    found := some (i, l)
          pure found
      let some (k, notH) := resolved | continue
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
      return ← (try mkAppM ``Classical.byCases #[negL, posL]
        catch e => throwError "byCases compose failed at {idStr}:\nnegL : {← Lean.Meta.inferType negL}\nposL : {← Lean.Meta.inferType posL}\n{e.toMessageData}")
    -- a literal that IS the ground constant 't (post-substitution ground
    -- evaluation reduced it), reported true by rewrite-atm's type-set
    -- (ATM/TYPE-SET-TRUE, :RESULT :TRUE — APP-NIL Subgoal *1/3): the clause
    -- closes on the literally-true literal, no chain to replay.
    if lp.literal == quoteT && lp.result == .atom (.keyword "TRUE") then
      return ← closeOnTrueLit cfg lp.literal (restLits.map (·.2)) (← quoteTFact cfg)
    if lp.result == quoteT then
      -- the closer: its chain proves it `t`; any later literals (scanned or
      -- not) are short-circuited by the true test.
      unless branchSegs.isEmpty do
        throwError "replayClauseSpine: branches after the closing literal \
                    {idx} at {idStr} (frontier)"
      let pclose ← replayLiteral cfg ctx lp
      closeOnTrueLit cfg lp.literal (restLits.map (·.2)) pclose
    else
      -- the literal's rewrite chain: literal ⇒ result
      let (chainOpt, finalT) ← replayLiteralChain cfg ctx lp
      let chainOpt ← do
        if finalT == lp.result then pure chainOpt else
        -- rewrite-equal's unrecorded NIL normalization at the chain end
        match ← bridgeEqualNilNorm cfg ctx finalT lp.result with
        | some br => match chainOpt with
          | none => pure (some ((br, false) : Expr × Bool))
          | some (ch, false) =>
            pure (some (← mkAppM ``fuel_chain_eq #[ch, br], false))
          | some (ch, true) => do
            -- append the eq bridge to an IFF chain (G1 inc-2b)
            let pConv ← ctxValProof cfg ctx lp.result
            let brS ← mkAppM ``evrel_of_fuel_eq #[mkConst ``siff_refl, br, pConv]
            pure (some (← mkAppM ``evrel_trans #[mkConst ``siff_trans, ch, brS], true))
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
        | [(segA, contA), (segB, contB)] => do
          -- AND-SHAPE conjunction strip (inc-2a, sorting arc 2026-07-29 —
          -- recon from the real ORDEREDP-ISORT record): the literal's
          -- rewritten result is `(IF L R 'NIL)` clausified by
          -- STRIP-BRANCHES/AND-SHAPE into TWO segment-open branches
          -- `[L]`/`[R]` with NO if-interp split test. Compose by value
          -- cases: the parent literal nil forces ONE conjunct nil (the
          -- left directly, or the right under a truthy left —
          -- `cond_true_nil_forces_r`), and that branch's continuation
          -- (walked under its segment-false fact) carries the rest.
          let (ifS, L, R) ← match lp.result with
            | .cons (.atom (.symbol ifS))
                (.cons L (.cons R (.cons e .nil))) =>
              if ifS.name == "IF" && e == quoteNil then pure (ifS, L, R)
              else throwError "replayClauseSpine: 2 branches on literal \
                {idx} but the result is not an AND-shape at {idStr} \
                (frontier)"
            | _ => throwError "replayClauseSpine: 2 branches on literal \
                {idx} but the result is not an AND-shape at {idStr} \
                (frontier)"
          let _ := ifS
          let segLitsOf (s : SExpr) : MetaM (List SExpr) := do
            let some l := s.toList?
              | throwError "replayClauseSpine: conjunction branch segment \
                  {repr s} is not a list at {idStr}"
            pure l
          let sA ← segLitsOf segA
          let sB ← segLitsOf segB
          let (contL, contR, segLLits, segRLits) ←
            if sA == [L] && sB == [R] then pure (contA, contB, sA, sB)
            else if sA == [R] && sB == [L] then pure (contB, contA, sB, sA)
            else throwError "replayClauseSpine: conjunction branch segments \
                {repr sA} / {repr sB} ≠ the AND-shape conjuncts at {idStr} \
                (frontier)"
          -- LEAF validation (audit F-B — the 1-branch arm's sibling check):
          -- an AND-shape strip records exactly two SEGMENT-OPEN leaves whose
          -- values are the conjuncts; anything else is a divergence.
          let leaves := lp.splitTrace.filterMap fun
            | .leaf v outcome _ _ => some (v, outcome)
            | _ => none
          unless leaves.length == 2 &&
              leaves.all (fun (_, o) => o == "segment-open") &&
              (leaves.map (·.1) == [L, R] || leaves.map (·.1) == [R, L]) do
            throwError "replayClauseSpine: conjunction trace leaves \
                {repr (leaves.map (·.1))} are not the two SEGMENT-OPEN \
                conjuncts at {idStr} (frontier)"
          let ctx ← pinTermOpaques cfg cfg.envExpr ctx lp.result
          let vLit ← ctxValExpr cfg ctx lp.literal
          let pLit ← ctxValProof cfg ctx lp.literal
          -- LAST-literal conjunction: both conjunct clauses were PUSHED as
          -- children — peel each to its conjunct's truth; both truthy makes
          -- the literal's AND-value truthy, closing the singleton spine.
          if restLits.isEmpty && contL.isEmpty && contR.isEmpty then
            let childProof (seg : List SExpr) : MetaM Expr := do
              let accClause' := accClause ++ seg.filter (!accClause.contains ·)
              let some child := children.find? (·.inputClause == accClause')
                | throwError "replayClauseSpine: no child clause matches the \
                    conjunction residual {repr accClause'} at {idStr}"
              let pChild ← rec.clause cfg { ctx with litFacts := [] } child
              peelToLast cfg ctx accClause' pChild fun Lt => do
                let some hf := ctx.litFactByTerm? Lt
                  | throwError "replayClauseSpine: no falsity fact for the \
                      conjunction residual literal {repr Lt} at {idStr}"
                pure hf
            let pL ← childProof segLLits
            let pR ← childProof segRLits
            let cL ← ctxValProof cfg ctx L
            let cR ← ctxValProof cfg ctx R
            let hLne ← mkAppM ``ne_nil_of_evtrue_conv #[pL, cL]
            let hRne ← mkAppM ``ne_nil_of_evtrue_conv #[pR, cR]
            let hbT ← mkAppM ``toBool_true_of_ne_nil #[hLne]
            let vR ← ctxValExpr cfg ctx R
            let hCond ← mkAppM ``cond_true_val
              #[vR, mkConst ``SExpr.nil, hbT]
            let pRes ← ctxValProof cfg ctx lp.result
            let some (ch, chIff) := chainOpt
              | throwError "replayClauseSpine: conjunction literal without a \
                  rewrite chain at {idStr} (internal)"
            let hNe ←
              if chIff then do
                -- IFF chain: the result's truthy AND-value transports back
                -- through the SIff contrapositive (G1 inc-2b)
                let hResNe ← mkAppM ``ne_nil_of_eq #[hCond, hRne]
                mkAppM ``siff_val_ne_nil_transport #[ch, pLit, pRes, hResNe]
              else do
                let vEq ← mkAppM ``val_eq_of_eval_eq #[ch, pLit, pRes]
                let hEq2 ← mkAppM ``Eq.trans #[vEq, hCond]
                mkAppM ``ne_nil_of_eq #[hEq2, hRne]
            return ← mkAppM ``evtrue_of_conv_ne_nil #[pLit, hNe]
          let restTerm := disjoinTerm (restLits.map (·.2))
          let neTy ← mkAppM ``Ne #[vLit, mkConst ``SExpr.nil]
          let hthen ← withLocalDeclD `h neTy fun h => do
            let p ← mkAppM ``evtrue_of_eq_t #[← quoteTFact cfg]
            let _ := h
            mkLambdaFVars #[h] p
          let eqTy ← mkEq vLit (mkConst ``SExpr.nil)
          let mkElseBodyC (h : Expr) : MetaM Expr := do
            let some (ch, chIff) := chainOpt
              | throwError "replayClauseSpine: conjunction literal without \
                  a rewrite chain at {idStr} (internal)"
            let vRes ← ctxValExpr cfg ctx lp.result
            let pRes ← ctxValProof cfg ctx lp.result
            -- hRes : v(IF L R 'NIL) = nil, i.e. cond (toBool vL) vR nil = nil
            let hRes ←
              if chIff then
                mkAppM ``siff_val_nil_transport #[ch, pLit, pRes, h]
              else do
                let vEq ← mkAppM ``val_eq_of_eval_eq #[ch, pLit, pRes]
                mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[vEq], h]
            let vL ← ctxValExpr cfg ctx L
            let branch (conjTerm : SExpr) (conjNil : Expr)
                (cont : List ClauseItem) (segL : List SExpr) : MetaM Expr := do
              let ctx' := { ctx with
                litFacts := ctx.litFacts ++ [(idx, conjTerm, conjNil)] }
              let accClause' := accClause ++ segL.filter (!accClause.contains ·)
              replayClauseSpineWith rec cfg ctx' idStr restLits cont
                accClause' children
            let nilTyL ← mkEq vL (mkConst ``SExpr.nil)
            let negL ← withLocalDeclD `hL nilTyL fun hL => do
              mkLambdaFVars #[hL] (← branch L hL contL segLLits)
            let posL ← withLocalDeclD `hL (← mkAppM ``Ne
                #[vL, mkConst ``SExpr.nil]) fun hL => do
              let hbTrue ← mkAppM ``toBool_true_of_ne_nil #[hL]
              let hRnil ← mkAppM ``cond_true_nil_forces_r #[hRes, hbTrue]
              mkLambdaFVars #[hL] (← branch R hRnil contR segRLits)
            (try mkAppM ``Classical.byCases #[negL, posL]
              catch e => throwError "byCases compose failed at {idStr}:\nnegL : {← Lean.Meta.inferType negL}\nposL : {← Lean.Meta.inferType posL}\n{e.toMessageData}")
          -- SINGLETON spine (G1 inc-2c): the goal is the BARE literal —
          -- dp_if_split's (IF l 'T 'NIL) conclusion would mismatch; byCases
          -- directly, the nil branch's EvTrue 'NIL closing ex falso.
          if restLits.isEmpty then
            let posT ← withLocalDeclD `h neTy fun h => do
              mkLambdaFVars #[h] (← mkAppM ``evtrue_of_conv_ne_nil #[pLit, h])
            let negT ← withLocalDeclD `h eqTy fun h => do
              let pBody ← mkElseBodyC h
              let goalTy ← mkAppM ``EvTrue
                #[cfg.worldExpr, cfg.envExpr, reflectSExpr lp.literal]
              let hFalse ← mkAppM ``evtrue_quote_nil_false #[pBody]
              mkLambdaFVars #[h]
                (← mkAppOptM ``False.elim #[some goalTy, some hFalse])
            return ← (try mkAppM ``Classical.byCases #[negT, posT]
              catch e => throwError "singleton mid-lit compose failed at \
                {idStr}:\n{e.toMessageData}")
          let helse ← withLocalDeclD `h eqTy fun h => do
            mkLambdaFVars #[h] (← mkElseBodyC h)
          return ← (try
            mkAppM ``evtrue_dp_if_split
              #[cfg.worldExpr, cfg.envExpr, reflectSExpr lp.literal,
                reflectSExpr quoteT, reflectSExpr restTerm, vLit, pLit,
                hthen, helse]
            catch e =>
              throwError "dp_if_split compose failed at {idStr} (mid-lit):\n{e.toMessageData}")
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
          return ← vacuousResidualClose cfg ctx accClause' pChild lp.literal
            fun L => do
              let some hf := ctx.litFactByTerm? L
                | throwError "replayClauseSpine: no falsity fact for the \
                              residual literal {repr L} at {idStr}"
              pure hf
        unless accClause'.getLast? == some lp.result do
          throwError "replayClauseSpine: residual's surviving literal is not \
                      literal {idx}'s result at {idStr} (frontier)"
        let pChild ← rec.clause cfg { ctx with litFacts := [] } child
        let p ← peelToLast cfg ctx accClause' pChild fun L => do
          let some hf := ctx.litFactByTerm? L
            | throwError "replayClauseSpine: no falsity fact for the residual \
                          literal {repr L} at {idStr}"
          pure hf
        -- p : EvTrue(lp.result) — bridge to the pre-rewrite literal
        return ← evtrueWithR chainOpt p
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
      let mkElseBody (h : Expr) : MetaM Expr := do
        let (factTerm, factProof) ←
          match chainOpt with
          | none => pure (lp.literal, h)
          | some (ch, false) => do
            -- bridge the falsity to the post-rewrite literal
            let _vLit' ← ctxValExpr cfg ctx lp.result
            let pLit' ← ctxValProof cfg ctx lp.result
            let vEq ← mkAppM ``val_eq_of_eval_eq #[ch, pLit, pLit']
            pure (lp.result, ← mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[vEq], h])
          | some (ch, true) => do
            let pLit' ← ctxValProof cfg ctx lp.result
            pure (lp.result,
              ← mkAppM ``siff_val_nil_transport #[ch, pLit, pLit', h])
        let ctx' := { ctx with litFacts := ctx.litFacts ++ [(idx, factTerm, factProof)] }
        let accClause' := accClause ++ segLits.filter (!accClause.contains ·)
        replayClauseSpineWith rec cfg ctx' idStr restLits contItems accClause' children
      if restLits.isEmpty then
        -- SINGLETON spine (G1 inc-2c): the goal is the BARE literal
        -- (disjoinTerm [l] = l) — the dp_if_split shape would conclude
        -- (IF l 'T 'NIL) and mismatch. byCases directly: a truthy value
        -- closes; the nil branch's continuation proves the EMPTY
        -- disjunction ('NIL) — absurd, ex falso closes.
        let posL ← withLocalDeclD `h neTy fun h => do
          mkLambdaFVars #[h] (← mkAppM ``evtrue_of_conv_ne_nil #[pLit, h])
        let negL ← withLocalDeclD `h eqTy fun h => do
          let p ← mkElseBody h
          let goalTy ← mkAppM ``EvTrue
            #[cfg.worldExpr, cfg.envExpr, reflectSExpr lp.literal]
          let hFalse ← mkAppM ``evtrue_quote_nil_false #[p]
          mkLambdaFVars #[h] (← mkAppOptM ``False.elim #[some goalTy, some hFalse])
        return ← (try
          mkAppM ``Classical.byCases #[negL, posL]
          catch e =>
            throwError "singleton-spine compose failed at {idStr}:\n{e.toMessageData}")
      let helse ← withLocalDeclD `h eqTy fun h => do
        mkLambdaFVars #[h] (← mkElseBody h)
      (try
        mkAppM ``evtrue_dp_if_split
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr lp.literal, reflectSExpr quoteT,
            reflectSExpr restTerm, vLit, pLit, hthen, helse]
        catch e =>
          throwError "dp_if_split compose failed at {idStr} (trivial):\n{e.toMessageData}")

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
  -- a FERTILIZE node (cross-fertilization): the emitted :FERTILIZE detail
  -- links the substitution to its justifying clause literal; replayFertilize
  -- byCases the literal, transports the disjunction onto the substituted
  -- clause, and closes via the child (emission arc, 2026-07-21). The step's
  -- items are the PRECEDING simplify miss's flushed events — not this
  -- transformation's record — and are deliberately not consumed.
  if let some st := cn.steps.find? (fun s => s.processor.toLower == "fertilize-clause") then
    unless clausifyInfos.isEmpty do
      throwError "replayClause: fertilize step alongside an effective \
                  clausify record at {cn.idStr} (frontier)"
    return ← replayFertilize rec cfg ctx cn st
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
