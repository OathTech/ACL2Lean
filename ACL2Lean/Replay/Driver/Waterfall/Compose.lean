/-
  Driver/Waterfall/Compose — split from Driver/Core (WP2 Stage 3a, 2026-07-17;
  see docs/plans/2026-07-18_driver-modular-refactor.md).

  The W3 branch-split composer (composeSplit).
-/
import ACL2Lean.Replay.Driver.Waterfall

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- The W3 branch-split COMPOSER: prove `EvTrue w env (disjoin (lit :: rest))`
    for a literal whose clausify SPLIT (docs/notes/2026-07-03_branch-split-
    spine.md, ratified partial logging). The byCases tree comes from the
    emitted decision trace; at each leaf the literal's collapse along the path
    facts is re-derived by `collapseEval` (fail-closed against the emitted
    leaf value), then:
    - a DROPPED leaf ('t): the literal itself is true — the disjunction closes;
    - a SEGMENT leaf: split on the literal's value (truth closes); under its
      falsity, select the unique branch whose segment literals are all
      derivably false, inject the segment facts, and recurse the branch's
      continuation — or, for an EMPTY continuation, peel the pushed sibling
      clause down to the surviving literal and bridge it back. -/
partial def composeSplit (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (idStr : String)
    (lp : LiteralProof) (chainOpt : Option Expr) (clauseLit : SExpr)
    (restLits : List (Nat × SExpr)) (branches : List (SExpr × List ClauseItem))
    (accClause : List SExpr) (children : List ClauseNode)
    (facts : List (SExpr × Expr × Bool × Expr)) (tree : TraceTree) :
    MetaM Expr := do
  let w := cfg.worldExpr
  let e := cfg.envExpr
  let nilC := mkConst ``SExpr.nil
  match tree with
  | .split T fSide tSide =>
    let ctx ← pinTermOpaques cfg e ctx T
    let vT ← ctxValExpr cfg ctx T
    let negL ← withLocalDeclD `hnil (← mkEq vT nilC) fun hNil => do
      let p ← composeSplit rec cfg ctx idStr lp chainOpt clauseLit restLits branches
        accClause children (facts ++ [(T, vT, false, hNil)]) fSide
      mkLambdaFVars #[hNil] p
    let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[vT, nilC]) fun hNe => do
      let p ← composeSplit rec cfg ctx idStr lp chainOpt clauseLit restLits branches
        accClause children (facts ++ [(T, vT, true, hNe)]) tSide
      mkLambdaFVars #[hNe] p
    mkAppM ``Classical.byCases #[negL, posL]
  | .resolved T verdict how sub =>
    -- a CONSTANT-resolved test: the test collapsed to a quoted constant under
    -- earlier splits before if-interp saw it — the verdict is ground, so
    -- re-derive it by evaluation (no assumption involved), fail-closed on any
    -- mismatch between the constant and the recorded verdict.
    if how == "constant" then
      let .cons (.atom (.symbol q)) (.cons cv .nil) := T
        | throwError "composeSplit: constant-resolved test {repr T} is not a \
                      quoted constant at {idStr} (frontier)"
      unless q.name == "QUOTE" do
        throwError "composeSplit: constant-resolved test {repr T} is not a \
                    quoted constant at {idStr} (frontier)"
      let wantSign := verdict == "true"
      unless wantSign == (cv != SExpr.nil) do
        throwError "composeSplit: constant-resolved test {repr T} has verdict \
                    {verdict}, contradicting the constant, at {idStr}"
      let ctx ← pinTermOpaques cfg e ctx T
      let vT ← ctxValExpr cfg ctx T
      let hFact ←
        if wantSign then
          proveByDecide (← mkAppM ``Ne #[vT, nilC]) "constant test non-nil"
        else
          proveByDecide (← mkEq vT nilC) "constant test nil"
      return ← composeSplit rec cfg ctx idStr lp chainOpt clauseLit restLits branches
        accClause children (facts ++ [(T, vT, wantSign, hFact)]) sub
    unless how == "assumed" do
      throwError "composeSplit: resolved test {repr T} how={how} at {idStr} \
                  (frontier — only assumption-resolved tests are re-derived)"
    let ctx ← pinTermOpaques cfg e ctx T
    let vT ← ctxValExpr cfg ctx T
    let wantSign := verdict == "true"
    -- re-derive the resolution: exact match, then commutative equal match
    -- (if-interp-assumed-value2's rule set; fail-closed beyond)
    let hFact ←
      match facts.find? (fun (T', _, _, _) => T' == T) with
      | some (_, _, sign, h) => do
        unless sign == wantSign do
          throwError "composeSplit: fact for {repr T} has sign {sign}, trace \
                      verdict {verdict} at {idStr}"
        pure h
      | none =>
        match T with
        | .cons (.atom (.symbol eqS)) (.cons x (.cons y .nil)) => do
          unless eqS.name == "EQUAL" do
            throwError "composeSplit: no fact for resolved test {repr T} at \
                        {idStr} (frontier)"
          let flipped : SExpr := .cons (.atom (.symbol eqS)) (.cons y (.cons x .nil))
          let some (_, _, sign, h) :=
              facts.find? (fun (T', _, _, _) => T' == flipped)
            | throwError "composeSplit: no fact for resolved test {repr T} \
                          (or its flip) at {idStr} (frontier)"
          unless sign == wantSign do
            throwError "composeSplit: flipped fact for {repr T} has sign \
                        {sign}, trace verdict {verdict} at {idStr}"
          -- transport across logic_equal_comm: vT = Logic.equal vx vy,
          -- fact over Logic.equal vy vx
          let vx ← ctxValExpr cfg ctx x
          let vy ← ctxValExpr cfg ctx y
          let comm ← mkAppM ``logic_equal_comm #[vx, vy]
          if wantSign then
            mkAppM ``ne_of_eq_of_ne #[comm, h]
          else
            mkAppM ``Eq.trans #[comm, h]
        | _ =>
          throwError "composeSplit: no fact for resolved test {repr T} at \
                      {idStr} (frontier)"
    composeSplit rec cfg ctx idStr lp chainOpt clauseLit restLits branches
      accClause children (facts ++ [(T, vT, wantSign, hFact)]) sub
  | .leaf value outcome emittedSeg =>
    -- re-derive the literal's collapse along the path facts
    let (collapseOpt, collapsed) ← collapseEval cfg ctx facts lp.result
    unless collapsed == value do
      throwError "composeSplit: collapse of literal {lp.index} reached \
                  {repr collapsed}, trace leaf is {repr value} at {idStr}"
    let fullChain ← match chainOpt, collapseOpt with
      | none, none => pure none
      | some c, none => pure (some c)
      | none, some c => pure (some c)
      | some c1, some c2 => pure (some (← mkAppM ``fuel_chain_eq #[c1, c2]))
    let restTerm := disjoinTerm (restLits.map (·.2))
    if outcome == "dropped" then
      -- the literal is TRUE on this path: eval lit ≡ eval 't → close
      unless value == quoteT do
        throwError "composeSplit: dropped leaf value {repr value} ≠ 't at {idStr}"
      let some ch := fullChain
        | throwError "composeSplit: dropped leaf with no chain at {idStr}"
      let pclose ← mkAppM ``fuel_conv_of_eq #[ch, ← quoteTFact cfg]
      if restLits.isEmpty then
        mkAppM ``evtrue_of_eq_t #[pclose]
      else
        let hq ← mkAppM ``re_val_quote #[w, e, reflectSExpr SExpr.t]
        let hcv ← proveByDecide
          (← mkEq (mkApp (mkConst ``Logic.toBool) (mkConst ``SExpr.t)) (mkConst ``Bool.true))
          "toBool t"
        let hIf ← mkAppM ``conv_if_true
          #[w, e, reflectSExpr clauseLit, reflectSExpr quoteT, reflectSExpr restTerm,
            mkConst ``SExpr.t, mkConst ``SExpr.t, pclose, hcv, hq]
        mkAppM ``evtrue_of_eq_t #[hIf]
    else if restLits.isEmpty then
      -- SEGMENT leaf on a SINGLETON clause: the disjunction IS the literal,
      -- and the leaf must be the RESIDUAL (an inline continuation would
      -- prove an empty disjunction). Peel the pushed sibling clause down to
      -- the surviving open-leaf literal and bridge it back — no value split.
      if outcome == "segment-false" then
        -- VACUOUS singleton path: the literal is 'nil here, and its EMITTED
        -- segment (with accClause) forms the pushed child clause — whose
        -- every literal has an in-scope falsity fact (ctx for accClause,
        -- this path's byCases facts for the segment). The child's proof
        -- then CONTRADICTS the path; the singleton goal follows ex falso
        -- (mirrors the spine walker's vacuous residual arm).
        let segL := emittedSeg.getD []
        let expected := accClause ++ segL.filter (!accClause.contains ·)
        -- the pushed child may have been SUBSUMPTION-SIMPLIFIED (Satriani):
        -- accept the UNIQUE child whose clause is an order-preserving SUBSET
        -- of the constructed residual — every used literal still needs its
        -- own falsity fact below, so the relaxation cannot compose unsoundly
        let rec isSublist : List SExpr → List SExpr → Bool
          | [], _ => true
          | _, [] => false
          | a :: as', b :: bs => if a == b then isSublist as' bs else isSublist (a :: as') bs
        let child ← do
          match children.find? (·.inputClause == expected) with
          | some c => pure c
          | none =>
            match children.filter (fun c => isSublist c.inputClause expected) with
            | [c] => pure c
            | [] => throwError "composeSplit: no child clause matches the vacuous \
                                residual {repr expected} at {idStr}"
            | cs => throwError "composeSplit: {cs.length} children are subsets of \
                                the vacuous residual {repr expected} at {idStr} \
                                (ambiguous)"
        let expected := child.inputClause
        if expected.isEmpty then
          throwError "composeSplit: vacuous residual with an EMPTY child \
                      clause at {idStr} (frontier)"
        let deriveF (ctx : ReplayCtx) (L : SExpr) : MetaM Expr := do
          if let some hf := ctx.litFactByTerm? L then return hf
          if let some (_, _, _, hf) :=
              facts.find? (fun (T, _, sign, _) => !sign && L == T) then
            return hf
          match L with
          | .cons (.atom (.symbol ns)) (.cons T .nil) =>
            if ns.name == "NOT" then
              match facts.find? (fun (T', _, sign, _) => sign && T' == T) with
              | some (_, _, _, hf) => mkAppM ``not_nil_of_truthy #[hf]
              | none => throwError "composeSplit: no falsity fact for the \
                                    vacuous-residual literal {repr L} at {idStr}"
            else throwError "composeSplit: no falsity fact for the \
                             vacuous-residual literal {repr L} at {idStr}"
          | _ => throwError "composeSplit: no falsity fact for the \
                             vacuous-residual literal {repr L} at {idStr}"
        let mut ctx := ctx
        for L in expected do
          ctx ← pinTermOpaques cfg e ctx L
        let pChild ← rec.clause cfg { ctx with litFacts := [] } child
        let mut p := pChild
        for L in expected.dropLast do
          let hf ← deriveF ctx L
          let pNil ← mkAppM ``re_val_cast
            #[w, e, reflectSExpr L, ← ctxValExpr cfg ctx L, nilC,
              ← ctxValProof cfg ctx L, hf]
          p ← mkAppM ``evtrue_extract_else #[pNil, p]
        let some lastL := expected.getLast?
          | throwError "composeSplit: internal — empty vacuous residual"
        let hfLast ← deriveF ctx lastL
        let hNe ← mkAppM ``ne_nil_of_evtrue_conv #[p, ← ctxValProof cfg ctx lastL]
        let goalTy ← mkAppM ``EvTrue #[w, e, reflectSExpr clauseLit]
        return ← mkAppOptM ``absurd #[none, some goalTy, some hfLast, some hNe]
      unless outcome == "segment-open" do
        throwError "composeSplit: {outcome} leaf on a singleton clause at \
                    {idStr} (frontier)"
      let deriveFalsity (L : SExpr) : MetaM (Option Expr) := do
        if let some (_, _, _, hf) :=
            facts.find? (fun (T, _, sign, _) => !sign && L == T) then
          return some hf
        match L with
        | .cons (.atom (.symbol ns)) (.cons T .nil) =>
          if ns.name == "NOT" then
            match facts.find? (fun (T', _, sign, _) => sign && T' == T) with
            | some (_, _, _, hf) =>
              return some (← mkAppM ``not_nil_of_truthy #[hf])
            | none => return none
          else return none
        | _ => return none
      -- selection: EXACT emitted-segment match first (the leaf→branch link
      -- ACL2's converter constructed); when no branch carries it (the
      -- Satriani/subsumption post-pass MERGED segments — complementary-
      -- literal consensus), fall back to derivable-falsity uniqueness (the
      -- merged branch is falsified by either source leaf's facts).
      let selectResidual (exact : Bool) :
          MetaM (Option (List SExpr × List Expr)) := do
        let mut selected : Option (List SExpr × List Expr) := none
        for (seg, cont) in branches do
          -- :CONTEXT-SUBST decorations are inert here (their equations live in
          -- the segment); a residual branch may still carry them
          let contCore := cont.dropWhile fun
            | .step n => (runeOf n).ty == "context-subst"
            | _ => false
          unless contCore.isEmpty do continue
          let some segL := seg.toList?
            | throwError "composeSplit: branch segment {repr seg} is not a \
                          list at {idStr}"
          if exact then
            unless emittedSeg == some segL do continue
          unless segL.getLast? == some value do continue
          let mut proofs : List Expr := []
          let mut ok := true
          for L in segL.dropLast do
            match ← deriveFalsity L with
            | some p => proofs := proofs ++ [p]
            | none => ok := false
          if ok then
            unless selected.isNone do
              throwError "composeSplit: ambiguous residual selection for the \
                          open leaf {repr value} at {idStr}"
            selected := some (segL, proofs)
        return selected
      let mut selected ← selectResidual (exact := emittedSeg.isSome)
      if selected.isNone && emittedSeg.isSome then
        selected ← selectResidual (exact := false)
      let some (segL, segProofs) := selected
        | throwError "composeSplit: no residual branch matches the open leaf \
                      {repr value} at {idStr} (frontier)"
      let expected := accClause ++ segL.filter (!accClause.contains ·)
      let some child := children.find? (·.inputClause == expected)
        | throwError "composeSplit: no child clause matches the residual \
                      {repr expected} at {idStr}"
      unless expected.getLast? == some value do
        throwError "composeSplit: residual survivor is not last at {idStr}"
      -- litFacts are INDEX-keyed and clause-scoped — the residual child is
      -- a PUSHED clause with its own numbering; stale entries collide
      let pChild ← rec.clause cfg { ctx with litFacts := [] } child
      let segFactsHere := segL.dropLast.zip segProofs
      let mut p := pChild
      for L in expected.dropLast do
        let hf ← match ctx.litFactByTerm? L,
                    (segFactsHere.find? (·.1 == L)).map (·.2) with
          | some hf, _ => pure hf
          | none, some hf => pure hf
          | none, none =>
            throwError "composeSplit: no falsity fact for the residual \
                        literal {repr L} at {idStr}"
        let pNil ← mkAppM ``re_val_cast
          #[w, e, reflectSExpr L, ← ctxValExpr cfg ctx L, nilC,
            ← ctxValProof cfg ctx L, hf]
        p ← mkAppM ``evtrue_extract_else #[pNil, p]
      -- p : EvTrue(value); bridge back to the literal
      match fullChain with
      | none => pure p
      | some ch => mkAppM ``evtrue_of_fuel_eq #[ch, p]
    else
      -- SEGMENT leaf: split on the literal's value
      let vLit ← ctxValExpr cfg ctx clauseLit
      let pLit ← ctxValProof cfg ctx clauseLit
      let hthen ← withLocalDeclD `h (← mkAppM ``Ne #[vLit, nilC]) fun h => do
        let p ← mkAppM ``evtrue_of_eq_t #[← quoteTFact cfg]
        let _ := h
        mkLambdaFVars #[h] p
      let helse ← withLocalDeclD `h (← mkEq vLit nilC) fun h => do
        -- the leaf value's falsity, bridged along the full chain
        let hLeafNil ← match fullChain with
          | none => pure h
          | some ch => do
            let pLeaf ← ctxValProof cfg ctx value
            let vEq ← mkAppM ``val_eq_of_eval_eq #[ch, pLit, pLeaf]
            mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[vEq], h]
        -- a segment literal's falsity, derivable from the path facts / the
        -- leaf fact (if-interp's convert-assumptions-to-clause-segment)
        let deriveFalsity (L : SExpr) : MetaM (Option Expr) := do
          if outcome == "segment-open" && L == value then
            return some hLeafNil
          if let some (_, _, _, hf) :=
              facts.find? (fun (T, _, sign, _) => !sign && L == T) then
            return some hf
          match L with
          | .cons (.atom (.symbol ns)) (.cons T .nil) =>
            if ns.name == "NOT" then
              match facts.find? (fun (T', _, sign, _) => sign && T' == T) with
              | some (_, _, _, hf) =>
                return some (← mkAppM ``not_nil_of_truthy #[hf])
              | none => return none
            else return none
          | _ => return none
        -- select the branch: EXACT emitted-segment match first (the
        -- leaf→branch link ACL2's converter constructed); when no branch
        -- carries it (the Satriani/subsumption post-pass MERGED segments —
        -- complementary-literal consensus), fall back to the UNIQUE branch
        -- whose segment is derivably all-false (the merged branch is
        -- falsified by either source leaf's facts).
        let selectBranch (exact : Bool) :
            MetaM (Option (List SExpr × List ClauseItem × List Expr)) := do
          let mut selected : Option (List SExpr × List ClauseItem × List Expr) := none
          for (seg, cont) in branches do
            let some segL := seg.toList?
              | throwError "composeSplit: branch segment {repr seg} is not a \
                            list at {idStr}"
            if exact then
              unless emittedSeg == some segL do continue
            let mut proofs : List Expr := []
            let mut ok := true
            for L in segL do
              match ← deriveFalsity L with
              | some p => proofs := proofs ++ [p]
              | none => ok := false
            if ok then
              if let some (prevSeg, _, _) := selected then
                throwError "composeSplit: ambiguous branch selection for the \
                            {outcome} leaf {repr value} at {idStr}: both \
                            {repr prevSeg} and {repr segL} are derivably false \
                            (facts: {repr (facts.map (fun (T, _, s, _) => (T, s)))})"
              selected := some (segL, cont, proofs)
          return selected
        let mut selected? ← selectBranch (exact := emittedSeg.isSome)
        if selected?.isNone && emittedSeg.isSome then
          selected? ← selectBranch (exact := false)
        let some (segL, cont, segProofs) := selected?
          | throwError "composeSplit: no branch matches the {outcome} leaf \
                        {repr value} at {idStr} (frontier)"
        let cont := cont.dropWhile fun
          | .step n => (runeOf n).ty == "context-subst"
          | _ => false
        let p ←
          if cont.isEmpty then do
            -- RESIDUAL: the branch's clause was pushed as a sibling subgoal
            let expected := accClause ++ segL.filter (!accClause.contains ·)
            let some child := children.find? (·.inputClause == expected)
              | throwError "composeSplit: no child clause matches the residual \
                            {repr expected} at {idStr}"
            unless outcome == "segment-open" && expected.getLast? == some value do
              throwError "composeSplit: residual branch's surviving literal is \
                          not the open leaf at {idStr} (frontier)"
            let pChild ← rec.clause cfg { ctx with litFacts := [] } child
            -- peel every literal but the survivor
            let segFactsHere := segL.zip segProofs
            let mut p := pChild
            for L in expected.dropLast do
              let hf ← match ctx.litFactByTerm? L,
                          (segFactsHere.find? (·.1 == L)).map (·.2) with
                | some hf, _ => pure hf
                | none, some hf => pure hf
                | none, none =>
                  throwError "composeSplit: no falsity fact for the residual \
                              literal {repr L} at {idStr}"
              let pNil ← mkAppM ``re_val_cast
                #[w, e, reflectSExpr L, ← ctxValExpr cfg ctx L, nilC,
                  ← ctxValProof cfg ctx L, hf]
              p ← mkAppM ``evtrue_extract_else #[pNil, p]
            -- p : EvTrue(value); bridge to the literal and refute h
            let pLitTrue ← match fullChain with
              | none => pure p
              | some ch => mkAppM ``evtrue_of_fuel_eq #[ch, p]
            let hNe ← mkAppM ``ne_nil_of_evtrue_conv #[pLitTrue, pLit]
            let goalTy ← mkAppM ``EvTrue #[w, e, reflectSExpr restTerm]
            mkAppOptM ``absurd #[none, some goalTy, some h, some hNe]
          else do
            -- inline continuation: inject the segment facts and recurse;
            -- leading context-subst steps are the :CONTEXT-SUBST decorations
            -- (their equations are consumed by solidify .segment nodes)
            let cont' := cont.dropWhile fun
              | .step n => (runeOf n).ty == "context-subst"
              | _ => false
            -- the literal's own falsity — at its RECORDED rewritten form
            -- (what the tree linker matched `.literal`-sourced solidify
            -- nodes against), bridged along the literal chain — joins
            -- litFacts under its index, exactly as on the non-split path
            let hResultNil ← match chainOpt with
              | none => pure h
              | some ch => do
                let pLit' ← ctxValProof cfg ctx lp.result
                let vEq ← mkAppM ``val_eq_of_eval_eq #[ch, pLit, pLit']
                mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[vEq], h]
            let ctx' := { ctx with
              litFacts := ctx.litFacts ++ [(lp.index, lp.result, hResultNil)],
              segFacts := ctx.segFacts ++ segL.zip segProofs }
            let accClause' := accClause ++ segL.filter (!accClause.contains ·)
            rec.clauseSpine cfg ctx' idStr restLits cont' accClause' children
        mkLambdaFVars #[h] p
      mkAppM ``evtrue_dp_if_split
        #[w, e, reflectSExpr clauseLit, reflectSExpr quoteT, reflectSExpr restTerm,
          vLit, pLit, hthen, helse]

end ACL2.Replay.Driver
