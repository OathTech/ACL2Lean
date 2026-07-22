/-
  Driver/Waterfall/Elim — split from Driver/Core (WP2 Stage 3a, 2026-07-17;
  see docs/plans/2026-07-18_driver-modular-refactor.md).

  The destructor-ELIMINATION processor (car-cdr-elim). Generalized to
  MULTI-RECORD rounds (emission arc 2026-07-21): a round's records nest as
  guard splits — record k cases on `(consp v_k)`; record 1's guard is the
  clause's own `(not (consp v))` head literal (nil-case closes the
  disjunction), while each LATER record's nil-case consumes its own GUARD
  CHILD (`(consp v_k) :: C_{k-1}` — the clause ACL2 pushes for the
  not-a-cons case, peeled via `evtrue_extract_else`); the success side
  extends the env and recurses, bottoming out at the fully-eliminated
  child with one `evalOpt_substTerm_substN` bridge per level.
-/
import ACL2Lean.Replay.Driver.Waterfall

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- Parse + validate one CAR-CDR-ELIM record
    `((:ELIM CAR-CDR-ELIM) v (CONS v1 v2) (((CAR v) . v1) ((CDR v) . v2))
      NIL NIL NIL)` → `(v, v1, v2)`. -/
private def parseElimRecord (idStr : String) (recS : SExpr) :
    MetaM (Symbol × Symbol × Symbol) := do
  let some [runeS, varS, targetS, destS, crit1, crit2, crit3] := recS.toList?
    | throwError "replayElim: elim record shape at {idStr}: {repr recS}"
  unless crit1 == .nil && crit2 == .nil && crit3 == .nil do
    throwError "replayElim: elim record carries non-nil trailing fields at \
                {idStr} (frontier): {repr recS}"
  let some [.atom (.keyword "ELIM"), .atom (.symbol runeName)] := runeS.toList?
    | throwError "replayElim: elim record rune {repr runeS} at {idStr}"
  unless runeName.name == "CAR-CDR-ELIM" do
    throwError "replayElim: elim rule {runeName.name} ≠ car-cdr-elim at \
                {idStr} (frontier)"
  let .atom (.symbol v) := varS
    | throwError "replayElim: eliminated var {repr varS} at {idStr}"
  let .cons (.atom (.symbol consS))
      (.cons (.atom (.symbol v1)) (.cons (.atom (.symbol v2)) .nil)) := targetS
    | throwError "replayElim: elim target {repr targetS} is not (cons v1 v2) \
                  at {idStr}"
  unless consS.name == "CONS" && v1 != v2 && v1 != v && v2 != v do
    throwError "replayElim: elim target vars ({consS.name} {v1.name} {v2.name}) \
                at {idStr}"
  let vT : SExpr := .atom (.symbol v)
  let carT : SExpr := .cons (.atom (.symbol { name := "CAR" })) (.cons vT .nil)
  let cdrT : SExpr := .cons (.atom (.symbol { name := "CDR" })) (.cons vT .nil)
  let expectedDest : List SExpr :=
    [.cons carT (.atom (.symbol v1)), .cons cdrT (.atom (.symbol v2))]
  unless destS.toList? == some expectedDest do
    throwError "replayElim: destructor map {repr destS} ≠ ((car {v.name}) . \
                {v1.name}) ((cdr {v.name}) . {v2.name}) at {idStr}"
  return (v, v1, v2)

/-- Replay a DESTRUCTOR-ELIMINATION node (`eliminate-destructors-clause`,
    rune `car-cdr-elim`, one round of ≥1 records — see the module doc):
    prove `EvTrue w env (disjoin C)` from the children, the emitted
    `:ELIMSEQUENCE` recomputed and REQUIRED to match at every level, never
    inferred. Per record, by cases on the value of `(consp v)`:
    - nil: record 1 closes via the clause's `(not (consp v))` head literal
      (required — frontier otherwise); a later record peels its GUARD child;
    - non-nil: recurse/replay at `env' = env[v1 ↦ car vv, v2 ↦ cdr vv]`;
      `evalOpt_substTerm_substN` bridges `eval env' (disjoin C')` to
      `eval env ((disjoin C')σ)` for `σ = v1↦(car v), v2↦(cdr v)`; the
      residual gap `disjoin C` vs `(disjoin C')σ` is exactly bare-`v` vs
      `(cons (car v) (cdr v))`, collapsed by `diffCollapse` under
      `logic_cons_car_cdr_of_consp`. -/
partial def replayElim (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (cn : ClauseNode)
    (st : WaterfallStep) : MetaM Expr := do
  -- companions must be inert; literal items are identity displays only
  for s in cn.steps do
    unless s.processor.toLower == "eliminate-destructors-clause" ||
           s.processor.toLower == "settled-down-clause" do
      throwError "replayElim: processor {s.processor} alongside elim at \
                  {cn.idStr} (frontier)"
  for (_, lp) in flattenLiterals (cn.steps.flatMap (·.items)) do
    unless lp.nodes.isEmpty && lp.result == lp.literal do
      throwError "replayElim: non-identity literal item at {cn.idStr} \
                  (frontier): {repr lp.literal}"
  -- the emitted justification: ONE round of ≥1 car-cdr-elim records
  let some seqS := st.extraFields.lookup "elimsequence"
    | throwError "replayElim: no :ELIMSEQUENCE at {cn.idStr}"
  let some [roundS] := seqS.toList?
    | throwError "replayElim: :ELIMSEQUENCE is not a single round at {cn.idStr} \
                  (frontier): {repr seqS}"
  let some recSs := roundS.toList?
    | throwError "replayElim: elim round {repr roundS} is not a list at {cn.idStr}"
  if recSs.isEmpty then
    throwError "replayElim: EMPTY elim round at {cn.idStr}"
  let records ← recSs.mapM (parseElimRecord cn.idStr)
  -- :ELIMVARS — one flat list of the round's fresh vars, in record order
  let some varsS := st.extraFields.lookup "elimvars"
    | throwError "replayElim: no :ELIMVARS at {cn.idStr}"
  let expectedVars : SExpr := .cons
    ((records.flatMap fun (_, v1, v2) =>
        [SExpr.atom (.symbol v1), SExpr.atom (.symbol v2)]).foldr .cons .nil)
    .nil
  unless varsS == expectedVars do
    throwError "replayElim: :ELIMVARS {repr varsS} does not match the \
                records' fresh vars at {cn.idStr}"
  -- children: the fully-eliminated clause + one guard clause per record ≥ 2
  unless cn.children.length == records.length do
    throwError "replayElim: {cn.children.length} children for \
                {records.length} elim record(s) at {cn.idStr} (frontier)"
  unless st.newClauses.length == records.length do
    throwError "replayElim: {st.newClauses.length} output clauses for \
                {records.length} elim record(s) at {cn.idStr} (frontier)"
  -- the clause's head literal must be (not (consp v₁)) — record 1's guard
  let (v0, _, _) := records.head!
  let lit1 : SExpr := .cons (.atom (.symbol { name := "NOT" }))
    (.cons (.cons (.atom (.symbol { name := "CONSP" }))
      (.cons (.atom (.symbol v0)) .nil)) .nil)
  let some lit1Idx := cn.inputClause.idxOf? lit1
    | throwError "replayElim: the clause has no (not (consp {v0.name})) \
                  literal at {cn.idStr} (frontier)"
  if cn.inputClause.length < 2 then
    throwError "replayElim: singleton clause at {cn.idStr} (frontier)"
  -- round-trip: recompute EVERY output clause (each later record's guard
  -- clause + the fully-eliminated clause) and REQUIRE the emitted set
  let mut computed : List (List SExpr) := []
  let mut curC := cn.inputClause
  let mut firstRec := true
  for (v, v1, v2) in records do
    let vT : SExpr := .atom (.symbol v)
    let carT : SExpr := .cons (.atom (.symbol { name := "CAR" })) (.cons vT .nil)
    let cdrT : SExpr := .cons (.atom (.symbol { name := "CDR" })) (.cons vT .nil)
    let uT : SExpr := .cons (.atom (.symbol { name := "CONS" }))
      (.cons (.atom (.symbol v1)) (.cons (.atom (.symbol v2)) .nil))
    unless firstRec do
      computed := computed ++
        [(SExpr.cons (.atom (.symbol { name := "CONSP" })) (.cons vT .nil)) :: curC]
    -- applying a record MOVES the eliminated var's (not (consp v)) literal
    -- to the FRONT (σ-image) — erase it (first occurrence; absent for a
    -- later record's fresh var), prepend its σ-image, σ the rest
    let litV : SExpr := .cons (.atom (.symbol { name := "NOT" }))
      (.cons (.cons (.atom (.symbol { name := "CONSP" })) (.cons vT .nil)) .nil)
    let curRest := match curC.idxOf? litV with
      | some i => curC.eraseIdx i
      | none => curC
    curC := elimReplace carT cdrT vT uT v1 v2 litV ::
      curRest.map (elimReplace carT cdrT vT uT v1 v2)
    firstRec := false
  computed := computed ++ [curC]
  for c in computed do
    unless st.newClauses.any (·.toList? == some c) do
      throwError "replayElim: recomputed clause {repr c} is not among the \
                  emitted :NEWCLAUSES at {cn.idStr} (record/output divergence)"
  -- the per-level recursion
  let rec go (recs : List (Symbol × Symbol × Symbol)) (curClause : List SExpr)
      (cfgK : ReplayConfig) (isTop : Bool) : MetaM Expr := do
    let ctxK0 : ReplayCtx := if isTop then ctx
      else { ctx with varVals := [], vals := [], litFacts := [] }
    -- pin the level's clause opaques AGAINST THIS LEVEL'S ENV (a deeper
    -- level's fresh env has none of the outer pins)
    let ctxK ← pinTermOpaques cfg cfgK.envExpr ctxK0 (disjoinTerm curClause)
    match recs with
    | [] =>
      let some child := cn.children.find? (·.inputClause == curClause)
        | throwError "replayElim: no child matches the fully-eliminated \
                      clause {repr curClause} at {cn.idStr}"
      rec.clause cfgK { ctxK with varVals := [], vals := [], litFacts := [] } child
    | (v, v1, v2) :: rest =>
      let vT : SExpr := .atom (.symbol v)
      let carT : SExpr := .cons (.atom (.symbol { name := "CAR" })) (.cons vT .nil)
      let cdrT : SExpr := .cons (.atom (.symbol { name := "CDR" })) (.cons vT .nil)
      let uT : SExpr := .cons (.atom (.symbol { name := "CONS" }))
        (.cons (.atom (.symbol v1)) (.cons (.atom (.symbol v2)) .nil))
      let notConspLit : SExpr := .cons (.atom (.symbol { name := "NOT" }))
        (.cons (.cons (.atom (.symbol { name := "CONSP" })) (.cons vT .nil)) .nil)
      -- the SUCCESS side's clause: erase the (not (consp v)) literal (first
      -- occurrence; absent for a later record's fresh var), REORDER it to
      -- the front, σ everything — mirroring ACL2's own clause construction
      let litIdx? := curClause.idxOf? notConspLit
      let restClause := match litIdx? with
        | some i => curClause.eraseIdx i
        | none => curClause
      let effClause := notConspLit :: restClause
      let nextClause := effClause.map (elimReplace carT cdrT vT uT v1 v2)
      let w := cfg.worldExpr
      let env := cfgK.envExpr
      let vE ← ctxValExpr cfgK ctxK vT
      let pV ← ctxValProof cfgK ctxK vT
      let conspVE := mkApp (mkConst ``Logic.consp) vE
      let nilC := mkConst ``SExpr.nil
      let conspLit : SExpr := .cons (.atom (.symbol { name := "CONSP" }))
        (.cons vT .nil)
      -- CASE (consp v) = nil
      let negL ← withLocalDeclD `hnil (← mkEq conspVE nilC) fun hNil => do
        let p ←
          if isTop then do
            -- the clause's own (not (consp v)) literal is true and closes
            -- the disjunction (at its actual position — need not be first)
            let notLit : SExpr := .cons (.atom (.symbol { name := "NOT" }))
              (.cons conspLit .nil)
            let hT ← mkAppM ``logic_not_t_of_nil #[hNil]
            let tNeNil ← proveByDecide
              (← mkAppM ``Ne #[mkConst ``SExpr.t, mkConst ``SExpr.nil]) "t ≠ nil"
            let hTrue ← mkAppM ``ne_of_eq_of_ne #[hT, tNeNil]
            evtrueOfLitTrue cfg ctxK curClause lit1Idx notLit hTrue
          else do
            -- a LATER record: the not-a-cons case is a pushed GUARD child
            -- `(consp v) :: curClause` — peel its false head literal
            let gClause := conspLit :: curClause
            let some gChild := cn.children.find? (·.inputClause == gClause)
              | throwError "replayElim: no guard child matches \
                            {repr gClause} at {cn.idStr}"
            let pG ← rec.clause cfgK
              { ctxK with varVals := [], vals := [], litFacts := [] } gChild
            let pNil ← mkAppM ``re_val_cast
              #[w, env, reflectSExpr conspLit, conspVE, nilC,
                ← ctxValProof cfgK ctxK conspLit, hNil]
            mkAppM ``evtrue_extract_else #[pNil, pG]
        mkLambdaFVars #[hNil] p
      -- CASE (consp v) ≠ nil: recurse at the elim env and bridge back
      let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[conspVE, nilC]) fun hNe => do
        let carV := mkApp (mkConst ``Logic.car) vE
        let cdrV := mkApp (mkConst ``Logic.cdr) vE
        let formalsE ← mkListLit (mkConst ``Symbol) [reflectSymbol v1, reflectSymbol v2]
        let valsE ← mkListLit (mkConst ``SExpr) [carV, cdrV]
        let env' ← mkAppM ``envUpdate #[env, formalsE, valsE]
        let cfg' := { cfgK with envExpr := env' }
        let pInner ← go rest nextClause cfg' false
        -- substN bridge: eval env ((disjoin C')σ) ≡ eval env' (disjoin C')
        let bodyT := disjoinTerm nextClause
        let argsS : List SExpr := [carT, cdrT]
        let argsE ← mkListLit (mkConst ``SExpr) (argsS.map reflectSExpr)
        let hNoLet ← proveByDecide
          (← mkEq (← mkAppM ``ACL2.Replay.NoLet #[reflectSExpr bodyT])
                  (mkConst ``Bool.true)) "NoLet elim child"
        let hlenPf ← proveByDecide
          (← mkEq (← mkAppM ``List.length #[argsE]) (← mkAppM ``List.length #[valsE]))
          "substN arg/val lengths"
        let pCar ← ctxValProof cfgK ctxK carT
        let pCdr ← ctxValProof cfgK ctxK cdrT
        let prodTy ← mkAppM ``Prod #[mkConst ``SExpr, mkConst ``SExpr]
        let pFn ← withLocalDeclD `pr prodTy fun prV => do
          let fst ← mkAppM ``Prod.fst #[prV]
          let snd ← mkAppM ``Prod.snd #[prV]
          mkLambdaFVars #[prV] (← mkValConvPropEx w env fst snd)
        let entries ← (argsS.zip [carV, cdrV]).mapM fun (a, av) =>
          mkAppM ``Prod.mk #[reflectSExpr a, av]
        let (_, hargsRaw) ← mkForallMemProof prodTy pFn (entries.zip [pCar, pCdr])
        let zipE ← mkAppM ``List.zip #[argsE, valsE]
        let hargsTy ← withLocalDeclD `pr prodTy fun prV => do
          let mem ← mkAppM ``Membership.mem #[zipE, prV]
          mkForallFVars #[prV] (← mkArrow mem (mkApp pFn prV).headBeta)
        let hargs ← mkExpectedTypeHint hargsRaw hargsTy
        let pBridge ← mkAppM ``evalOpt_substTerm_substN
          #[w, env, formalsE, argsE, valsE, reflectSExpr bodyT, hNoLet, hlenPf, hargs]
        -- diff-collapse: eval env (disjoin C) ≡ eval env ((disjoin C')σ)
        let sTermS := ACL2.Replay.substTerm [v1, v2] argsS bodyT
        let uSig : SExpr := .cons (.atom (.symbol { name := "CONS" }))
          (.cons carT (.cons cdrT .nil))
        let hVeq ← mkAppM ``Eq.symm #[← mkAppM ``logic_cons_car_cdr_of_consp #[hNe]]
        let pU ← ctxValProof cfgK ctxK uSig
        let nodeEq ← mkAppM ``fuel_eq_of_conv #[pV, pU, hVeq]
        let chainOpt ← diffCollapse w env vT uSig nodeEq
          (disjoinTerm effClause) sTermS
        let pAll ← chainAfter chainOpt pBridge
        let pEff ← mkAppM ``evtrue_of_fuel_eq #[pAll, pInner]
        -- pEff : EvTrue(disjoin (litV :: restClause)) at env. litV is FALSE
        -- under hne — peel it off the front (fuel-eq of the head frame,
        -- transported by fuel_eq_symm), then — when litV sat at position i
        -- of curClause — re-insert by the SAME frame collapse at i, lifted
        -- through the preceding frames.
        let hNotNil ← mkAppM ``not_nil_of_truthy #[hNe]
        let pLitNil ← mkAppM ``re_val_cast
          #[w, env, reflectSExpr notConspLit,
            mkApp (mkConst ``Logic.not) conspVE, nilC,
            ← ctxValProof cfgK ctxK notConspLit, hNotNil]
        let restTerm := disjoinTerm restClause
        let vRest ← ctxValExpr cfgK ctxK restTerm
        let hRest ← ctxValProof cfgK ctxK restTerm
        let _ := vRest
        let chainHead ← mkAppM ``re_if_false
          #[w, env, reflectSExpr notConspLit, reflectSExpr quoteT,
            reflectSExpr restTerm, vRest, pLitNil, hRest]
        let pRest ← mkAppM ``evtrue_of_fuel_eq
          #[← mkAppM ``fuel_eq_symm #[chainHead], pEff]
        let p ← match litIdx? with
          | none => pure pRest
          | some i => do
            -- eval(disjoin curClause) ≡ eval(disjoin restClause): the litV
            -- frame collapse at position i, lifted through i else-descents
            let mut inner ← mkAppM ``re_if_false
              #[w, env, reflectSExpr notConspLit, reflectSExpr quoteT,
                reflectSExpr (disjoinTerm (curClause.drop (i + 1))), 
                ← ctxValExpr cfgK ctxK (disjoinTerm (curClause.drop (i + 1))),
                pLitNil, ← ctxValProof cfgK ctxK (disjoinTerm (curClause.drop (i + 1)))]
            let mut curL : SExpr := .cons (.atom (.symbol { name := "IF" }))
              (.cons notConspLit (.cons quoteT
                (.cons (disjoinTerm (curClause.drop (i + 1))) .nil)))
            let mut curR : SExpr := disjoinTerm (curClause.drop (i + 1))
            for l in (curClause.take i).reverse do
              let stp : PathStep := { fn := { name := "IF" }, arity := 3,
                                      argIdx := 2, siblings := [l, quoteT] }
              inner ← applyStep w env stp curL curR inner
              curL := rebuild stp.fn stp.arity stp.argIdx curL stp.siblings
              curR := rebuild stp.fn stp.arity stp.argIdx curR stp.siblings
            unless curL == disjoinTerm curClause &&
                   curR == disjoinTerm restClause do
              throwError "replayElim: reorder lift reconstructed \
                          {repr curL} / {repr curR} at {cn.idStr}"
            mkAppM ``evtrue_of_fuel_eq #[inner, pRest]
        mkLambdaFVars #[hNe] p
      mkAppM ``Classical.byCases #[negL, posL]
  go records cn.inputClause cfg true

end ACL2.Replay.Driver
