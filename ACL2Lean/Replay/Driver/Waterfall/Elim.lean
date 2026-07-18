/-
  Driver/Waterfall/Elim — split from Driver/Core (WP2 Stage 3a, 2026-07-17;
  see docs/plans/2026-07-18_driver-modular-refactor.md).

  The destructor-ELIMINATION processor (car-cdr-elim).
-/
import ACL2Lean.Replay.Driver.Waterfall

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- Replay a DESTRUCTOR-ELIMINATION node (`eliminate-destructors-clause`, rune
    `car-cdr-elim`, single elim record): prove `EvTrue w env (disjoin C)` from
    the child clause `C' = C[(car v)↦v1, (cdr v)↦v2, v↦(cons v1 v2)]` — the
    emitted `:ELIMSEQUENCE`, recomputed and REQUIRED to match, never inferred —
    by cases on the value of `(consp v)`:
    - nil: the clause's `(not (consp v))` literal (required to be literal 1 —
      frontier otherwise) is true and closes the disjunction;
    - non-nil: replay the child at `env' = env[v1 ↦ car vv, v2 ↦ cdr vv]`;
      `evalOpt_substTerm_substN` bridges `eval env' (disjoin C')` to
      `eval env ((disjoin C')σ)` for `σ = v1↦(car v), v2↦(cdr v)`; the residual
      syntactic gap `disjoin C` vs `(disjoin C')σ` is exactly bare-`v`
      occurrences vs `(cons (car v) (cdr v))`, collapsed occurrence-by-occurrence
      by `diffCollapse` under `logic_cons_car_cdr_of_consp` (the elim rule at
      the value level). -/
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
  -- the emitted justification: exactly one round of one car-cdr-elim record
  let some seqS := st.extraFields.lookup "elimsequence"
    | throwError "replayElim: no :ELIMSEQUENCE at {cn.idStr}"
  let some [roundS] := seqS.toList?
    | throwError "replayElim: :ELIMSEQUENCE is not a single round at {cn.idStr} \
                  (frontier): {repr seqS}"
  let some [recS] := roundS.toList?
    | throwError "replayElim: elim round is not a single record at {cn.idStr} \
                  (frontier): {repr roundS}"
  let some [runeS, varS, targetS, destS, crit1, crit2, crit3] := recS.toList?
    | throwError "replayElim: elim record shape at {cn.idStr}: {repr recS}"
  unless crit1 == .nil && crit2 == .nil && crit3 == .nil do
    throwError "replayElim: elim record carries non-nil trailing fields at \
                {cn.idStr} (frontier): {repr recS}"
  let some [.atom (.keyword "ELIM"), .atom (.symbol runeName)] := runeS.toList?
    | throwError "replayElim: elim record rune {repr runeS} at {cn.idStr}"
  unless runeName.name == "CAR-CDR-ELIM" do
    throwError "replayElim: elim rule {runeName.name} ≠ car-cdr-elim at \
                {cn.idStr} (frontier)"
  let .atom (.symbol v) := varS
    | throwError "replayElim: eliminated var {repr varS} at {cn.idStr}"
  let .cons (.atom (.symbol consS))
      (.cons (.atom (.symbol v1)) (.cons (.atom (.symbol v2)) .nil)) := targetS
    | throwError "replayElim: elim target {repr targetS} is not (cons v1 v2) \
                  at {cn.idStr}"
  unless consS.name == "CONS" && v1 != v2 && v1 != v && v2 != v do
    throwError "replayElim: elim target vars ({consS.name} {v1.name} {v2.name}) \
                at {cn.idStr}"
  let vT : SExpr := .atom (.symbol v)
  let carT : SExpr := .cons (.atom (.symbol { name := "CAR" })) (.cons vT .nil)
  let cdrT : SExpr := .cons (.atom (.symbol { name := "CDR" })) (.cons vT .nil)
  let uT : SExpr := .cons (.atom (.symbol { name := "CONS" }))
    (.cons (.atom (.symbol v1)) (.cons (.atom (.symbol v2)) .nil))
  let expectedDest : List SExpr :=
    [.cons carT (.atom (.symbol v1)), .cons cdrT (.atom (.symbol v2))]
  unless destS.toList? == some expectedDest do
    throwError "replayElim: destructor map {repr destS} ≠ ((car {v.name}) . \
                {v1.name}) ((cdr {v.name}) . {v2.name}) at {cn.idStr}"
  let some varsS := st.extraFields.lookup "elimvars"
    | throwError "replayElim: no :ELIMVARS at {cn.idStr}"
  let expectedVars : SExpr :=
    .cons (.cons (.atom (.symbol v1)) (.cons (.atom (.symbol v2)) .nil)) .nil
  unless varsS == expectedVars do
    throwError "replayElim: :ELIMVARS {repr varsS} ≠ (({v1.name} {v2.name})) \
                at {cn.idStr}"
  -- structure: one output clause, one child, and they match
  let [outClause] := st.newClauses
    | throwError "replayElim: {st.newClauses.length} output clauses at \
                  {cn.idStr} (frontier)"
  let some outLits := outClause.toList?
    | throwError "replayElim: output clause {repr outClause} is not a list"
  let [child] := cn.children
    | throwError "replayElim: {cn.children.length} children at {cn.idStr} (frontier)"
  unless child.inputClause == outLits do
    throwError "replayElim: child clause ≠ elim output clause at {cn.idStr}"
  -- recompute the elim substitution on the input clause and REQUIRE the
  -- emitted output (round-trip validation of the record)
  unless cn.inputClause.map (elimReplace carT cdrT vT uT v1 v2) == outLits do
    throwError "replayElim: recomputed elim clause ≠ emitted output at \
                {cn.idStr} (record/output divergence)"
  -- the clause's head literal must be (not (consp v)) — the elim split's guard
  let lit1 : SExpr := .cons (.atom (.symbol { name := "NOT" }))
    (.cons (.cons (.atom (.symbol { name := "CONSP" })) (.cons vT .nil)) .nil)
  let c0 :: cRest := cn.inputClause
    | throwError "replayElim: empty input clause at {cn.idStr}"
  unless c0 == lit1 do
    throwError "replayElim: clause head {repr c0} is not (not (consp {v.name})) \
                at {cn.idStr} (frontier — elim literal not first)"
  if cRest.isEmpty then
    throwError "replayElim: singleton clause at {cn.idStr} (frontier)"
  let w := cfg.worldExpr
  let env := cfg.envExpr
  let vE ← ctxValExpr cfg ctx vT
  let pV ← ctxValProof cfg ctx vT
  let conspVE := mkApp (mkConst ``Logic.consp) vE
  let nilC := mkConst ``SExpr.nil
  -- CASE (consp v) = nil: literal 1 is true and closes the disjunction
  let negL ← withLocalDeclD `hnil (← mkEq conspVE nilC) fun hNil => do
    let pLit1 ← ctxValProof cfg ctx lit1
    let hT ← mkAppM ``logic_not_t_of_nil #[hNil]
    let pLit1T ← mkAppM ``re_val_cast
      #[w, env, reflectSExpr lit1, mkApp (mkConst ``Logic.not) conspVE,
        mkConst ``SExpr.t, pLit1, hT]
    let hToBool ← proveByDecide
      (← mkEq (mkApp (mkConst ``Logic.toBool) (mkConst ``SExpr.t)) (mkConst ``Bool.true))
      "toBool t"
    let hQt ← quoteTFact cfg
    let hIf ← mkAppM ``conv_if_true
      #[w, env, reflectSExpr lit1, reflectSExpr quoteT,
        reflectSExpr (disjoinTerm cRest), mkConst ``SExpr.t, mkConst ``SExpr.t,
        pLit1T, hToBool, hQt]
    let p ← mkAppM ``evtrue_of_eq_t #[hIf]
    mkLambdaFVars #[hNil] p
  -- CASE (consp v) ≠ nil: replay the child at the elim env and bridge back
  let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[conspVE, nilC]) fun hNe => do
    let carV := mkApp (mkConst ``Logic.car) vE
    let cdrV := mkApp (mkConst ``Logic.cdr) vE
    let formalsE ← mkListLit (mkConst ``Symbol) [reflectSymbol v1, reflectSymbol v2]
    let valsE ← mkListLit (mkConst ``SExpr) [carV, cdrV]
    let env' ← mkAppM ``envUpdate #[env, formalsE, valsE]
    let cfg' := { cfg with envExpr := env' }
    let ctx' := { ctx with varVals := [], vals := [], litFacts := [] }
    let pChild ← rec.clause cfg' ctx' child
    -- substN bridge: eval env ((disjoin C')σ) ≡ eval env' (disjoin C')
    let bodyT := disjoinTerm child.inputClause
    let argsS : List SExpr := [carT, cdrT]
    let argsE ← mkListLit (mkConst ``SExpr) (argsS.map reflectSExpr)
    let hNoLet ← proveByDecide
      (← mkEq (← mkAppM ``ACL2.Replay.NoLet #[reflectSExpr bodyT]) (mkConst ``Bool.true))
      "NoLet elim child"
    let hlenPf ← proveByDecide
      (← mkEq (← mkAppM ``List.length #[argsE]) (← mkAppM ``List.length #[valsE]))
      "substN arg/val lengths"
    let pCar ← ctxValProof cfg ctx carT
    let pCdr ← ctxValProof cfg ctx cdrT
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
    -- diff-collapse: eval env (disjoin C) ≡ eval env ((disjoin C')σ) — the
    -- residual diffs are bare `v` vs the σ-IMAGE of the elim target,
    -- `(cons (car v) (cdr v))`
    let sTermS := ACL2.Replay.substTerm [v1, v2] argsS bodyT
    let uSig : SExpr := .cons (.atom (.symbol { name := "CONS" }))
      (.cons carT (.cons cdrT .nil))
    let hVeq ← mkAppM ``Eq.symm #[← mkAppM ``logic_cons_car_cdr_of_consp #[hNe]]
    let pU ← ctxValProof cfg ctx uSig
    let nodeEq ← mkAppM ``fuel_eq_of_conv #[pV, pU, hVeq]
    let chainOpt ← diffCollapse w env vT uSig nodeEq (disjoinTerm cn.inputClause) sTermS
    let pAll ← match chainOpt with
      | none => pure pBridge
      | some c => mkAppM ``fuel_chain_eq #[c, pBridge]
    let p ← mkAppM ``evtrue_of_fuel_eq #[pAll, pChild]
    mkLambdaFVars #[hNe] p
  mkAppM ``Classical.byCases #[negL, posL]

end ACL2.Replay.Driver
