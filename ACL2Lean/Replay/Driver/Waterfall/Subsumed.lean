/-
  Driver/Waterfall/Subsumed — split from Driver/Core (WP2 Stage 3a, 2026-07-17;
  see docs/plans/2026-07-18_driver-modular-refactor.md).

  The SUBSUMED-clause processor.
-/
import ACL2Lean.Replay.Driver.Waterfall

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- Replay a POOL-SUBSUMED root: ACL2 regarded this pool clause `C` as proved
    pending the MORE GENERAL pool root `G` (its clause attached as the child's
    subtree by the builder). Recompute the subsumption witness σ (every
    Gσ-literal ∈ C — validated, fail-closed), replay `G`'s subtree at
    `env' = env[σvars ↦ σterm values]`, bridge `eval env ((∨G)σ) ≡
    eval env' (∨G)` by substN, and walk the σ-instance literals: nil peels,
    the first truthy literal is IN `C` and closes the disjunction. -/
partial def replaySubsumed (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx)
    (cn : ClauseNode) : MetaM Expr := do
  let [child] := cn.children
    | throwError "replaySubsumed: {cn.children.length} children at {cn.idStr}"
  let G := child.inputClause
  let C := cn.inputClause
  let gvars := (G.flatMap ACL2.Replay.freeVars).eraseDups
  let some σ := subsumeWitness gvars G C []
    | throwError "replaySubsumed: no subsumption witness — {cn.idStr}'s \
                  clause is not an instance-superset of {child.idStr}'s \
                  (recompute/emission divergence)"
  -- VALIDATE the witness (recompute-and-check): every σ-literal is in C
  let σvars := σ.map (·.1)
  let σterms := σ.map (·.2)
  let litsσ := G.map (ACL2.Replay.substTerm σvars σterms)
  for l in litsσ do
    unless C.contains l do
      throwError "replaySubsumed: witness literal {repr l} not in the \
                  subsumed clause at {cn.idStr}"
  let w := cfg.worldExpr
  let env := cfg.envExpr
  let mut ctx := ctx
  let mut vals : List Expr := []
  let mut convs : List Expr := []
  for t in σterms do
    ctx ← pinTermOpaques cfg env ctx t
    vals := vals ++ [← ctxValExpr cfg ctx t]
    convs := convs ++ [← ctxValProof cfg ctx t]
  let formalsE ← mkListLit (mkConst ``Symbol) (σvars.map reflectSymbol)
  let argsE ← mkListLit (mkConst ``SExpr) (σterms.map reflectSExpr)
  let valsE ← mkListLit (mkConst ``SExpr) vals
  let env' ← mkAppM ``bindArgsOver #[env, formalsE, valsE]
  let cfg' := { cfg with envExpr := env' }
  let ctx' := { ctx with varVals := [], vals := [], litFacts := [],
                         branchFacts := [], segFacts := [] }
  let pChild ← rec.clause cfg' ctx' child
  let childTerm := disjoinTerm G
  let hWellScoped ← proveByDecide
    (← mkEq (← mkAppM ``ACL2.Replay.WellScoped #[reflectSExpr childTerm])
            (mkConst ``Bool.true))
    "WellScoped subsumed general clause"
  let hlenPf ← proveByDecide
    (← mkEq (← mkAppM ``List.length #[argsE]) (← mkAppM ``List.length #[valsE]))
    "substN arg/val lengths"
  let prodTy ← mkAppM ``Prod #[mkConst ``SExpr, mkConst ``SExpr]
  let pFn ← withLocalDeclD `pr prodTy fun prV => do
    let fst ← mkAppM ``Prod.fst #[prV]
    let snd ← mkAppM ``Prod.snd #[prV]
    mkLambdaFVars #[prV] (← mkValConvPropEx w env fst snd)
  let entries ← (σterms.zip vals).mapM fun (t, v) =>
    mkAppM ``Prod.mk #[reflectSExpr t, v]
  let (_, hargsRaw) ← mkForallMemProof prodTy pFn (entries.zip convs)
  let zipE ← mkAppM ``List.zip #[argsE, valsE]
  let hargsTy ← withLocalDeclD `pr prodTy fun prV => do
    let mem ← mkAppM ``Membership.mem #[zipE, prV]
    mkForallFVars #[prV] (← mkArrow mem (mkApp pFn prV).headBeta)
  let hargs ← mkExpectedTypeHint hargsRaw hargsTy
  let pBridge ← mkAppM ``evalOpt_substTerm_substN
    #[w, env, formalsE, argsE, valsE, reflectSExpr childTerm, hWellScoped, hlenPf, hargs]
  -- EvTrue of the σ-instance disjunction at THIS env
  let pInst ← mkAppM ``evtrue_of_fuel_eq #[pBridge, pChild]
  -- walk the σ-instance literals into the subsumed clause
  let nilC := mkConst ``SExpr.nil
  let closeAt (ctxW : ReplayCtx) (l : SExpr) (hne : Expr) : MetaM Expr := do
    let some m := C.findIdx? (· == l)
      | throwError "replaySubsumed: internal — witness literal {repr l} \
                    lost from the clause"
    evtrueOfLitTrue cfg ctxW C m l hne
  let rec goW (ctxW : ReplayCtx) (pCur : Expr) : List SExpr → MetaM Expr
    | [] => throwError "replaySubsumed: empty instance walk"
    | [l] => do
      let ctxW ← pinTermOpaques cfg cfg.envExpr ctxW l
      let pL ← ctxValProof cfg ctxW l
      let hne ← mkAppM ``ne_nil_of_evtrue_conv #[pCur, pL]
      closeAt ctxW l hne
    | l :: restL => do
      let ctxW ← pinTermOpaques cfg cfg.envExpr ctxW l
      let vL ← ctxValExpr cfg ctxW l
      let pL ← ctxValProof cfg ctxW l
      let negB ← withLocalDeclD `hnil (← mkEq vL nilC) fun hNil => do
        let pNil ← mkAppM ``re_val_cast
          #[w, env, reflectSExpr l, vL, nilC, pL, hNil]
        let pRest ← mkAppM ``evtrue_extract_else #[pNil, pCur]
        mkLambdaFVars #[hNil] (← goW ctxW pRest restL)
      let posB ← withLocalDeclD `hne (← mkAppM ``Ne #[vL, nilC]) fun hNe => do
        mkLambdaFVars #[hNe] (← closeAt ctxW l hNe)
      mkAppM ``Classical.byCases #[negB, posB]
  goW ctx pInst litsσ

end ACL2.Replay.Driver
