/-
  Driver/Waterfall/Generalize — split from Driver/Core (WP2 Stage 3a, 2026-07-17;
  see docs/plans/2026-07-18_driver-modular-refactor.md).

  The GENERALIZE processor.
-/
import ACL2Lean.Replay.Driver.Waterfall

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- Replay a GENERALIZE node (`generalize-clause`): the child clause `C'`
    abstracts the emitted `:TERMS` by the fresh `:VARS` — substituting the
    terms back for the vars must recover THIS clause exactly (recompute-and-
    check; a var that was not fresh fails it). Prove `EvTrue w env (disjoin C)`
    by replaying the child at `env' = env[vars ↦ term values]` and bridging
    `eval env ((disjoin C')σ) ≡ eval env' (disjoin C')` by `substN`
    (σ = vars ↦ terms) — the elim pattern without the case split. -/
partial def replayGeneralize (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (cn : ClauseNode)
    (st : WaterfallStep) : MetaM Expr := do
  for s in cn.steps do
    unless s.processor.toLower == "generalize-clause" ||
           s.processor.toLower == "settled-down-clause" do
      throwError "replayGeneralize: processor {s.processor} alongside \
                  generalize at {cn.idStr} (frontier)"
  for (_, lp) in flattenLiterals (cn.steps.flatMap (·.items)) do
    unless lp.nodes.isEmpty && lp.result == lp.literal do
      throwError "replayGeneralize: non-identity literal item at {cn.idStr} \
                  (frontier): {repr lp.literal}"
  let some genS := st.extraFields.lookup "generalize"
    | throwError "replayGeneralize: no :GENERALIZE record at {cn.idStr}"
  let rec plistLookup (k : String) : SExpr → Option SExpr
    | .cons (.atom (.keyword kw)) (.cons v rest) =>
      if kw == k then some v else plistLookup k rest
    | .cons _ rest => plistLookup k rest
    | _ => none
  let some termsS := plistLookup "TERMS" genS
    | throwError "replayGeneralize: :GENERALIZE without :TERMS at {cn.idStr}"
  let some varsS := plistLookup "VARS" genS
    | throwError "replayGeneralize: :GENERALIZE without :VARS at {cn.idStr}"
  -- one round only (a multi-round generalize is a frontier)
  let some [roundTermsS] := termsS.toList?
    | throwError "replayGeneralize: :TERMS {repr termsS} is not a single \
                  round at {cn.idStr} (frontier)"
  let some [roundVarsS] := varsS.toList?
    | throwError "replayGeneralize: :VARS {repr varsS} is not a single \
                  round at {cn.idStr} (frontier)"
  let some terms := roundTermsS.toList?
    | throwError "replayGeneralize: round terms {repr roundTermsS} not a list"
  let some varsL := roundVarsS.toList?
    | throwError "replayGeneralize: round vars {repr roundVarsS} not a list"
  let gvars ← varsL.mapM fun v => do
    let .atom (.symbol s) := v
      | throwError "replayGeneralize: non-variable {repr v} in :VARS"
    pure s
  unless gvars.length == terms.length && !gvars.isEmpty do
    throwError "replayGeneralize: {gvars.length} vars for {terms.length} \
                terms at {cn.idStr}"
  let [child] := cn.children
    | throwError "replayGeneralize: {cn.children.length} children at \
                  {cn.idStr} (frontier)"
  -- recompute-and-check: σ-substituting the child recovers this clause
  let childTerm := disjoinTerm child.inputClause
  unless ACL2.Replay.substTerm gvars terms childTerm
      == disjoinTerm cn.inputClause do
    throwError "replayGeneralize: substituting the :TERMS back does not \
                recover the clause at {cn.idStr} (recompute/emission \
                divergence)"
  let w := cfg.worldExpr
  let env := cfg.envExpr
  -- pin the generalized terms and take their values at THIS env
  let mut ctx := ctx
  let mut vals : List Expr := []
  let mut convs : List Expr := []
  for t in terms do
    ctx ← pinTermOpaques cfg env ctx t
    vals := vals ++ [← ctxValExpr cfg ctx t]
    convs := convs ++ [← ctxValProof cfg ctx t]
  let formalsE ← mkListLit (mkConst ``Symbol) (gvars.map reflectSymbol)
  let argsE ← mkListLit (mkConst ``SExpr) (terms.map reflectSExpr)
  let valsE ← mkListLit (mkConst ``SExpr) vals
  let env' ← mkAppM ``envUpdate #[env, formalsE, valsE]
  let cfg' := { cfg with envExpr := env' }
  -- clear ALL env-bound fact channels (audit 2026-07-06: branchFacts/segFacts
  -- carry proofs about THIS env; stale ones at env\' would only kernel-fail,
  -- but must not be offered)
  let ctx' := { ctx with varVals := [], vals := [], litFacts := [],
                         branchFacts := [], segFacts := [] }
  let pChild ← rec.clause cfg' ctx' child
  -- substN bridge back to this env
  let hNoLet ← proveByDecide
    (← mkEq (← mkAppM ``ACL2.Replay.NoLet #[reflectSExpr childTerm])
            (mkConst ``Bool.true))
    "NoLet generalize child"
  let hlenPf ← proveByDecide
    (← mkEq (← mkAppM ``List.length #[argsE]) (← mkAppM ``List.length #[valsE]))
    "substN arg/val lengths"
  let prodTy ← mkAppM ``Prod #[mkConst ``SExpr, mkConst ``SExpr]
  let pFn ← withLocalDeclD `pr prodTy fun prV => do
    let fst ← mkAppM ``Prod.fst #[prV]
    let snd ← mkAppM ``Prod.snd #[prV]
    mkLambdaFVars #[prV] (← mkValConvPropEx w env fst snd)
  let entries ← (terms.zip vals).mapM fun (t, v) =>
    mkAppM ``Prod.mk #[reflectSExpr t, v]
  let (_, hargsRaw) ← mkForallMemProof prodTy pFn (entries.zip convs)
  let zipE ← mkAppM ``List.zip #[argsE, valsE]
  let hargsTy ← withLocalDeclD `pr prodTy fun prV => do
    let mem ← mkAppM ``Membership.mem #[zipE, prV]
    mkForallFVars #[prV] (← mkArrow mem (mkApp pFn prV).headBeta)
  let hargs ← mkExpectedTypeHint hargsRaw hargsTy
  let pBridge ← mkAppM ``evalOpt_substTerm_substN
    #[w, env, formalsE, argsE, valsE, reflectSExpr childTerm, hNoLet, hlenPf, hargs]
  mkAppM ``evtrue_of_fuel_eq #[pBridge, pChild]

end ACL2.Replay.Driver
