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
    unless identityLiteralItem lp do
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
  -- recompute-and-check, WITH generalize TYPE RESTRICTIONS: ACL2's
  -- generalize-clause PREPENDS per-var type-restriction literals derived
  -- from the generalized terms' type prescriptions (the step's cited
  -- tp runes — msort *1/3'5': (NOT (TRUE-LISTP ES))). The child clause is
  -- `restr ++ core` where σ-substituting `core` recovers THIS clause
  -- literal-wise; `restr` may be empty (the pre-existing exact case).
  let k := child.inputClause.length - cn.inputClause.length
  let restr := child.inputClause.take k
  let core := child.inputClause.drop k
  unless core.map (ACL2.Replay.substTerm gvars terms) == cn.inputClause do
    throwError "replayGeneralize: substituting the :TERMS back does not \
                recover the clause at {cn.idStr} (recompute/emission \
                divergence)"
  -- each restriction literal must be `(NOT (pred ESi))` for a generalize
  -- var ESi — anything else is a frontier
  let restrInfo ← restr.mapM fun lit => do
    let .cons (.atom (.symbol nt))
        (.cons (.cons (.atom (.symbol p)) (.cons (.atom (.symbol v)) .nil))
          .nil) := lit
      | throwError "replayGeneralize: unsupported type-restriction literal \
                    {repr lit} at {cn.idStr} (frontier: (NOT (pred var)))"
    unless nt.name == "NOT" do
      throwError "replayGeneralize: unsupported type-restriction literal \
                  {repr lit} at {cn.idStr} (frontier: (NOT (pred var)))"
    let some j := (gvars.zipIdx.find? (fun (g, _) => g == v)).map (·.2)
      | throwError "replayGeneralize: restriction var {v.name} is not a \
                    generalize :VARS entry at {cn.idStr}"
    pure (p, v, j, lit)
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
  let env' ← mkAppM ``bindArgsOver #[env, formalsE, valsE]
  let cfg' := { cfg with envExpr := env' }
  -- clear ALL env-bound fact channels (audit 2026-07-06: branchFacts/segFacts
  -- carry proofs about THIS env; stale ones at env\' would only kernel-fail,
  -- but must not be offered)
  let ctx' := { ctx with varVals := [], vals := [], litFacts := [], dedupDrops := [],
                         branchFacts := [], segFacts := [] }
  let pChild ← rec.clause cfg' ctx' child
  -- DROP the restriction heads: each `(NOT (pred ESi))` is FALSE at env'
  -- because the generalized term satisfies its type prescription — the
  -- EMITTED tp hypothesis for the term's head fn, instantiated at THIS
  -- env with the term's pinned value/convergence (consumed, not inferred),
  -- gives `⟦pred⟧ val_i = t`; `not` of that is nil, and the leading
  -- disjunct falls away (`evtrue_tail_of_if_head_nil`).
  let mut pChild := pChild
  for (p, _, j, lit) in restrInfo do
    let termJ := terms[j]!
    let valJ := vals[j]!
    let convJ := convs[j]!
    let .cons (.atom (.symbol fnJ)) argsSpineJ := termJ
      | throwError "replayGeneralize: generalized term {repr termJ} is not \
                    an application (restriction source, frontier)"
    let some (_, cor, tpHyp) := ctx.tpHyps.find? (fun (nm, _, _) => nm == fnJ.name)
      | throwError "replayGeneralize: no :TYPE-PRESCRIPTION hypothesis for \
                    {fnJ.name} justifying restriction {repr lit} (emit \
                    more, frontier)"
    let some (fnFormals, _) := cfg.worldVal.defs.get? fnJ
      | throwError "replayGeneralize: restriction fn {fnJ.name} not in the \
                    world at {cn.idStr}"
    -- the corollary must be exactly (pred (fn formals…)) — the shape whose
    -- lift is `⟦pred⟧ v = t`
    let appPat : SExpr := .cons (.atom (.symbol fnJ))
      ((fnFormals.map (SExpr.atom ∘ Atom.symbol)).foldr SExpr.cons .nil)
    unless cor == .cons (.atom (.symbol p)) (.cons appPat .nil) do
      throwError "replayGeneralize: tp corollary {repr cor} of {fnJ.name} \
                  does not justify restriction pred {p.name} at {cn.idStr} \
                  (frontier)"
    let argsJ := (argsSpineJ.toList?).getD []
    unless argsJ.length == fnFormals.length do
      throwError "replayGeneralize: arity mismatch instantiating the TP of \
                  {fnJ.name}"
    let fact := mkAppN tpHyp ((#[env] : Array Expr)
      ++ (argsJ.map reflectSExpr).toArray ++ #[valJ, convJ])
    -- the literal's value at env': not (pred (lookup ESi)) — defeq
    -- not (pred val_i) through the concrete bindArgsOver lookups
    let vLit ← ctxValExpr cfg' ctx' lit
    let convLit ← ctxValProof cfg' ctx' lit
    let hnilRaw ← mkAppM ``not_of_eq_t #[fact]
    let nilE := mkConst ``SExpr.nil
    let hnilTy ← mkEq vLit nilE
    unless ← isDefEq (← inferType hnilRaw) hnilTy do
      throwError "replayGeneralize: restriction value for {repr lit} does \
                  not reduce to the tp fact's subject at {cn.idStr} \
                  (internal)"
    let hnil ← mkExpectedTypeHint hnilRaw hnilTy
    let hLitNil ← mkAppM ``re_val_cast
      #[cfg.worldExpr, env', reflectSExpr lit, vLit, nilE, convLit, hnil]
    pChild ← mkAppM ``evtrue_tail_of_if_head_nil #[hLitNil, pChild]
  let coreTerm := disjoinTerm core
  -- substN bridge back to this env (over the CORE — the restrictions are
  -- gone and σ(core) is exactly this clause)
  let hWellScoped ← proveByDecide
    (← mkEq (← mkAppM ``ACL2.Replay.WellScoped #[reflectSExpr coreTerm])
            (mkConst ``Bool.true))
    "WellScoped generalize child"
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
    #[w, env, formalsE, argsE, valsE, reflectSExpr coreTerm, hWellScoped, hlenPf, hargs]
  mkAppM ``evtrue_of_fuel_eq #[pBridge, pChild]

end ACL2.Replay.Driver
