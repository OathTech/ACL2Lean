/-
  Driver/Waterfall/Fertilize — the FERTILIZE-CLAUSE (cross-fertilization)
  recipe (emission arc, 2026-07-21; docs/notes/2026-07-21_emission-arc.md).

  ACL2's fertilize-clause uses a clause literal `(not (equiv lhs rhs))` to
  substitute one side of the equality for the other THROUGHOUT the clause,
  deleting the used literal (under induction). The step's emitted
  `:FERTILIZE` detail carries :BULLET (the term substituted IN), :TARGET
  (the term substituted FOR), :EQUIV, :LITERAL (the justifying literal),
  :CROSS-FERT-FLG and :DELETE-LIT-FLG.

  Replay (EQUAL equiv, cross-fert NIL): byCases on the literal's value —
  - TRUTH closes the whole disjunction (`evtrueOfLitTrue`);
  - FALSITY gives `v(lhs) = v(rhs)` (`logic_not_equal_nil_eq`), the used
    literal's if-frame collapses out of the disjunction (`re_if_false`
    lifted through the preceding frames), `diffCollapse` transports the
    shortened disjunction onto the substituted clause (recorded output,
    checked exactly), and the CHILD's replay closes it. When delete-lit is
    NIL, the recorded output retains the equality inside HIDE; its false
    IF frame is restored before the child is used.
-/
import ACL2Lean.Replay.Driver.Waterfall

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- Replace every occurrence of `frm` by `to'` (fertilize's full-substitution
    mode, cross-fert-flg NIL). -/
private partial def replaceAllTerm (frm to' : SExpr) (t : SExpr) : SExpr :=
  if t == frm then to'
  else match t with
    | .cons a b => .cons (replaceAllTerm frm to' a) (replaceAllTerm frm to' b)
    | _ => t

/-- Remove a false literal's IF frame, lifted through its actual prefix.
The retained-equality route uses this on both the input and HIDE-wrapped
output, so the ordinary deletion route shares the same composition. -/
private def dropFertilizeFrame (cfg : ReplayConfig) (ctx : ReplayCtx)
    (input : List SExpr) (kPos : Nat) (literal : SExpr) (hNil : Expr) : MetaM Expr := do
  let w := cfg.worldExpr
  let e := cfg.envExpr
  let shortened := input.eraseIdx kPos
  let hcNil ← castConvToNil cfg ctx literal hNil
  let tailTerm := disjoinTerm (input.drop (kPos + 1))
  let vTail ← ctxValExpr cfg ctx tailTerm
  let hTail ← ctxValProof cfg ctx tailTerm
  let mut inner ← mkAppM ``re_if_false
    #[w, e, reflectSExpr literal, reflectSExpr quoteT, reflectSExpr tailTerm,
      vTail, hcNil, hTail]
  let mut curL : SExpr := .cons (.atom (.symbol { name := "IF" }))
    (.cons literal (.cons quoteT (.cons tailTerm .nil)))
  let mut curR : SExpr := tailTerm
  for l in (input.take kPos).reverse do
    let stp : PathStep := { fn := { name := "IF" }, arity := 3, argIdx := 2,
                            siblings := [l, quoteT] }
    inner ← applyStep w e stp curL curR inner
    curL := rebuild stp curL
    curR := rebuild stp curR
  unless curL == disjoinTerm input && curR == disjoinTerm shortened do
    throwError "replayFertilize: frame-removal lift reconstructed \
                {repr curL} / {repr curR} at position {kPos}"
  return inner

def replayFertilize (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx)
    (cn : ClauseNode) (st : WaterfallStep) : MetaM Expr := do
  let w := cfg.worldExpr
  let e := cfg.envExpr
  let some fertS := st.extraFields.lookup "fertilize"
    | throwError "replayFertilize: no :FERTILIZE detail at {cn.idStr}"
  let items := fertS.toList?.getD []
  let get (k : String) : MetaM SExpr := do
    let rec go : List SExpr → Option SExpr
      | .atom (.keyword k') :: v :: rest =>
        if k' == k then some v else go rest
      | _ => none
    match go items with
    | some v => pure v
    | none => throwError "replayFertilize: :FERTILIZE missing :{k} at {cn.idStr}"
  let bullet ← get "BULLET"
  let target ← get "TARGET"
  let equivS ← get "EQUIV"
  let literal ← get "LITERAL"
  let crossFert ← get "CROSS-FERT-FLG"
  let deleteLit ← get "DELETE-LIT-FLG"
  unless equivS == .atom (.symbol { name := "EQUAL" }) do
    throwError "replayFertilize: equiv {repr equivS} at {cn.idStr} \
                (frontier — EQUAL only; IFF/user equivs route through L2)"
  unless crossFert == .nil do
    throwError "replayFertilize: cross-fert-flg set at {cn.idStr} (frontier — \
                positional cross-fertilization not yet mirrored)"
  unless deleteLit == SExpr.t || deleteLit == .nil do
    throwError "replayFertilize: non-Boolean delete-lit-flg at {cn.idStr}"
  -- the justifying literal (not (equal A B)) and the substitution direction
  let .cons (.atom (.symbol ns)) (.cons
      eqT@(.cons (.atom (.symbol es)) (.cons a (.cons b .nil))) .nil) := literal
    | throwError "replayFertilize: :LITERAL {repr literal} is not \
                  (not (equal _ _)) at {cn.idStr}"
  unless ns.name == "NOT" && es.name == "EQUAL" do
    throwError "replayFertilize: :LITERAL {repr literal} is not \
                (not (equal _ _)) at {cn.idStr}"
  unless (bullet == a && target == b) || (bullet == b && target == a) do
    throwError "replayFertilize: :BULLET/:TARGET are not the :LITERAL's \
                equality sides at {cn.idStr}"
  let input := cn.inputClause
  let some kPos := input.idxOf? literal
    | throwError "replayFertilize: :LITERAL not in the input clause at {cn.idStr}"
  unless kPos + 1 < input.length do
    throwError "replayFertilize: :LITERAL is the clause's LAST literal at \
                {cn.idStr} (frontier)"
  let shortened := input.eraseIdx kPos
  let substituted := shortened.map (replaceAllTerm target bullet)
  let app := fun name args => SExpr.ofList (.atom (.symbol {name}) :: args)
  let hiddenLiteral := app "NOT" [app "HIDE" [eqT]]
  let output := if deleteLit == SExpr.t then substituted else
    input.mapIdx fun i lit => if i == kPos then hiddenLiteral else replaceAllTerm target bullet lit
  -- fail-closed against the RECORDED output clause
  match st.newClauses with
  | [recorded] =>
    let some recordedL := recorded.toList?
      | throwError "replayFertilize: recorded output clause is not a list \
                    at {cn.idStr}"
    unless output == recordedL do
      throwError "replayFertilize: computed substitution {repr output} ≠ \
                  recorded output {repr recordedL} at {cn.idStr}"
  | _ => throwError "replayFertilize: expected exactly one output clause at \
                     {cn.idStr}"
  let some child := cn.children.find? (·.inputClause == output)
    | throwError "replayFertilize: no child clause matches the substituted \
                  clause at {cn.idStr}"
  -- pin every opaque the values below will need
  let mut ctx := ctx
  ctx ← pinTermOpaques cfg e ctx (disjoinTerm input)
  ctx ← pinTermOpaques cfg e ctx (disjoinTerm substituted)
  ctx ← pinTermOpaques cfg e ctx (disjoinTerm output)
  let vLit ← ctxValExpr cfg ctx literal
  let pLit ← ctxValProof cfg ctx literal
  let nilC := mkConst ``SExpr.nil
  let negL ← withLocalDeclD `hnil (← mkEq vLit nilC) fun hNil => do
    -- v(a) = v(b), oriented target ⇒ bullet
    let va ← ctxValExpr cfg ctx a
    let vb ← ctxValExpr cfg ctx b
    let hEq ← mkAppM ``logic_not_equal_nil_eq #[va, vb, hNil]  -- va = vb
    let hVeq ← if target == a then pure hEq else mkAppM ``Eq.symm #[hEq]
    let nodeEq ← mkAppM ``fuel_eq_of_conv
      #[← ctxValProof cfg ctx target, ← ctxValProof cfg ctx bullet, hVeq]
    let inner ← dropFertilizeFrame cfg ctx input kPos literal hNil
    -- substitute target ⇒ bullet across the shortened disjunction
    let chainSub ← diffCollapse w e target bullet nodeEq
      (disjoinTerm shortened) (disjoinTerm substituted)
    let chainAll ← chainWith inner chainSub
    let chainAll ← if deleteLit == SExpr.t then pure chainAll else do
      -- HIDE keeps the original equality; it is false under exactly the
      -- same checked value fact. Restore its frame before using the child.
      let hiddenDrop ← dropFertilizeFrame cfg ctx output kPos hiddenLiteral hNil
      chainWith chainAll (← mkAppM ``fuel_eq_symm #[hiddenDrop])
    -- the child replays STANDALONE (its own literal walk / processors)
    let pChild ← rec.clause cfg { ctx with litFacts := [], dedupDrops := [] } child
    let p ← mkAppM ``evtrue_of_fuel_eq #[chainAll, pChild]
    mkLambdaFVars #[hNil] p
  let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[vLit, nilC]) fun hNe => do
    let p ← evtrueOfLitTrue cfg ctx input kPos literal hNe
    mkLambdaFVars #[hNe] p
  let _ := pLit
  mkAppM ``Classical.byCases #[negL, posL]

end ACL2.Replay.Driver
