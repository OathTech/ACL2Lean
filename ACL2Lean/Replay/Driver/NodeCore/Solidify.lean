import ACL2Lean.Replay.Driver.TypeSetQuery
import ACL2Lean.Replay.Lemmas.TsSingletonFacts

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- Check the recorded Boolean singleton exclusion and the actual selected
entry. Operand support is restricted to the recorded primitive Boolean range
and a quoted singleton; recursive type derivations need their own records. -/
def replaySolidifySingleton (cfg : ReplayConfig) (ctx : ReplayCtx)
    (n : ProofNode) (basis : TaSingletonBasis) : MetaM Expr := do
  let .node rune lhs rhs children prov := n
  let app := fun name args => SExpr.cons (.atom (.symbol { name })) (SExpr.ofList args)
  unless rune.ty == "type-alist" && prov.origin == "solidify/type-alist" &&
      prov.equiv == "equal" && children.isEmpty &&
      basis.equality == app "EQUAL" [basis.left, basis.right] do
    throwError "singleton exclusion: node or source equality mismatch"
  let (term, constant, termMask, constantMask) ← match basis.side with
    | 1 => pure (basis.left, basis.right, basis.leftMask, basis.rightMask)
    | 2 => pure (basis.right, basis.left, basis.rightMask, basis.leftMask)
    | _ => throwError "singleton exclusion: invalid selected side"
  let (cv, output, mask, law) ←
    if constant == quoteNil && constantMask == 128 then
      pure (SExpr.nil, SExpr.t, (256 : Int), ``boolean_exclude_nil)
    else if constant == quoteT && constantMask == 256 then
      pure (SExpr.t, SExpr.nil, (128 : Int), ``boolean_exclude_t)
    else throwError "singleton exclusion: unsupported quoted singleton/mask"
  unless termMask == 384 && lhs == term && rhs == app "QUOTE" [output] &&
      prov.typeSet == some mask &&
      basis.entry == SExpr.ofList [term, .atom (.number (.int mask))] do
    throwError "singleton exclusion: operand mask, selected entry or output mismatch"
  let some (fn, [a, b]) := asApp term
    | throwError "singleton exclusion: operand has no recorded primitive range"
  let some range := tsBooleanBinaryRangeOf fn.name
    | throwError "singleton exclusion: operand type requires an unrecorded derivation"
  let _ ← proveNoShadow cfg fn
  let mut ctx := ctx
  for t in [basis.equality, term] do ctx ← pinTermOpaques cfg cfg.envExpr ctx t
  let equalityValue ← ctxValExpr cfg ctx basis.equality
  let some hEq ← ctx.litFactByTermChecked? basis.equality
      (← mkEq equalityValue (mkConst ``SExpr.nil))
    | throwError "singleton exclusion: recorded source equality is not false in scope"
  let v ← ctxValExpr cfg ctx term
  let hEq ← if basis.side == 1 then pure hEq else do
    mkAppM ``Eq.trans #[← mkAppM ``logic_equal_comm #[v, reflectSExpr cv], hEq]
  let hRange ← mkAppM range #[← ctxValExpr cfg ctx a, ← ctxValExpr cfg ctx b]
  let hType ← mkAppM ``inTs_of_boolean_range #[hRange]
  let hValue ← mkAppM law #[hType, hEq]
  mkAppM ``fuel_eq_of_conv #[← ctxValProof cfg ctx lhs,
    ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr output], hValue]

/-- The emitted equal/type-set-true verdict on two singleton-zero cells.
No context is manufactured: both actual operand masks must already check. -/
def replayTypeSetSingletonEquality (cfg : ReplayConfig) (ctx : ReplayCtx)
    (n : ProofNode) : MetaM Expr := do
  let .node rune lhs rhs kids p := n
  let some (fn, [a, b]) := asApp lhs
    | throwError "singleton equality: malformed binary equality"
  unless rune.ty == "type-set-equality" && p.origin == "equal/type-set-true" &&
      p.equiv == "equal" && fn.name == "EQUAL" && rhs == quoteT && kids.isEmpty &&
      p.lhsTs == some 1 && p.rhsTs == some 1 do
    throwError "singleton equality: unsupported emitted operand cells or node shape"
  let some raw := p.operandTypeBasis
    | throwError "singleton equality: missing executed operand queries"
  let fs ← tsQueryRead (TsQueryCapture.fields raw ["TYPE-ALIST", "QUERIES"])
  let ta ← tsQueryRead (TsQueryCapture.typeAlist (← tsQueryRead (TsQueryCapture.required fs "TYPE-ALIST")))
  let [qa, qb] ← tsQueryRead (TsQueryCapture.asList (← tsQueryRead (TsQueryCapture.required fs "QUERIES")))
    | throwError "singleton equality: expected the two executed operand queries"
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx lhs
  let check (term query : SExpr) : MetaM Expr := do
    let q ← tsQueryRead (TsQueryCapture.query query)
    unless q.term == term && q.result == 1 do
      throwError "singleton equality: operand query term/mask mismatch"
    checkTsQueryLookups ta query
    replayTsQuery cfg ctx query
  let ha ← check a qa
  let hb ← check b qb
  let h ← mkAppM ``equal_t_of_zero_cells #[ha, hb]
  mkAppM ``fuel_eq_of_conv #[← ctxValProof cfg ctx lhs,
    ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, mkConst ``SExpr.t], h]

/-- Consume SOLIDIFY's recorded singleton mask. The context proves the
value; the emitted mask only selects this primitive singleton cell. -/
def replaySolidifyConstant (cfg : ReplayConfig) (ctx : ReplayCtx)
    (n : ProofNode) : MetaM Expr := do
  let .node _ lhs rhs _ prov := n
  let cv := SExpr.atom (.number (.int 0))
  unless rhs == .cons (.atom (.symbol {name := "QUOTE"})) (.cons cv .nil) &&
      prov.origin == "solidify/type-alist" && prov.typeSet == some 1 do
    throwError "type-alist: unsupported recorded value/mask {repr rhs}/{repr prov.typeSet} (frontier)"
  let v ← ctxValExpr cfg ctx lhs
  let some hv ← inTsFromCtx cfg ctx [] [] lhs v 1
    | throwFrontier m!"type-alist: no checked context for emitted zero mask on {repr lhs}"
  let he ← mkAppM ``zero_of_inTs1 #[hv]
  let pl ← ctxValProof cfg ctx lhs
  let pr ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr cv]
  mkAppM ``fuel_eq_of_conv #[pl, pr, he]

end ACL2.Replay.Driver
