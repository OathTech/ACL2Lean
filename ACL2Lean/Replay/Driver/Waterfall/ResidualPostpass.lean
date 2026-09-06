import ACL2Lean.Replay.Driver.Waterfall

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

/-- Replay the recorded remove-trivial-equivalences postpass on a residual
    clause. Unlike the scan's in-clause substitution, this pass retains the
    negative equality that justified the substitution. Its falsity is already
    proved on the selected segment. Every recorded operation is checked, and
    only the resulting exact clause can be handed to a pushed child.

    First witness: EQUAL-DENOMINATOR-1, Goal', whose denominator substitution
    and reciprocal constant fold change an earlier accumulated literal. -/
def replayResidualPostpass (rec : ClauseRec) (cfg : ReplayConfig)
    (ctx : ReplayCtx) (idStr : String) (clause : List SExpr)
    (items : List ClauseItem) (children : List ClauseNode) : MetaM Expr := do
  let mut ctx := ctx
  let mut current := clause
  let mut chain : Option Expr := none
  for item in items do
    let .step n := item
      | throwError "residual postpass: non-step continuation at {idStr} (frontier)"
    let .node rune lhs rhs childNodes prov := n
    if rune.ty == "context-subst" then
      unless childNodes.isEmpty do
        throwError "residual postpass: context substitution has children at {idStr}"
      ctx := { ctx with contextSubsts := ctx.contextSubsts ++ [(lhs, rhs)] }
      continue
    ctx ← pinTermOpaques cfg cfg.envExpr ctx lhs
    ctx ← pinTermOpaques cfg cfg.envExpr ctx rhs
    let (stepEq, next) ←
      if rune.ty == "branch-substitution" then do
        unless prov.equivTerm == some (.atom (.symbol { name := "EQUAL" })) &&
            childNodes.isEmpty do
          throwError "residual postpass: substitution relation/children at {idStr} (frontier)"
        let some (a, b, hf, truthy) := (inScopeEquations ctx).find? fun (a, b, _, _) =>
            (a == lhs && b == rhs) || (a == rhs && b == lhs)
          | throwError "residual postpass: no equation justifies {repr lhs} => {repr rhs} at {idStr}"
        let some hEq ← composeEqChain cfg ctx [(a, b, hf, truthy, a != lhs)]
          | throwError "residual postpass: empty equation at {idStr}"
        unless ← isDefEq (← inferType hEq)
            (← mkEq (← ctxValExpr cfg ctx lhs) (← ctxValExpr cfg ctx rhs)) do
          throwError "residual postpass: equation has the wrong value type at {idStr}"
        let stepEq ← mkAppM ``fuel_eq_of_conv
          #[← ctxValProof cfg ctx lhs, ← ctxValProof cfg ctx rhs, hEq]
        let next := current.map fun L =>
          match notEqualSides? L with
          | some (a, b) =>
            if (a == lhs && b == rhs) || (a == rhs && b == lhs) then L
            else replaceTermOcc lhs rhs L
          | none => replaceTermOcc lhs rhs L
        pure (stepEq, next)
      else if rune.ty == "executable-counterpart" then do
        let (stepEq, relation) ← replayNode cfg ctx n
        unless relation.isNone do
          throwError "residual postpass: executable step is not equality at {idStr}"
        let next := current.map (replaceTermOcc lhs rhs)
        unless next != current do
          throwError "residual postpass: executable step changes no literal at {idStr}"
        pure (stepEq, next)
      else
        throwError "residual postpass: unsupported {rune.ty}/{nodeOrigin n} at {idStr}"
    if let some lifted ← diffCollapse cfg.worldExpr cfg.envExpr lhs rhs stepEq
        (disjoinTerm current) (disjoinTerm next) then
      chain := some (← chainAfter chain lifted)
    current := next
    ctx ← pinTermOpaques cfg cfg.envExpr ctx (disjoinTerm current)
  -- subst-equiv-and-maybe-delete-lit rebuilds through add-literal-and-pt,
  -- which removes quoted NIL after the recorded constant folds.
  let (ctx', lits, drops) ← dropFoldedNilLiterals cfg ctx idStr
    (current.zipIdx.map fun (l, i) => (i + 1, l))
  ctx := ctx'
  current := lits.map (·.2)
  for drop in drops do
    chain := some (← chainAfter chain drop)
  let [child] := children.filter (·.inputClause == current)
    | throwError "residual postpass: no unique pushed child matches {repr current} at {idStr}"
  let p ← rec.clause cfg { ctx with litFacts := [], dedupDrops := [] } child
  evtrueWith chain p

end ACL2.Replay.Driver
