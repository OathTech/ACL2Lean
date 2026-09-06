import ACL2Lean.Replay.Driver.Waterfall

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- Recognize only a recorded two-argument equality alias, with its exact body. -/
def equalityAlias? (cfg : ReplayConfig) (source target : SExpr) :
    Option (Symbol × Symbol × Symbol × SExpr × SExpr) := do
  let .cons (.atom (.symbol fn)) (.cons a (.cons b .nil)) := source | none
  let .cons (.atom (.symbol eq)) (.cons a' (.cons b' .nil)) := target | none
  guard (eq.name == "EQUAL" && a == a' && b == b')
  let some ([f1, f2], body) := cfg.worldVal.defs.get? fn | none
  guard (f1 != f2)
  guard (body == .cons (.atom (.symbol eq))
    (.cons (.atom (.symbol f1)) (.cons (.atom (.symbol f2)) .nil)))
  return (fn, f1, f2, a, b)

/-- Prove the recognized alias's value equality through its world definition. -/
def equalityAliasValue (cfg : ReplayConfig) (ctx : ReplayCtx)
    (source target : SExpr) : MetaM Expr := do
  let some (fn, f1, f2, a, b) := equalityAlias? cfg source target
    | throwError "ruling alias: unsupported source/target"
  let di ← deriveDefInfoN cfg fn
  let va ← ctxValExpr cfg ctx a
  let vb ← ctxValExpr cfg ctx b
  let vs ← ctxValExpr cfg ctx source
  let pa ← ctxValProof cfg ctx a
  let pb ← ctxValProof cfg ctx b
  let ps ← ctxValProof cfg ctx source
  let hbody ← mkAppM ``re_body_conv2
    #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1, reflectSymbol f2,
      reflectSExpr di.body, reflectSExpr a, reflectSExpr b, va, vb, vs,
      ← proveNotSpecial fn, di.defFact, pa, pb, ps]
  let envBody ← mkAppM ``bindArgs
    #[← mkListLit (mkConst ``Symbol) [reflectSymbol f1, reflectSymbol f2],
      ← mkListLit (mkConst ``SExpr) [va, vb]]
  let pbody ← dpValProof { cfg with envExpr := envBody } envBody [] [] (fun _ => none) di.body
  let heq ← mkAppM ``conv_unique #[hbody, pbody]
  let expected ← mkEq vs (← ctxValExpr cfg ctx target)
  unless ← isDefEq (← inferType heq) expected do
    throwError "ruling alias: body value does not align with target"
  mkExpectedTypeHint heq expected

/-- Decompose only the actual false OR-form test and prove the requested leaf. -/
partial def falseRulerComponent? (cfg : ReplayConfig) (ctx : ReplayCtx)
    (source target : SExpr) (hNil : Expr) : MetaM (Option Expr) := do
  let expected ← mkEq (← ctxValExpr cfg ctx source) (mkConst ``SExpr.nil)
  unless ← isDefEq (← inferType hNil) expected do
    throwError "ruling component: recorded fact has a different value"
  let hNil ← mkExpectedTypeHint hNil expected
  if source == target then return some hNil
  if (equalityAlias? cfg source target).isSome then
    let eq ← equalityAliasValue cfg ctx source target
    return some (← mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[eq], hNil])
  match source with
  | .cons (.atom (.symbol fn)) (.cons a (.cons a2 (.cons c .nil))) =>
    if fn.name == "IF" && a == a2 then
      let pair ← mkAppM ``cond_or_nil_inv #[hNil]
      if let some h ← falseRulerComponent? cfg ctx a target (← mkAppM ``And.left #[pair]) then
        return some h
      falseRulerComponent? cfg ctx c target (← mkAppM ``And.right #[pair])
    else return none
  | _ => return none

def falseRulingFact? (cfg : ReplayConfig) (ctx : ReplayCtx)
    (facts : List TestFact) (target : SExpr) : MetaM (Option Expr) := do
  for f in facts do
    if !f.sign then
      if let some h ← falseRulerComponent? cfg ctx f.test target f.signE then
        return some h
  return none
end ACL2.Replay.Driver
