import ACL2Lean.Replay.Driver.Waterfall

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- Falsity of a disjunction supplies falsity of its actual indexed literal.
Shared by recorded linear insertion and elimination restriction queries. -/
def clauseLiteralFalsity (cfg : ReplayConfig) (ctx : ReplayCtx)
    (clause : List SExpr) (hFalse : Expr) (index : Nat) : MetaM (SExpr × Expr) := do
  let some lit := clause[index]? | throwError "clause falsity: literal index outside clause"
  let value ← ctxValExpr cfg ctx lit
  let eqNil ← mkEq value (mkConst ``SExpr.nil)
  let contra ← withLocalDeclD `hLiteralTrue (← mkAppM ``Not #[eqNil]) fun ht => do
    mkLambdaFVars #[ht] (mkApp hFalse (← evtrueOfLitTrue cfg ctx clause index lit ht))
  return (lit, ← mkAppM ``Classical.byContradiction #[contra])

/-- Reconstruct the emitted clause assuming its literals false, then close
that assumption by contradiction. No context snapshot is assumed as a fact. -/
def withClauseFalsity (cfg : ReplayConfig) (ctx : ReplayCtx) (clause : List SExpr)
    (build : ReplayCtx → MetaM Expr) : MetaM Expr := do
  let goal ← mkAppM ``EvTrue
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr (disjoinTerm clause)]
  let contra ← withLocalDeclD `hClauseFalse (← mkAppM ``Not #[goal]) fun hf => do
    let mut ctxF := ctx
    for index in List.range clause.length do
      let (lit, h) ← clauseLiteralFalsity cfg ctx clause hf index
      ctxF := { ctxF with litFacts := ctxF.litFacts ++ [(index + 1, lit, h)] }
    let proof ← mkExpectedTypeHint (← build ctxF) goal
    mkLambdaFVars #[hf] (mkApp hf proof)
  mkAppM ``Classical.byContradiction #[contra]

end ACL2.Replay.Driver
