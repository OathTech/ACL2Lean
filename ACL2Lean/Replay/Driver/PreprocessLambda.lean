import ACL2Lean.Replay.Driver.NodeCore
import ACL2Lean.Replay.Lemmas.LambdaBody

/-! Recorded abbreviation paths may enter an unopened lambda body. This
boundary changes the environment, unlike ordinary argument congruence. -/

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

def hasLambdaBodyFrame (frames : List PathFrame) : Bool :=
  frames.any fun
    | .boundary k _ => k.name == "LAMBDA-BODY"
    | _ => false

/-- Replay one recorded equality under its exact abbreviation path, including
lambda-body boundaries. No occurrence search or evaluator shortcut is used. -/
partial def replayPreprocessBodyPath
    (replay : ReplayConfig → ReplayCtx → ProofNode → MetaM Expr)
    (cfg : ReplayConfig) (ctx : ReplayCtx) (current : SExpr)
    (frames : List PathFrame) (node : ProofNode) : MetaM (Expr × SExpr) := do
  let (lhs, rhs) := nodeLhsRhs node
  let .node _ _ _ _ prov := node
  unless prov.equiv == "equal" do
    throwFrontier m!"preprocess lambda body: non-equality {prov.equiv}"
  let isBody : PathFrame → Bool := fun
    | .boundary k _ => k.name == "LAMBDA-BODY"
    | _ => false
  let outerFrames := frames.takeWhile (fun f => !isBody f)
  let rest := frames.drop outerFrames.length
  let (path, baseL, baseR, proof) ← match rest with
    | [] => do
      let path ← ofExcept (pathStepsFromFrames current frames lhs)
      pure (path, lhs, rhs, ← replay cfg ctx node)
    | .boundary _ fn :: innerFrames => do
      let (path, lamApp) ← ofExcept (navigateFrames current outerFrames)
      let some (head, lam, args) := asLamApp lamApp
        | throwError "preprocess lambda body: recorded boundary enters {repr lamApp}"
      unless fn == lam do
        throwError "preprocess lambda body: frame head {fn.name} differs from {lam.name}"
      let some (_, formalsE, body) := asLamHead head
        | throwError "preprocess lambda body: malformed head {repr head}"
      let some formals := ACL2.lamFormals? formalsE
        | throwError "preprocess lambda body: malformed formals {repr formalsE}"
      unless args.length == formals.length && (args.length == 1 || args.length == 2) do
        throwFrontier m!"preprocess lambda body: unsupported binder/actual arity"
      -- Only function-level hypotheses survive entry into a fresh body
      -- environment. Clause facts and outer occurrence/variable pins do not.
      let bodyCtx : ReplayCtx := {
        totalHyps := ctx.totalHyps, tpHyps := ctx.tpHyps,
        tpHypsAv := ctx.tpHypsAv, ruleHyps := ctx.ruleHyps }
      let (bodyProof, body') ← withLocalDeclD `bodyEnv (mkConst ``Env) fun env' => do
        let (p, body') ← replayPreprocessBodyPath replay { cfg with envExpr := env' }
          bodyCtx body innerFrames node
        pure (← mkLambdaFVars #[env'] p, body')
      let (hlam, hform, _) ← dpValProof.lamCerts lam formalsE body formals
      let argConvs ← args.mapM (proveConv cfg cfg.envExpr ctx)
      let common := #[cfg.worldExpr, cfg.envExpr, reflectSymbol lam,
        reflectSExpr formalsE, reflectSExpr body, reflectSExpr body']
      let proof ← match formals, args, argConvs with
        | [f], [a], [ha] =>
          mkAppM ``re_lam_body1_eq
            (common ++ #[reflectSExpr a, reflectSymbol f, hlam, hform, ha, bodyProof])
        | [f1, f2], [a, b], [ha, hb] =>
          mkAppM ``re_lam_body2_eq
            (common ++ #[reflectSExpr a, reflectSExpr b, reflectSymbol f1,
              reflectSymbol f2, hlam, hform, ha, hb, bodyProof])
        | _, _, _ => throwError "preprocess lambda body: checked arity changed"
      let rhsApp : SExpr := .cons (.cons (.atom (.symbol lam))
        (.cons formalsE (.cons body' .nil))) (SExpr.ofList args)
      pure (path, lamApp, rhsApp, proof)
    | _ => throwError "preprocess lambda body: unexpected boundary {repr rest}"
  let mut p := proof
  let mut l := baseL
  let mut r := baseR
  for step in path.reverse do
    p ← applyStep cfg.worldExpr cfg.envExpr step l r p
    l := rebuild step l
    r := rebuild step r
  unless l == current do
    throwError "preprocess lambda body: reconstructed source differs from current term"
  return (p, r)

end ACL2.Replay.Driver
