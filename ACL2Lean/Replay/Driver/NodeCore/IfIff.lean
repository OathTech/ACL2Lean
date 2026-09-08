import ACL2Lean.Replay.Driver.NodeCore.Congruence

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- Select the recorded test prefix in the owning IF's coordinate space.
An RHS window is eligible only when its complete identity and entry frame
match the owner. Other window-local paths never become literal positions.
The caller replays this selection and checks the recorded final test. -/
def ifTestPrefix (owner : StepProvenance) (priorNodes : List ProofNode) : List ProofNode :=
  let rel := relativizeFrames owner.path
  priorNodes.filterMap fun pn =>
    let .node _ _ _ _ p := pn
    let sameWindow := if owner.innerKind == "" then p.innerKind == "" else
      owner.innerKind == "rhs" && p.innerKind == owner.innerKind &&
      owner.innerTerm.isSome && p.innerTerm == owner.innerTerm &&
      p.innerPath == owner.innerPath && p.innerSwapped == owner.innerSwapped &&
      p.innerIfTest == owner.innerIfTest && p.path.take 1 == owner.path.take 1
    if !sameWindow then none else
    let pr := relativizeFrames p.path
    if pr.take rel.length != rel then none else
    match pr.drop rel.length with
    | .arg 1 _ :: _ =>
      let node := if owner.innerKind == "" then pn else clearWindowTag pn
      some (retargetAtIf node (rel.length + 1))
    | _ => none

/-- ACL2's constant-test OR optimization reuses the rewritten test for its
then-copy. The recorded test chain supplies that copy's value; only its
truthiness is preserved by the emitted result 'T. -/
private theorem evrel_siff_constant_copy (w : World) (env : Env) (a b c : SExpr) (hc : c ≠ .nil)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env a = evalOpt f w env (quoteVal c)) :
    EvRel SIff w env (.cons (.atom (.symbol { name := "IF" }))
      (.cons (quoteVal c) (.cons a (.cons b .nil)))) (quoteVal SExpr.t) := by
  have pc := conv_quote_val w env c
  have pa := fuel_conv_of_eq h pc
  have pi := conv_if_true w env (quoteVal c) a b c c pc (toBool_true_of_ne_nil hc) pa
  obtain ⟨ni, hi⟩ := pi
  obtain ⟨nt, ht⟩ := conv_quote_val w env SExpr.t
  exact ⟨ni + nt, fun f hf => ⟨c, SExpr.t, hi f (by omega), ht f (by omega),
    by simp [SIff, hc, SExpr.t]⟩⟩

private def constantPayload (rec : NodeRec) (cfg : ReplayConfig) (ctx : ReplayCtx)
    (n : ProofNode) (priorNodes : List ProofNode) : MetaM Expr := do
  let .node rune lhs rhs kids prov := n
  unless rune.ty == "if-simplification" && prov.equiv == "iff" &&
      prov.origin == "rewrite-if/constant-test" && kids.isEmpty &&
      prov.innerKind == "" && rhs == quoteT do throwError "constant-copy record"
  let some (ifs, [test, a, b]) := asApp lhs | throwError "IF shape"
  unless ifs.name == "IF" do throwError "IF name"
  let .cons (.atom (.symbol qs)) (.cons c .nil) := test | throwError "constant test"
  unless qs.name == "QUOTE" do throwError "quote name"
  if c == .nil then throwError "false test"
  let testNodes := ifTestPrefix prov priorNodes
  let (chain, final) ← rec.rewrites cfg ctx a testNodes
  unless final == test do throwError "test-copy chain endpoint differs"
  let some chain ← chainReqEq chain | throwError "missing recorded test-copy chain"
  let hc ← proveByDecide (← mkAppM ``Ne #[reflectSExpr c, mkConst ``SExpr.nil]) "truthy constant"
  mkAppM ``evrel_siff_constant_copy #[cfg.worldExpr, cfg.envExpr, reflectSExpr a,
    reflectSExpr b, reflectSExpr c, hc, chain]

/-- The IFF-only IF simplifications, lifted through the existing relation
congruences. A Boolean consumer must turn SIff into equality before root. -/
def replayIfIff (rec : NodeRec) (cfg : ReplayConfig) (ctx : ReplayCtx)
    (start : SExpr) (n : ProofNode) (priorNodes : List ProofNode) :
    MetaM (Expr × SExpr) := do
  let .node rune lhs rhs kids prov := n
  unless rune.ty == "if-simplification" && prov.equiv == "iff" && kids.isEmpty do
    throwError "IFF IF simplification: unexpected node"
  let rel := relativizeFrames prov.path
  let steps ← ofExcept (pathStepsFromFrames start rel lhs)
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx lhs
  let payload ← if prov.origin == "rewrite-if/constant-test" then
    constantPayload rec cfg ctx n priorNodes
  else do
    let .cons (.atom (.symbol ifS)) (.cons a (.cons a2 (.cons bT .nil))) := lhs
      | throwError "IFF IF simplification: lhs is not IF"
    unless ifS.name == "IF" && a == a2 do
      throwError "IFF IF simplification: lhs is not the recorded OR shape"
    let expectedRhs : SExpr := .cons (.atom (.symbol ifS))
      (.cons a (.cons quoteT (.cons bT .nil)))
    unless rhs == expectedRhs do throwError "IFF OR simplification: RHS differs"
    mkAppM ``evrel_siff_if_or_shape
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr a, reflectSExpr bT,
        ← ctxValExpr cfg ctx a, ← ctxValExpr cfg ctx bT,
        ← ctxValProof cfg ctx a, ← ctxValProof cfg ctx bT]
  let mut inner := payload
  let mut innerIff := true
  let mut curL := lhs
  let mut curR := rhs
  for st in steps.reverse do
    if innerIff then
      let (p, still) ← applyStepSIff cfg ctx st inner
      inner := p
      innerIff := still
    else
      inner ← applyStep cfg.worldExpr cfg.envExpr st curL curR inner
    curL := rebuild st curL
    curR := rebuild st curR
  unless curL == start do
    throwError "replayRewrites: IFF IF lift reconstructed \
        {repr curL} ≠ running {repr start}"
  if innerIff then
    throwError "replayRewrites: IFF IF chain still IFF at the \
        literal root (frontier — R-parameterized literal chains)"
  return (inner, curR)

end ACL2.Replay.Driver
