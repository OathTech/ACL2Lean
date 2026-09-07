import ACL2Lean.Replay.Driver.NodeCore.TypeSetWalk

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- Consume the executed NIL-left/right arm of rewrite-equal. The existing
primitive normalization lemma checks its exact IF result. -/
def replayEqualNil (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode) : MetaM Expr := do
  let .node r lhs rhs kids p := n
  let some (f, [a, b]) := asApp lhs | throwError "NIL equality: malformed lhs"
  unless r.ty == "equal-nil" && f.name == "EQUAL" && kids.isEmpty && p.equiv == "equal" do
    throwError "NIL equality: node shape/equivalence mismatch"
  let (term, law) ←
    if p.origin == "equal/nil-lhs" && a == quoteNil then pure (b, ``re_equal_nil_norm_l)
    else if p.origin == "equal/nil-rhs" && b == quoteNil then pure (a, ``re_equal_nil_norm_r)
    else throwError "NIL equality: origin/operands mismatch"
  unless rhs == SExpr.ofList [.atom (.symbol { name := "IF" }), term, quoteNil, quoteT] do
    throwError "NIL equality: result differs from the recorded IF normalization"
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx term
  mkAppM law #[cfg.worldExpr, cfg.envExpr, reflectSExpr term,
    ← proveNoShadow cfg f, ← proveConv cfg cfg.envExpr ctx term]

/-- rewrite-equal's recorded Boolean equality normalization. The mask and
addressed IF leaves select the primitive type-set proof; no DP is used. -/
def replayEqualBoolean (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode) : MetaM Expr := do
  let .node r lhs rhs kids p := n
  let some (f, [a, b]) := asApp lhs | throwError "Boolean equality: bad lhs"
  unless r.ty == "equal-boolean" && f.name == "EQUAL" && kids.isEmpty && p.equiv == "equal" do
    throwError "Boolean equality: node shape/equivalence mismatch"
  let isLeft := p.origin == "equal/boolean-lhs"
  unless (isLeft && b == quoteT && rhs == a) ||
      (p.origin == "equal/boolean-rhs" && a == quoteT && rhs == b) do
    throwError "Boolean equality: origin/operands/result mismatch"
  let some ts := p.typeSet | throwError "Boolean equality: missing operand mask"
  unless tsSubsumedM ts 384 do throwError "Boolean equality: operand mask is not Boolean"
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx lhs
  let v ← ctxValExpr cfg ctx rhs
  let citedCr := p.runes.filterMap fun r => if r.ty == "compound-recognizer" then some r.name else none
  let citedTp := p.runes.filterMap fun r => if r.ty == "type-prescription" then some r.name else none
  let h? ← if let some (f, _) := asApp rhs then
      if f.name == "IF" then
        inTsFromArgLeaves cfg ctx p.argLeaves [] citedCr rhs ts citedTp
      else inTsFromCtx cfg ctx [] citedCr rhs v ts citedTp
    else inTsFromCtx cfg ctx [] citedCr rhs v ts citedTp
  let some h := h? | throwError "Boolean equality: recorded operand type cannot be replayed"
  let h ← mkAppM ``inTs_weaken #[← tsSubsumedProofM ts 384, h]
  let eq ← mkAppM ``equal_t_of_inTs #[h]
  let eq ← if isLeft then pure eq else do
    mkAppM ``Eq.trans #[← mkAppM ``logic_equal_comm #[mkConst ``SExpr.t, v], eq]
  mkAppM ``fuel_eq_of_conv #[← ctxValProof cfg ctx lhs, ← ctxValProof cfg ctx rhs, eq]

end ACL2.Replay.Driver
