import ACL2Lean.Replay.Driver.NodeCore.TypeSetWalk

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

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
