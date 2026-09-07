import ACL2Lean.Replay.Driver.NodeCore.TypeSetWalk

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- The shared semantic type of a stored LINEAR or single-conclusion FC
rule. Rule metadata and proof provenance stay in their separate callers. -/
def mkStoredImplicationType (cfg : ReplayConfig) (hyps : List SExpr) (concl : SExpr) : MetaM Expr := do
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let target := mkAppN (mkConst ``EvTrue) #[cfg.worldExpr, envV, reflectSExpr concl]
    let body ← hyps.foldrM (fun h acc => do
      mkArrow (mkAppN (mkConst ``EvTrue) #[cfg.worldExpr, envV, reflectSExpr h]) acc) target
    mkForallFVars #[envV] body

def mkFcHypType (cfg : ReplayConfig) (spec : FcRuleSpec) : MetaM Expr := do
  let [concl] := spec.concls | throwFrontier m!"FC implication: multiple conclusions"
  mkStoredImplicationType cfg spec.hyps concl

/-- Transport all antecedents and the conclusion through the supplied
substitution bridge. The LINEAR caller selects its recorded trigger;
the FC caller supplies the explicitly emitted substitution. -/
def instantiateStoredImplication (cfg : ReplayConfig) (sb : SubstNBridge)
    (hyps : List SExpr) (concl : SExpr) (inst : SExpr → SExpr) (hypV : Expr) : MetaM Expr := do
  let decls := hyps.zipIdx.toArray.map fun (h, i) =>
    (Name.mkSimple s!"hPremise{i}", BinderInfo.default,
      fun (_ : Array Expr) => pure (mkAppN (mkConst ``EvTrue)
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr (inst h)]))
  withLocalDecls decls fun hs => do
    let sourceHyps ← hyps.zipIdx.toArray.mapM fun (h, i) => do
      mkAppM ``evtrue_of_fuel_eq #[← mkAppM ``fuel_eq_symm #[← sb.bridge h], hs[i]!]
    let cSource := mkAppN hypV (#[sb.env'] ++ sourceHyps)
    let cBack ← mkAppM ``evtrue_of_fuel_eq #[← sb.bridge concl, cSource]
    mkLambdaFVars hs cBack

end ACL2.Replay.Driver
