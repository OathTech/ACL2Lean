import ACL2Lean.Replay.Driver.NodeCore.Compose
import ACL2Lean.Replay.Driver.TsFacts

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- Consume a cited defun TP whose corollary asserts INTEGERP, possibly with
an additional conjunct. INTEGERP-MOD cites the quotient TP inside its emitted
argument leaves. The corollary proof remains an ordinary replay obligation. -/
def inTsFromCitedIntegerTp (cfg : ReplayConfig) (ctx : ReplayCtx)
    (cited : List String) (t : SExpr) (tv : Expr) : MetaM (Option Expr) := do
  let .cons (.atom (.symbol fn)) argsSpine := t | return none
  unless cited.contains fn.name do return none
  let some (_, cor, tpHyp) := ctx.tpHyps.find? (fun (nm, _, _) => nm == fn.name)
    | return none
  let some (formals, _) := cfg.worldVal.defs.get? fn | return none
  let some args := argsSpine.toList? | return none
  unless formals.length == args.length do return none
  let inst := ACL2.Replay.substTerm formals args cor
  let recog := SExpr.ofList [.atom (.symbol { name := "INTEGERP" }), t]
  let conjunct? : Option SExpr := match inst.toList? with
    | some [.atom (.symbol ifS), c, th, el] =>
      if ifS.name == "IF" && c == recog && el == quoteNil then some th else none
    | _ => none
  unless inst == recog || conjunct?.isSome do return none
  let conv ← ctxValProof cfg ctx t
  let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
    ++ (args.map reflectSExpr).toArray ++ #[tv, conv])
  let hInt ← match conjunct? with
    | none => pure fact
    | some th => do
      let ctxTh ← pinTermOpaques cfg cfg.envExpr ctx th
      mkAppM ``tp_cond_integerp_t #[tv, ← ctxValExpr cfg ctxTh th, fact]
  let hb ← mkAppM ``congrArg #[mkConst ``Logic.toBool, hInt]
  return some (← mkExpectedTypeHint (← mkAppM ``inTs_integerp_true #[hb])
    (← mkAppM ``InTs #[Lean.toExpr (23 : Int), tv]))

end ACL2.Replay.Driver
