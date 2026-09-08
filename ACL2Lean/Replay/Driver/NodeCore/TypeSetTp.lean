import ACL2Lean.Replay.Driver.NodeCore.Compose
import ACL2Lean.Replay.Driver.TsFacts
import ACL2Lean.Replay.Driver.TpCorollary
import ACL2Lean.Replay.Lemmas.TsListFacts

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- Consume a cited defun TP's value-only corollary. INTEGERP-MOD
cites the quotient TP in its argument leaves; sorting's Boolean equality
step cites PERM. Recorded sorting queries also consume true-list and
nonnegative-integer classes. The corollary proof remains an ordinary replay obligation. -/
def inTsFromCitedTp (cfg : ReplayConfig) (ctx : ReplayCtx)
    (cited : List String) (t : SExpr) (tv : Expr) : MetaM (Option (Int × Expr)) := do
  let .cons (.atom (.symbol fn)) argsSpine := t | return none
  unless cited.contains fn.name do return none
  let some (_, cor, tpHyp) := ctx.tpHyps.find? (fun (nm, _, _) => nm == fn.name)
    | return none
  let some (formals, _) := cfg.worldVal.defs.get? fn | return none
  let some args := argsSpine.toList? | return none
  unless formals.length == args.length do return none
  let inst := ACL2.Replay.substTerm formals args cor
  let conv ← ctxValProof cfg ctx t
  let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
    ++ (args.map reflectSExpr).toArray ++ #[tv, conv])
  -- Share the TP prover's exact corollary classification. These constant
  -- classes retain the whole checked corollary rather than extracting only
  -- its INTEGERP conjunct (which would lose ACL2-COUNT's nonnegative mask).
  let cls := tpCorClass? t inst
  let membership := match cls with
    | some .nonNegInt => some (7, ``inTs_of_nonNegIntCor)
    | some .trueListp => some (1152, ``inTs_of_trueListp_t)
    | _ => none
  if let some (mask, lemmaName) := membership then
    return some (mask, ← mkExpectedTypeHint (← mkAppM lemmaName #[fact])
      (← mkAppM ``InTs #[Lean.toExpr (mask : Int), tv]))
  let eqT (x y : SExpr) := SExpr.ofList [.atom (.symbol { name := "EQUAL" }), x, y]
  let booleanCor := SExpr.ofList [.atom (.symbol { name := "IF" }),
    eqT t quoteT, quoteT, eqT t quoteNil]
  if inst == booleanCor then
    let h ← mkAppM ``tp_boolean_t_or_nil #[tv, fact]
    return some (384, ← mkExpectedTypeHint (← mkAppM ``inTs_of_boolean_range #[h])
      (← mkAppM ``InTs #[Lean.toExpr (384 : Int), tv]))
  let recog := SExpr.ofList [.atom (.symbol { name := "INTEGERP" }), t]
  let conjunct? : Option SExpr := match inst.toList? with
    | some [.atom (.symbol ifS), c, th, el] =>
      if ifS.name == "IF" && c == recog && el == quoteNil then some th else none
    | _ => none
  unless inst == recog || conjunct?.isSome do return none
  let hInt ← match conjunct? with
    | none => pure fact
    | some th => do
      let ctxTh ← pinTermOpaques cfg cfg.envExpr ctx th
      mkAppM ``tp_cond_integerp_t #[tv, ← ctxValExpr cfg ctxTh th, fact]
  let hb ← mkAppM ``congrArg #[mkConst ``Logic.toBool, hInt]
  return some (23, ← mkExpectedTypeHint (← mkAppM ``inTs_integerp_true #[hb])
    (← mkAppM ``InTs #[Lean.toExpr (23 : Int), tv]))

end ACL2.Replay.Driver
