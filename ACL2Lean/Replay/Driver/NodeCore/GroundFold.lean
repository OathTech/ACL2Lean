import ACL2Lean.Replay.Driver.NodeCore.Ctx

/-! ACL2 cons-term's ground folding domain, read from the real capture.
The result is an admissibility check; the caller separately kernel-checks
the closed value computation and the surrounding congruence chain. -/

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- Find a concrete fuel/value for a closed computation. Shared by recorded
    executable counterparts and clausification's permitted ground folds.
    The existing fuel ceiling is unchanged; failure remains explicit. -/
def findGroundValue (cfg : ReplayConfig) (lhs : SExpr) : MetaM (Nat × SExpr) := do
  unless (ACL2.Replay.freeVars lhs).isEmpty do
    throwError "ground computation: lhs {repr lhs} has free variables"
  let mut F := 8
  let mut v? : Option SExpr := none
  while v?.isNone && F ≤ 65536 do
    v? := ACL2.evalOpt F cfg.worldVal {} lhs
    if v?.isNone then F := F * 2
  let some v := v?
    | throwError "ground computation: {repr lhs} does not converge by fuel 65536"
  return (F, v)

/-- Ground `executable-counterpart` computation: ACL2 ran the executable
    counterpart of a CLOSED term `lhs`, recording the result `v`. The kernel
    re-checks the SAME computation by reducing `evalOpt` at a concrete fuel
    (found by running the evaluator) and lifts by fuel monotonicity. Returns
    `∃N∀f≥N, eval lhs = some v`. Hard-fails if `lhs` is open or the evaluator
    diverges from ACL2's recorded result — this is the carve-out's faithful
    mirror (ACL2 records only a verdict; we re-run the same closed computation),
    NOT a license to compute through open terms. -/
def replayExecGround (cfg : ReplayConfig) (lhs v : SExpr) : MetaM Expr := do
  let (F, vComputed) ← findGroundValue cfg lhs
  unless vComputed == v do
    throwError "executable-counterpart: evalOpt computes {repr vComputed}, \
                the recorded result is {repr v} — evaluator/ACL2 divergence on {repr lhs}"
  -- PARAMETRIC route (Phase 2 item c): over an abstract `worldExpr` the
  -- reduction check below cannot run — derive the convergence
  -- COMPOSITIONALLY instead (`dpValProof`: quote/IF/registered-builtin
  -- steps, whose only world dependence is the no-shadow hypotheses), then
  -- pin it to the recorded value's statement (defeq for a ground term —
  -- the dp value form and the recorded constant are both closed).
  unless cfg.noShadowHyps.isEmpty do
    let p ← dpValProof cfg cfg.envExpr [] [] (fun _ => none) lhs
    let target ← mkConvStmt cfg lhs v
    unless ← withTransparency .all <| isDefEq (← inferType p) target do
      throwError "executable-counterpart (parametric): the compositional \
        convergence proof for {repr lhs} does not state the recorded value \
        {repr v} (dp value form/recorded constant mismatch)"
    return ← mkExpectedTypeHint p target
  let lhsApp := mkApp4 (mkConst ``evalOpt) (mkNatLit F) cfg.worldExpr cfg.envExpr
    (reflectSExpr lhs)
  let someV ← mkAppM ``Option.some #[reflectSExpr v]
  -- Closed executable arithmetic includes core Rat operations, which are
  -- irreducible to ordinary elaboration. The kernel can unfold them; this
  -- local check must use the same definitional equality.
  unless ← withTransparency .all <| isDefEq lhsApp someV do
    throwError "executable-counterpart: evalOpt {F} … {repr lhs} does not REDUCE \
                to {repr v} (env-dependence or reflected-world mismatch?)"
  let hAt ← mkExpectedTypeHint (← mkEqRefl someV) (← mkEq lhsApp someV)
  mkAppM ``conv_of_eval_at
    #[mkNatLit F, cfg.worldExpr, cfg.envExpr, reflectSExpr lhs, reflectSExpr v, hAt]


def consTermGroundValue? (cfg : ReplayConfig) (fn : Symbol)
    (args : List SExpr) : MetaM (Option SExpr) := do
  let allQuoted := args.all fun
    | .cons (.atom (.symbol q)) (.cons _ .nil) => q.name == "QUOTE"
    | _ => false
  unless allQuoted do return none
  -- call-stack treats EQUAL and IFF explicitly, independently of cons-term.
  -- NOT has its own existing collapse arm; IF is handled before this call.
  unless fn.name == "EQUAL" || fn.name == "IFF" do
    let some spec := cfg.consTermGuards.find? (·.fn == fn)
      | return none
    unless spec.formals.length == args.length do
      throwError "cons-term: arity mismatch for emitted primitive {fn.name}"
    let guardTerm := substTerm spec.formals args spec.guardTerm
    let (_, guardValue) ← findGroundValue cfg guardTerm
    unless Logic.toBool guardValue do return none
  let term := SExpr.cons (.atom (.symbol fn)) (SExpr.ofList args)
  return some (← findGroundValue cfg term).2

end ACL2.Replay.Driver
