import ACL2Lean.Replay.Driver.NodeCore.ClausifyEval

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- Validate the actual selected exact-term or commutative EQUAL assumption. Other call-stack
lookup classes remain explicit frontiers, including an absent selected basis. -/
def clausifyCallSource (call : ClausifyCallAssumption) : Except String (SExpr × Bool) := do
  let app := fun name args => SExpr.cons (.atom (.symbol { name })) (SExpr.ofList args)
  unless call.input == app "NOT" [call.query] &&
      call.output == (if call.value then quoteNil else quoteT) do
    throw "clausify call: input/query/value/output mismatch"
  let parseSign := fun sign => do
    let sign ← match sign with
      | .atom (.keyword "TRUE") => pure true
      | .atom (.keyword "FALSE") => pure false
      | _ => throw "clausify call: malformed assumption sign"
    unless sign == call.value do throw "clausify call: selected sign differs from returned value"
    return sign
  if let some [.atom (.keyword "KIND"), .atom (.keyword "EXACT-TERM"),
      .atom (.keyword "TERM"), source, .atom (.keyword "SIGN"), sign] := call.basis.toList? then
    unless source == call.query do throw "clausify call: selected exact term differs from query"
    return (source, ← parseSign sign)
  let some [.atom (.keyword "KIND"), .atom (.keyword "COMMUTATIVE-BINARY"),
      .atom (.keyword "TERM"), source, .atom (.keyword "SIGN"), sign,
      .atom (.keyword "FN"), .atom (.symbol fn)] := call.basis.toList?
    | throw "clausify call: unsupported selected assumption basis"
  let sign ← parseSign sign
  unless fn == ({ name := "EQUAL" } : Symbol) do
    throw "clausify call: commutative function has no checked recipe"
  let some (qfn, [x, y]) := asApp call.query
    | throw "clausify call: query is not a binary call"
  unless qfn == fn && (source == call.query || source == app "EQUAL" [y, x]) do
    throw "clausify call: selected assumption does not match query or its commute"
  return (source, sign)

/-- Check one emitted NOT call from the selected in-scope assumption only. -/
def replayClausifyCall (cfg : ReplayConfig) (ctx : ReplayCtx)
    (facts : List (SExpr × Expr × Bool × Expr)) (call : ClausifyCallAssumption) :
    MetaM Expr := do
  let (source, sign) ← ofExcept (clausifyCallSource call)
  let mut ctx := ctx
  for term in [call.input, call.query, source] do
    ctx ← pinTermOpaques cfg cfg.envExpr ctx term
  let sourceValue ← ctxValExpr cfg ctx source
  let nilC := mkConst ``SExpr.nil
  let expected ← if sign then mkAppM ``Ne #[sourceValue, nilC] else mkEq sourceValue nilC
  let fromPath? := (facts ++ ctx.branchFacts).find? fun (t, _, s, _) => t == source && s == sign
  let sourceProof ← match fromPath? with
    | some (_, _, _, h) => do
      unless ← isDefEq (← inferType h) expected do
        throwError "clausify call: selected path fact is outside this environment"
      pure h
    | none => do
      let literal := if sign then
        SExpr.cons (.atom (.symbol { name := "NOT" })) (.cons source .nil) else source
      let lv ← if sign then pure (mkApp (mkConst ``Logic.not) sourceValue) else pure sourceValue
      let some h ← ctx.litFactByTermChecked? literal (← mkEq lv nilC)
        | throwError "clausify call: selected assumption {repr source} is not in scope"
      if sign then mkAppM ``logic_not_nil_ne #[sourceValue, h] else pure h
  let queryProof ← if source == call.query then pure sourceProof else do
    let some (_, [x, y]) := asApp call.query | throwError "clausify call: binary query lost"
    let comm ← mkAppM ``logic_equal_comm #[← ctxValExpr cfg ctx x, ← ctxValExpr cfg ctx y]
    if sign then mkAppM ``ne_of_eq_of_ne #[comm, sourceProof]
    else mkAppM ``Eq.trans #[comm, sourceProof]
  let valueProof ← if sign then mkAppM ``not_nil_of_truthy #[queryProof]
    else mkAppM ``logic_not_t_of_nil #[queryProof]
  let outputValue := if sign then SExpr.nil else SExpr.t
  let inputConv ← ctxValProof cfg ctx call.input
  let outputConv ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr outputValue]
  mkAppM ``fuel_eq_of_conv #[inputConv, outputConv, valueProof]

/-- Consume every recorded call in order during the literal's actual bottom-up
CALL traversal. This lane disables legacy assumption reconstruction: the selected
record is the only source of each assumption fold. Unused records fail. -/
def collapseWithCallAssumptions (cfg : ReplayConfig) (ctx : ReplayCtx)
    (facts : List (SExpr × Expr × Bool × Expr)) (term : SExpr)
    (calls : List ClausifyCallAssumption) : MetaM (Option Expr × SExpr) := do
  if calls.isEmpty then return ← collapseEval cfg ctx facts term
  let pending ← IO.mkRef calls
  let consume := fun input => do
    let call :: rest ← pending.get | return none
    if call.input != input then return none
    let proof ← replayClausifyCall cfg ctx facts call
    pending.set rest
    return some (proof, call.output)
  let result ← collapseEval cfg ctx facts term (some consume)
  unless (← pending.get).isEmpty do
    throwError "clausify call: unused or out-of-order call assumption record"
  return result

end ACL2.Replay.Driver
