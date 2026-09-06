import Tests.Ns1Arithmetic

/-! The positive EQUAL-DENOMINATOR-1 pin is in Ns1Arithmetic. These controls
alter one actual parsed record in memory and require the relevant consuming
check to reject it. The captured artifact and the source book stay untouched. -/
open ACL2 ACL2.Replay ACL2.Replay.Driver Lean
namespace ACL2.Tests.Ns1Contexts

private def capture : String := include_str "../acl2_samples/ns1/numerator-and-denominator.proof-log"
private def sym (s : String) : SExpr := .atom (.symbol { name := s })
private def app (s : String) (xs : List SExpr) : SExpr := .cons (sym s) (SExpr.ofList xs)

elab "ns1_context_controls%" : command => Elab.Command.liftTermElabM do
  let .ok log := ProofLog.parse capture | throwError "context controls: capture parse failed"
  -- All constructor fields must be matched: omitting the optional classes
  -- field would match only legacy declarations with classes = none.
  let names := log.events.filterMap fun
    | .defthm n _ _ _ => some n
    | _ => none
  unless names.contains "EQUAL-DENOMINATOR-1" &&
      (ProofLog.splitByTheorem log).map (·.1) == names &&
      ((ProofLog.summary log).splitOn s!"Theorems: {names.length} (").length == 2 do
    throwError "BUG-043: modern theorem declarations missing from reporting helpers"
  for kind in ["missing-alias", "wrong-postpass-equation", "wrong-discharge-clause"] do
    let active ← IO.mkRef false
    let changed ← IO.mkRef (0 : Nat)
    let events ← log.events.mapM fun ev => do
      match ev with
      | .defthm name _ _ _ =>
        active.set (name == "EQUAL-DENOMINATOR-1")
        pure ev
      | .step s =>
        unless (← active.get) do return ev
        let traceEvents ← s.traceEvents.flatMapM fun ev => do
          match ev with
          | .contextSubst x value _ =>
            if kind == "missing-alias" && x == sym "X" && value ==
                app "BINARY-*" [app "UNARY-/" [app "DENOMINATOR" [sym "X"]],
                  app "NUMERATOR" [sym "X"]] then
              changed.modify (· + 1)
              return []
          | .branchSubstitution equiv lhs _ =>
            if kind == "wrong-postpass-equation" && lhs == app "DENOMINATOR" [sym "X"] then
              changed.modify (· + 1)
              return [.branchSubstitution equiv lhs
                (app "QUOTE" [.atom (.number (.int 2))])]
          | .rewriteStep st =>
            if kind == "wrong-discharge-clause" &&
                st.origin == "rewrite-clause/type-alist-contradiction" &&
                (match asApp st.lhs with
                  | some (_, test :: _) => test == app "RATIONALP" [sym "X"]
                  | _ => false) then
              changed.modify (· + 1)
              return [.rewriteStep { st with lhs := app "IF" [quoteNil, quoteT, st.lhs] }]
          | _ => pure ()
          return [ev]
        pure (.step { s with traceEvents })
      | _ => pure ev
    unless (← changed.get) == 1 do
      throwError "context controls: {kind} did not change exactly one actual record"
    let .ok bad := ClauseTree.buildDevelopment { log with events }
      | throwError "context controls: reconstruction failed before consumption"
    let some cp := findThm bad "EQUAL-DENOMINATOR-1"
      | throwError "context controls: target missing"
    let deps := (developmentTheoremsWithRules bad).map (fun (p, _) => (p.name, p))
    Meta.withLocalDeclD `env (mkConst ``Env) fun env => do
      let cfg : ReplayConfig := {
        worldExpr := mkConst ``Ns1Arithmetic.numdenWorld, envExpr := env,
        worldVal := bad.toWorld, gzDefs := bad.groundZeroSnapshotDefs,
        justs := bad.justifications }
      let failure ← try
        let _ ← replayProofConditional cfg bad.typePrescriptions cp bad.justifications
          (rulesBefore bad cp.name) deps
        pure none
      catch e => pure (some (← e.toMessageData.toString))
      let some failure := failure | throwError "context controls: {kind} was accepted"
      let expected := if kind == "missing-alias" then "replayRecognizer"
        else if kind == "wrong-postpass-equation" then "residual postpass: no equation justifies"
        else "whole-clause discharge node lhs"
      unless (failure.splitOn expected).length > 1 do
        throwError "context controls: unexpected {kind} failure: {failure}"
      logInfo m!"context {kind} rejected at its consuming check"

ns1_context_controls%

private def productCapture : String := include_str "../acl2_samples/ns1/basic.proof-log"

elab "ns1_product_marker_control%" : command => Elab.Command.liftTermElabM do
  let .ok log := ProofLog.parse productCapture | throwError "product marker: capture parse failed"
  let active ← IO.mkRef false
  let changed ← IO.mkRef (0 : Nat)
  let events ← log.events.mapM fun ev => do
    match ev with
    | .defthm name _ _ _ =>
      active.set (name == "(< (* x y) 0)")
      pure ev
    | .step s =>
      unless (← active.get) do return ev
      let traceEvents ← s.traceEvents.flatMapM fun ev => do
        if let .ifTestTrue test _ _ := ev then
          if test == app "<" [app "QUOTE" [.atom (.number (.int 0))], sym "X"] then
            changed.modify (· + 1)
            return []
        return [ev]
      pure (.step { s with traceEvents })
    | _ => pure ev
  unless (← changed.get) == 1 do
    throwError "product marker: did not remove exactly one actual IF decision"
  let .ok bad := ClauseTree.buildDevelopment { log with events }
    | throwError "product marker: reconstruction failed before consumption"
  let some cp := findThm bad "(< (* x y) 0)" | throwError "product marker: target missing"
  let (status, _) ← Runner.tryReplay bad bad.toWorld (mkConst ``Ns1Arithmetic.bindBasicWorld)
    cp (rulesBefore bad cp.name)
    (crossTrees := Runner.bookTrees Ns1Arithmetic.pass1Dev ++
      Runner.bookTrees Ns1Arithmetic.inequalitiesDev)
    (crossRules := Runner.combineRules (Runner.allBookRules Ns1Arithmetic.pass1Dev)
      (Runner.allBookRules Ns1Arithmetic.inequalitiesDev))
  unless (status.splitOn "FAIL: replayClauseSpine: literal 3 chain reached").length > 1 do
    throwError "product marker: unexpected result after removing the decision: {status}"
  logInfo "product marker removal rejected at the literal-chain consumer"

ns1_product_marker_control%

private def congruenceCapture : String :=
  include_str "../acl2_samples/ns1/basic-arithmetic-helper.proof-log"

elab "ns1_congruence_substitution_control%" : command => Elab.Command.liftTermElabM do
  let .ok log := ProofLog.parse congruenceCapture | throwError "congruence control: capture parse failed"
  let active ← IO.mkRef false
  let changed ← IO.mkRef (0 : Nat)
  let events ← log.events.mapM fun ev => do
    match ev with
    | .defthm name _ _ _ =>
      active.set (name == "EQUIV-1-IMPLIES-EQUIV-*")
      pure ev
    | .step s =>
      unless (← active.get) do return ev
      let traceEvents ← s.traceEvents.flatMapM fun ev => do
        if let .branchSubstitution _ _ _ := ev then
          changed.modify (· + 1)
          return []
        return [ev]
      pure (.step { s with traceEvents })
    | _ => pure ev
  unless (← changed.get) == 1 do
    throwError "congruence control: did not remove exactly one actual substitution"
  let .ok bad := ClauseTree.buildDevelopment { log with events }
    | throwError "congruence control: reconstruction failed before consumption"
  let some cp := findThm bad "EQUIV-1-IMPLIES-EQUIV-*" | throwError "congruence control: target missing"
  let (status, _) ← Runner.tryReplay bad bad.toWorld (mkConst ``Ns1Arithmetic.helperWorld)
    cp (rulesBefore bad cp.name)
  unless (status.splitOn "FAIL: replayClauseSpine: equal-self literal").length > 1 &&
      (status.splitOn "not in the clause").length > 1 do
    throwError "congruence control: unexpected result after removing substitution: {status}"
  logInfo "congruence substitution removal rejected at equal-self clause membership"

ns1_congruence_substitution_control%

end ACL2.Tests.Ns1Contexts
