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

end ACL2.Tests.Ns1Contexts
