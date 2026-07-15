/-
  TAMPER tests for the theorem-dependency (`rule:<thm>`) recompute-and-check
  joints (audit 2026-07-06 hardening): each test corrupts ONE emitted record of
  the REAL perm-transitive replay — a stored rule, a node's :SUBST, the relief
  markers — and asserts the replay REJECTS it with the expected joint failure.
  A tamper that replays anyway is a soundness/fidelity hole and FAILS the build.

  The one deliberate non-rejection: tampering a stored rule's HYPS changes the
  STATED hypothesis (the conditional mirror's type), which the replay cannot
  detect — that is what the committed type-pin in DriverTests locks.
-/
import ACL2Lean.Replay.Driver
import ACL2Lean.ProofLog
import ACL2Lean.ClauseTree
import Lean

open ACL2 ACL2.Replay ACL2.Replay.Driver Lean Lean.Elab Lean.Meta

namespace ACL2.Tests.Tamper

private def permLog : String := include_str "../acl2_samples/sorting/perm.proof-log"

private def permDev : Development :=
  (((ProofLog.parse permLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

private def permTransCp : Option ClauseProof := do
  let log ← (ProofLog.parse permLog).toOption
  let dev ← (ClauseTree.buildDevelopment log).toOption
  findThm dev "perm-transitive"

/-! ### Node-level tamper helpers (map a function over every ProofNode) -/

private partial def mapNode (f : ProofNode → ProofNode) : ProofNode → ProofNode
  | .node r l rh ch p => f (.node r l rh (ch.map (mapNode f)) p)

private partial def mapItem (f : ProofNode → ProofNode) : ClauseItem → ClauseItem
  | .literal lp => .literal { lp with nodes := lp.nodes.map (mapNode f) }
  | .step n => .step (mapNode f n)
  | .branch seg its => .branch seg (its.map (mapItem f))
  | .clausify i => .clausify i

private partial def mapClause (f : ProofNode → ProofNode) (n : ClauseNode) : ClauseNode :=
  { n with
    steps := n.steps.map fun s => { s with items := s.items.map (mapItem f) },
    children := n.children.map (mapClause f) }

private def mapProof (f : ProofNode → ProofNode) (cp : ClauseProof) : ClauseProof :=
  { cp with root := cp.root.map (mapClause f) }

/-- Drop HYP-kind children matching `pred` from every node (marker removal). -/
private partial def dropHypChildren (pred : ProofNode → Bool) : ProofNode → ProofNode
  | .node r l rh ch p =>
    .node r l rh ((ch.filter (fun c => !pred c)).map (dropHypChildren pred)) p

derive_world tamperWorld from permDev

/-- Run the CONDITIONAL replay of the (tampered) perm-transitive and require it
    to THROW with `expect` in the message. Succeeding, or failing with an
    unrelated message, fails the build. -/
private def assertRejected (label expect : String) (cp : ClauseProof)
    (rules : List RuleSpec) : TermElabM Unit := do
  Meta.withLocalDeclD `env (mkConst ``Env) fun env => do
    let cfg : ReplayConfig :=
      { worldExpr := mkConst ``ACL2.Tests.Tamper.tamperWorld, envExpr := env,
        worldVal := permDev.toWorld, gzNames := permDev.groundZeroDefunNames }
    try
      let (_, conds) ← replayProofConditional cfg permDev.typePrescriptions cp
        permDev.justifications rules
      throwError "TAMPER NOT REJECTED ({label}): replay succeeded with \
                  conditions {conds}"
    catch e =>
      let msg ← e.toMessageData.toString
      if (msg.splitOn "TAMPER NOT REJECTED").length > 1 then
        throw e
      unless (msg.splitOn expect).length > 1 do
        throwError "TAMPER ({label}): rejected, but not at the expected \
                    joint — wanted …{expect}…, got: {msg}"
      logInfo m!"tamper rejected as expected ({label}): …{expect}…"

elab "run_tamper_tests% " : command => Lean.Elab.Command.liftTermElabM do
  let cpOpt ← unsafe evalExpr (Option ClauseProof)
    (mkApp (mkConst ``Option [0]) (mkConst ``ACL2.ClauseProof))
    (mkConst ``permTransCp)
  let some cp := cpOpt | throwError "permTransCp: parse/extract failed"
  let rules := rulesBefore permDev "perm-transitive"
  -- T1: DELETE the cited rule from the stored-rule offers → the recipe must
  -- fail at the rule lookup, never invent the statement.
  assertRejected "rule deleted" "no stored-rule hypothesis in scope" cp
    (rules.filter (·.name != "perm-symmetric"))
  -- T2: TAMPER the stored rule's rhs ('t → 'nil) → the rhs recompute-and-check
  -- joint must reject (node rhs ≠ substTerm(σ, rule rhs)).
  assertRejected "rule rhs tampered" "RHS continuation (frontier)" cp
    (rules.map fun r =>
      if r.name == "perm-symmetric" then { r with rhs := quoteNil } else r)
  -- T3: TAMPER a node's emitted :SUBST (swap the two bindings' terms) → the
  -- lhs joint must reject (substTerm(σ, rule lhs) ≠ node lhs → 0 matches).
  let cpSubst := mapProof (fun n => match n with
    | .node r l rh ch p =>
      if r == ("rewrite", "perm-symmetric") then
        .node r l rh ch { p with subst := p.subst.map fun (v, _) => (v, quoteNil) }
      else n) cp
  assertRejected ":SUBST tampered" "stored rules match" cpSubst rules
  -- T4: DROP the silent-relief markers → the relief-record requirement
  -- (audit finding A) must reject: no marker, no chain ⇒ emission gap.
  let cpNoMarkers := mapProof
    (dropHypChildren (fun c => (runeOf c).1 == "hyp-relief")) cp
  assertRejected "relief markers dropped" "NO emitted relief record" cpNoMarkers rules

run_tamper_tests%

end ACL2.Tests.Tamper
