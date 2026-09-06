import Tests.Ns1Arithmetic

/-! The multiplication-cancellation theorem remains open at its linear equation
insertion. These pins consume its six actual atom boundary prefixes/verdicts;
the arithmetic pins check actual emitted verdict leaves under the ordinary
command budget. Negative controls change only parsed records in memory. No native product is
claimed by these fragment checks. -/
open ACL2 ACL2.Replay ACL2.Replay.Driver Lean Lean.Meta Lean.Elab
namespace ACL2.Tests.Ns1Positive
private partial def boundaries (c : ClauseNode) : List LiteralProof :=
  let rec items (xs : List ClauseItem) : List LiteralProof := xs.flatMap fun
    | .literal lp => if lp.boundaryVerdicts.isEmpty then [] else [lp]
    | .branch _ ys => items ys
    | _ => []
  items (c.steps.flatMap (·.items)) ++ c.children.flatMap boundaries
private partial def useNode (c : ClauseNode) : Option ClauseNode :=
  if c.steps.any (fun s => s.items.any fun | .useHint .. => true | _ => false)
    then some c else c.children.findSome? useNode
private def expectRefusal (kind needle : String) (act : MetaM α) : MetaM Unit := do
  let msg ← try let _ ← act; pure none catch e => pure (some (← e.toMessageData.toString))
  let some msg := msg | throwError "{kind}: accepted"
  unless (msg.splitOn needle).length > 1 do throwError "{kind}: wrong refusal: {msg}"
  logInfo m!"{kind}: rejected by consuming check"
private def primitiveUseControls (cfg : ReplayConfig) (label : String)
    (hs raw : List SExpr) (tr : Option (List SExpr)) : MetaM Unit := do
  let .ok lmis := resolveUseLmis raw tr hs.length | throwError "LMIs"
  for (hyp, lmi) in hs.zip lmis do
    let some (_ :: .atom (.symbol name) :: pairs) := lmi.toList? | throwError "LMI shape"
    let subst ← pairs.mapM fun pair => do
      let some [.atom (.symbol formal), value] := pair.toList? | throwError "binding shape"
      return (formal, value)
    -- An identity :INSTANCE has no bindings: insert X explicitly so this
    -- negative control changes even that actual empty substitution.
    let badSubst := (({ name := "X" } : Symbol), quoteNil) ::
      ((subst.filter fun (v, _) => v.name != "X").map fun (v, _) => (v, quoteNil))
    expectRefusal (label ++ " changed substitution") "recorded substitution disagrees with :HYPS"
      (primitiveUseInstance? cfg {} name.name badSubst hyp)
    expectRefusal (label ++ " changed hypothesis") "recorded substitution disagrees with :HYPS"
      (primitiveUseInstance? cfg {} name.name subst quoteT)
elab "checkActualPositiveControls" : command => Command.liftTermElabM do
  let dev := Ns1Arithmetic.timesDev
  let some cp := findThm dev "<-OF-*-AND-*-CANCEL" | throwError "theorem"
  let some c := cp.root | throwError "root"
  let lps := boundaries c
  unless lps.length == 6 do throwError "actual boundary count differs"
  let w := mkConst ``Ns1Arithmetic.timesWorld
  for (lp, i) in lps.zipIdx do
    let p ← withLocalDeclD `env (mkConst ``Env) fun env => do
      let cfg := Runner.mkBookConfig dev dev.toWorld w env
      let (p, _) ← replayNegatedAtomBoundary cfg {} lp
      mkLambdaFVars #[env] p
    Meta.check p
    let name := Name.str `ACL2.Tests.Ns1Positive (s!"boundary{i}")
    addDecl (.thmDecl { name, levelParams := [], type := ← inferType p, value := p })
    let axioms ← Runner.collectProofAxioms (mkConst name)
    unless axioms.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "unexpected boundary axioms: {axioms}"
  logInfo "all six actual prefix/verdict compositions check with accepted axioms"
  let some lp := lps.head? | throwError "boundary"
  withLocalDeclD `env (mkConst ``Env) fun env => do
    let cfg := Runner.mkBookConfig dev dev.toWorld w env
    expectRefusal "missing prefix" "does not reach verdict input"
      (replayNegatedAtomBoundary cfg {} { lp with nodes := [] })
    expectRefusal "changed verdict input" "does not reach verdict input"
      (replayNegatedAtomBoundary cfg {} { lp with boundaryVerdicts := lp.boundaryVerdicts.map (fun st => { st with lhs := quoteNil }) })
    expectRefusal "changed verdict result" "verdict or literal polarity differs"
      (replayNegatedAtomBoundary cfg {} { lp with boundaryVerdicts := lp.boundaryVerdicts.map (fun st => { st with rhs := quoteNil }) })
    expectRefusal "changed polarity" "verdict or literal polarity differs"
      (replayNegatedAtomBoundary cfg {} { lp with notFlg := false })
    let some cn := useNode c | throwError "USE node"
    expectRefusal "missing CASES child" "child clauses differ from the recorded applications"
      (replayClause cfg {} { cn with children := cn.children.drop 1 })
    let hints := (cn.steps.flatMap (·.items)).filterMap fun
      | .useHint hs _ apps raw tr => some (hs, apps, raw, tr) | _ => none
    let [(hs, apps, raw, tr)] := hints | throwError "USE payload"
    primitiveUseControls cfg "POSITIVE" hs raw tr
    let clauses := apps.map (·.drop hs.length)
    let first :: second :: rest := clauses | throwError "case pair"
    let .error _ := recordedCasePartition cn.inputClause
      (first :: (quoteNil :: second.drop 1) :: rest) | throwError "changed case accepted"
    logInfo "changed CASES partition rejected"
checkActualPositiveControls
/-- These were the measured cancellation hot spots. Using the production
DP entry point preserves the exact emitted obligation and its type premises;
the ordinary command budget catches a return to constructor enumeration. -/
elab "checkActualRationalLeaves" : command => Command.liftTermElabM do
  let some cp := findThm Ns1Arithmetic.timesDev "<-OF-*-AND-*-CANCEL"
    | throwError "cancellation theorem absent"
  for id in ["Subgoal 2.4", "Subgoal 2.1", "Subgoal 1.7"] do
    let some (_, _, clause) := (theoremDischargeLeaves cp).find? (fun x => x.1 == id)
      | throwError "actual arithmetic leaf absent: {id}"
    let (tests, last) := dpSpine clause
    let vars := ((tests ++ [last]).flatMap freeVars).eraseDups
    let ops := ((tests ++ [last]).flatMap collectOpaques).eraseDups
    let stmt ← dpFactStmt tests last vars ops []
    let p ← proveDpFact stmt (vars.length + ops.length)
    Meta.checkWithKernel p
    let axioms ← Runner.collectProofAxioms p
    unless axioms.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "unexpected arithmetic leaf axioms: {axioms}"
    logInfo m!"actual {id}: production DP proof kernel-checked with accepted axioms"
checkActualRationalLeaves
replayed_theorem commutativityTwoReplayed :=
  driver_replayed% Ns1Arithmetic.timesDev Ns1Arithmetic.timesWorld "COMMUTATIVITY-2-OF-*"
theorem commutativityTwoSourcePinned (env : Env) :
    let x : SExpr := .atom (.symbol { name := "X" })
    let y : SExpr := .atom (.symbol { name := "Y" })
    let z : SExpr := .atom (.symbol { name := "Z" })
    let times := fun a b : SExpr => SExpr.ofList
      [.atom (.symbol { name := "BINARY-*" }), a, b]
    EvTrue Ns1Arithmetic.timesWorld env (SExpr.ofList
      [.atom (.symbol { name := "EQUAL" }), times x (times y z), times y (times x z)]) :=
  commutativityTwoReplayed env
/-- info: 'ACL2.Tests.Ns1Positive.commutativityTwoReplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms commutativityTwoReplayed

elab "checkActualAssociativityUseControls" : command => Command.liftTermElabM do
  let dev := Ns1Arithmetic.timesDev
  let some cp := findThm dev "COMMUTATIVITY-2-OF-*" | throwError "commutativity theorem absent"
  let some root := cp.root | throwError "root absent"
  let some cn := useNode root | throwError "actual associativity USE absent"
  let hints := (cn.steps.flatMap (·.items)).filterMap fun
    | .useHint hs _ _ raw tr => some (hs, raw, tr) | _ => none
  let [(hs, raw, tr)] := hints | throwError "actual associativity USE payload"
  withLocalDeclD `env (mkConst ``Env) fun env => do
    let cfg := Runner.mkBookConfig dev dev.toWorld (mkConst ``Ns1Arithmetic.timesWorld) env
    primitiveUseControls cfg "ASSOCIATIVITY-OF-*" hs raw tr
checkActualAssociativityUseControls
end ACL2.Tests.Ns1Positive
