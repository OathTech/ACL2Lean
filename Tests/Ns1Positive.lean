import Tests.Ns1Arithmetic

/-! The multiplication-cancellation theorem remains open at its linear equation
insertion. These pins consume its six actual atom boundary prefixes/verdicts;
negative controls change only parsed records in memory. No native product is
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
    let .ok lmis := resolveUseLmis raw tr hs.length | throwError "LMIs"
    for (hyp, lmi) in hs.zip lmis do
      let some (_ :: .atom (.symbol name) :: pairs) := lmi.toList? | throwError "LMI shape"
      let subst ← pairs.mapM fun pair => do
        let some [.atom (.symbol formal), value] := pair.toList? | throwError "binding shape"
        return (formal, value)
      expectRefusal "POSITIVE changed substitution" "recorded substitution disagrees with :HYPS"
        (primitiveUseInstance? cfg {} name.name (subst.map fun (v, _) => (v, quoteNil)) hyp)
      expectRefusal "POSITIVE changed hypothesis" "recorded substitution disagrees with :HYPS"
        (primitiveUseInstance? cfg {} name.name subst quoteT)
    let clauses := apps.map (·.drop hs.length)
    let first :: second :: rest := clauses | throwError "case pair"
    let .error _ := recordedCasePartition cn.inputClause
      (first :: (quoteNil :: second.drop 1) :: rest) | throwError "changed case accepted"
    logInfo "changed CASES partition rejected"
checkActualPositiveControls
end ACL2.Tests.Ns1Positive
