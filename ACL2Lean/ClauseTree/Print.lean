import ACL2Lean.ClauseTree.Core

namespace ACL2

/-! ## Tree printers (shared by the `acl2lean` CLI and the focused replay binary) -/

partial def printProofNodes (nodes : List ACL2.ProofNode) (indent : Nat) : IO Unit := do
  for node in nodes do
    match node with
    | .node rune lhs rhs children prov =>
      let pad := String.ofList (List.replicate (indent * 2) ' ')
      let originStr := if prov.origin.isEmpty then "" else s!" [{prov.origin}]"
      let windowStr := if prov.innerKind.isEmpty then "" else
        s!" ⟨{prov.innerKind}{if prov.blockKind.isEmpty then "" else s!" in {prov.blockKind}"}⟩"
      IO.println s!"{pad}{rune.tag}{originStr}{windowStr}"
      IO.println s!"{pad}  {lhs} => {rhs}"
      if let some wt := prov.innerTerm then
        IO.println s!"{pad}  window: {wt} @ {repr prov.innerPath}"
      if let some basis := prov.operandTypeBasis then
        IO.println s!"{pad}  operand type queries: {basis}"
      if let some basis := prov.taSingletonBasis then
        IO.println s!"{pad}  singleton exclusion: {basis.equality}, side {basis.side}"
        IO.println s!"{pad}  operand masks {basis.leftMask}/{basis.rightMask}; entry {basis.entry}"
      if let some basis := prov.comparisonBasis then
        IO.println s!"{pad}  comparison result {basis.resultTs}: {basis.route}"
      if !prov.runes.isEmpty then
        let runeStrs := prov.runes.map (·.tag)
        IO.println s!"{pad}  runes: {String.intercalate ", " runeStrs}"
      if !prov.subst.isEmpty then
        let substStrs := prov.subst.map fun (k, v) => s!"{k} → {v}"
        IO.println s!"{pad}  subst: {String.intercalate ", " substStrs}"
      if let some basis := prov.substBasis then
        if !basis.folds.isEmpty then
          IO.println s!"{pad}  unfolded hypothesis: {basis.input}"
          for fold in basis.folds do
            IO.println s!"{pad}  substitution fold @ {repr fold.path}: {fold.lhs} => {fold.rhs}"
      if let some eq := prov.equivTerm then
        IO.println s!"{pad}  equiv: {eq}"
      if let some src := prov.equivSource then
        match src with
        | .literal idx =>
          IO.println s!"{pad}  ⮑ justified by hypothesis literal {idx} (the induction hypothesis)"
        | .branchTest =>
          IO.println s!"{pad}  ⮑ justified by the enclosing unresolved-if's test (assume-true-false branch)"
        | .segment =>
          IO.println s!"{pad}  ⮑ justified by the enclosing clausify-branch segment hypothesis (:CONTEXT-SUBST)"
        | .typeSetDerived =>
          IO.println s!"{pad}  ⮑ justified by a type-set verdict under the enclosing branch facts (type-set-derived)"
      if !children.isEmpty then
        printProofNodes children (indent + 1)

/-- Render a clause step's branch tree: literals (with their rewrite chains),
    clause-level steps (branch substitutions / rewrites), and nested case
    branches. -/
partial def printClauseItems (items : List ACL2.ClauseItem)
    (pad : String) (rwIndent : Nat) : IO Unit := do
  for item in items do
    match item with
    | .literal lp =>
      if lp.nodes.isEmpty then
        IO.println s!"{pad}  │    literal {lp.index}: {lp.literal} ⇒ {lp.result}"
      else
        IO.println s!"{pad}  │    literal {lp.index}: {lp.literal} ⇒ {lp.result}  ({lp.nodes.length}-step rewrite)"
        printProofNodes lp.nodes rwIndent
      for decision in lp.splitTrace do
        if let .leaf _ _ _ _ calls := decision then
          for call in calls do
            IO.println s!"{pad}  │      clausify call: {call.input} ⇒ {call.output}"
            IO.println s!"{pad}  │        query {call.query}, value {call.value}, path {repr call.path}"
            IO.println s!"{pad}  │        selected assumption: {call.basis}"
    | .step (.node rune lhs rhs children prov) =>
      IO.println s!"{pad}  │    {rune.ty}: {lhs} ⇒ {rhs}"
      if prov.clauseContextBasis.isSome then
        IO.println s!"{pad}  │      recorded clause-context/FC basis"
      -- A clause-level step (e.g. a termination conjecture's bare rewrite chain)
      -- can have adopted inner-rewrite children; render them too.
      if !children.isEmpty then printProofNodes children rwIndent
    | .clausify info =>
      IO.println s!"{pad}  │    clausify: {info.input}"
      IO.println s!"{pad}  │      ¬-clause: {info.negClause}"
      for (lit, cl) in info.splits do
        IO.println s!"{pad}  │      split {lit} ⇒ {cl}"
      IO.println s!"{pad}  │      out: {info.out}"
      if info.expanded then
        IO.println s!"{pad}  │      (expand-and-or fired — replay frontier)"
    | .fcDerivations derivs =>
      IO.println s!"{pad}  │    fc-derivations: {derivs.length} record(s)"
    | .complementClose lit =>
      IO.println s!"{pad}  │    complement-close: {lit}"
    | .dedupDrop lit =>
      IO.println s!"{pad}  │    dedup-drop: {lit}"
    | .linearEquation info =>
      IO.println s!"{pad}  │    linear equation insertion: {info.newLiteral}"
      IO.println s!"{pad}  │      parent clause: {info.parentClause}"
      IO.println s!"{pad}  │      input: {info.inputClause}"
      IO.println s!"{pad}  │      output: {info.outputClause}"
      IO.println s!"{pad}  │      numeric flags: {info.numericFlags}; assumptions: {info.assumptions}"
      IO.println s!"{pad}  │      polynomial pairs: {info.polyPairs}; runes: {repr info.runes}"
      if let some basis := info.polyTypeBasis then
        IO.println s!"{pad}  │      polynomial construction queries: {basis}"
    | .taSubst n f _ _ _ =>
      IO.println s!"{pad}  │    ta-subst: {f} ⇒ {n}"
    | .useHint hyps ccl appC lmis translated folds =>
      IO.println s!"{pad}  │    :use hint — {hyps.length} instantiated hyp(s):"
      for h in hyps do
        IO.println s!"{pad}  │      hyp: {h}"
      if let some ts := translated then
        for (raw, cooked) in lmis.zip ts do
          if raw != cooked then IO.println s!"{pad}  │      instance: {raw} ⇒ {cooked}"
      if let some groups := folds then
        for (group, i) in groups.zipIdx do
          for fold in group do
            IO.println s!"{pad}  │      instance {i + 1} fold {fold.path}: {fold.lhs} ⇒ {fold.rhs}"
      IO.println s!"{pad}  │      constraint-cl: {ccl}"
      IO.println s!"{pad}  │      application clauses: {appC}"
    | .branch segment subitems =>
      IO.println s!"{pad}  │    ┌ case branch: {segment}"
      printClauseItems subitems (pad ++ "    ") rwIndent

partial def printClauseNode (node : ACL2.ClauseNode) (indent : Nat) : IO Unit := do
  let pad := String.ofList (List.replicate indent ' ')
  -- The clause this node proves.
  let clauseStr := match node.inputClause with
    | [] => "(no clause recorded — synthesized)"
    | [lit] => s!"{lit}"
    | lits => "{" ++ String.intercalate " ∨ " (lits.map (s!"{·}")) ++ "}"
  IO.println s!"{pad}{node.idStr}:  {clauseStr}"
  -- The processors applied to this clause, in order.
  for st in node.steps do
    let res := match st.result with | .proved => "proved" | .subgoals => s!"{st.newClauses.length} subgoal(s)"
    let runeStr := if st.runes.isEmpty then "" else
      "  runes: " ++ String.intercalate ", " (st.runes.map (·.tag))
    IO.println s!"{pad}  ├─ {st.processor} ⇒ {res}{runeStr}"
    -- Processor-specific justification (fertilize target/bullet, eliminate-
    -- destructors elim sequence, generalize term→var map, …).
    for (k, v) in st.extraFields do
      IO.println s!"{pad}  │    {k}: {v}"
    -- Rewriter detail: the clause's branch tree (literals, clause-level steps,
    -- nested case branches).
    printClauseItems st.items pad (indent / 2 + 4)
    -- For processors with no branch tree (generalize, eliminate-destructors,
    -- fertilize, …), show the clauses they produced so the step isn't opaque.
    if st.result == ACL2.ProofResult.subgoals && st.items.isEmpty then
      for nc in st.newClauses do
        IO.println s!"{pad}  │    ⇒ {nc}"
  -- Induction applied here: the measure justification (what decreases, under which
  -- well-founded relation) and the per-case structure (tests + IH substitutions); the
  -- subgoals are the children below.
  if let some ind := node.induction then
    IO.println s!"{pad}  ╫ INDUCTION on {ind.term}  ({ind.subgoalCount} subgoals)"
    if ind.measure != .nil then
      let ctrlStr := String.intercalate ", " (ind.controllers.map (·.name))
      IO.println s!"{pad}      measure {ind.measure} decreases under {ind.mp}/{ind.rel}; on: {ctrlStr}"
    for c in ind.cases do
      let testsStr := String.intercalate " ∧ " (c.tests.map (·.toString))
      if c.alists.isEmpty then
        IO.println s!"{pad}      case [{testsStr}]: base (no IH)"
      else
        IO.println s!"{pad}      case [{testsStr}]:"
        for al in c.alists do
          let subst := String.intercalate ", " (al.map (fun (v, t) => s!"{v.name} := {t}"))
          IO.println s!"{pad}        IH: {subst}"
    for cl in ind.scheme do
      IO.println s!"{pad}      scheme clause: {cl}"
  -- Children (subgoal clauses).
  for c in node.children do
    printClauseNode c (indent + 4)

/-- Render a theorem/termination clause proof (its goal + clause-tree root). -/
def printClauseProof (cp : ACL2.ClauseProof) (indent : Nat) : IO Unit := do
  let pad := String.ofList (List.replicate indent ' ')
  -- The formula is the defthm statement for theorems; for termination proofs it
  -- is nil (the measure conjecture shows as the root clause below), so skip it.
  if cp.formula != .nil then IO.println s!"{pad}goal: {cp.formula}"
  match cp.root with
  | none => IO.println s!"{pad}(no logged proof — imported or trivial)"
  | some root => printClauseNode root (indent + 2)

/-- Render the whole development as one scoped proof tree: each world event in
    file order (definitions bind over the theorems that follow). -/
partial def printDevelopment : ACL2.Development → IO Unit
  | .done => pure ()
  | .bind event rest => do
    match event with
    | .encapsulateBegin sigs =>
      IO.println s!"\n── encapsulate begin (sigs: \
        {String.intercalate " " (sigs.map (·.name))}) ──"
    | .encapsulateEnd =>
      IO.println "── encapsulate end ──"
    | .groundZeroRecognizerTuples specs =>
      IO.println s!"── ground-zero recognizer tuples: {specs.length} ──"
    | .consTermGuards specs =>
      IO.println s!"── cons-term primitive guards: {specs.length} ──"
    | .includeBookEdge book parent =>
      IO.println s!"── include-book edge: {book} ←         {parent.getD "<top>"} ──"
    | .captureEnd _ =>
      IO.println "── capture end (complete) ──"
    | .constraints fns formulas =>
      IO.println s!"── constraints for \
        {String.intercalate " " (fns.map (·.name))}: \
        {formulas.length} formula(s) ──"
    | .defun name formals body just termination | .localDefun name formals body just termination =>
      let fs := String.intercalate " " (formals.map (·.name))
      let kind := match event with | .localDefun .. => "local helper" | _ => "def"
      IO.println s!"\n── {kind} {name} ({fs}) ──"
      IO.println s!"  body: {body}"
      if let some j := just then
        let ms := String.intercalate " " (j.measuredSubset.map (·.name))
        IO.println s!"  admission: measure {j.measure} under {j.wfRel.name}; measured: ({ms})"
        for c in j.terminationClauses do
          IO.println s!"    obligation: {c}"
      if let some t := termination then
        IO.println "  termination proof:"
        printClauseProof t 4
    | .groundZeroDefun name formals body just =>
      let fs := String.intercalate " " (formals.map (·.name))
      IO.println s!"\n── ground-zero def {name} ({fs}) ──"
      IO.println s!"  body: {body}"
      if let some j := just then
        let ms := String.intercalate " " (j.measuredSubset.map (·.name))
        IO.println s!"  admission: measure {j.measure} under {j.wfRel.name}; measured: ({ms})"
        for c in j.terminationClauses do
          IO.println s!"    obligation (recomputed): {c}"
    | .groundZeroRules specs =>
      IO.println s!"\n── ground-zero rules ──"
      for r in specs do
        let hs := String.intercalate " ∧ " (r.hyps.map (·.toString))
        let hyps := if r.hyps.isEmpty then "" else s!" (hyps: {hs})"
        let mf := r.matchFree.elim "" (fun v => s!" (match-free {v})")
        IO.println s!"  {r.name} [{r.equiv}]: {r.lhs} ⇒ {r.rhs}{hyps}{mf}"
    | .groundZeroFcRules specs =>
      IO.println s!"\n── ground-zero FC rules ──"
      for r in specs do
        let hs := String.intercalate " ∧ " (r.hyps.map (·.toString))
        let cs := String.intercalate " ∧ " (r.concls.map (·.toString))
        IO.println s!"  {r.name}: trigger {r.trigger}; hyps {hs} ⇒ concls {cs}"
    | .groundZeroLinearRules specs =>
      IO.println s!"\n── ground-zero LINEAR rules ──"
      for r in specs do
        let hs := String.intercalate " ∧ " (r.hyps.map (·.toString))
        IO.println s!"  {r.name}: hyps {hs} ⇒ {r.concl} (max-term {r.maxTerm})"
    | .typePrescription name cor _ _ _ =>
      IO.println s!"\n── type-prescription {name} ──"
      IO.println s!"  {cor}"
    | .rules specs =>
      IO.println s!"\n── stored rules ──"
      for r in specs do
        let hs := String.intercalate " ∧ " (r.hyps.map (·.toString))
        let hyps := if r.hyps.isEmpty then "" else s!" (hyps: {hs})"
        IO.println s!"  {r.name} [{r.equiv}]: {r.lhs} ⇒ {r.rhs}{hyps}"
    | .theorem proof =>
      IO.println s!"\n══ THEOREM {proof.name} ══"
      printClauseProof proof 2
    | .guardProof guard proof =>
      IO.println s!"\n── {guard.label}: recorded tree; replay UNSUPPORTED ──"
      for c in guard.clauses do IO.println s!"  obligation clause: {SExpr.ofList c}"
      printClauseProof proof 2
    | .redundantTheorem name formula _ =>
      IO.println s!"\n── redundant declaration {name} (no new proof) ──"
      IO.println s!"  {formula}"
    | .includedTheorem name formula cls =>
      IO.println s!"\n── included theorem {name} (certified in its own book) ──"
      IO.println s!"  {formula}"
      if let some c := cls then
        IO.println s!"  :CLASSES {c}"
    | .witnessDefun name formals body _ termination =>
      let fstr := String.intercalate " " (formals.map (·.name))
      IO.println s!"\n── witness defun {name} ({fstr}) — scoped canonical-model definition ──"
      IO.println s!"  {body}"
      if let some t := termination then
        IO.println s!"  (admission proof recorded: {t.name})"
    printDevelopment rest


end ACL2
