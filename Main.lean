import ACL2Lean

private def theoremMatches (needle : String) (name : ACL2.Symbol) : Bool :=
  name.normalizedName = needle.map Char.toLower

private def printTheoremMetadata (name : ACL2.Symbol) (info : ACL2.TheoremInfo) : IO Unit := do
  IO.println s!"theorem {repr name}"
  let ruleClasses := info.ruleClasses.map ACL2.RuleClass.summary
  if ruleClasses.isEmpty then
    IO.println "  rule-classes: none"
  else
    IO.println s!"  rule-classes: {String.intercalate ", " ruleClasses}"
  let hints := info.hintGoals
  if hints.isEmpty then
    IO.println "  hints: none"
  else
    for hint in hints do
      IO.println s!"  {hint.summary}"
  let instructions := info.instructions
  if !instructions.isEmpty then
    IO.println "  instructions:"
    for instruction in instructions do
      for line in ACL2.ProofInstruction.renderLines 4 instruction do
        IO.println line
  let extraKeys := info.extraOptions.map (fun option => s!":{option.key}")
  if !extraKeys.isEmpty then
    IO.println s!"  other-options: {String.intercalate ", " extraKeys}"

private partial def printProofNodes (nodes : List ACL2.ProofNode) (indent : Nat) : IO Unit := do
  for node in nodes do
    match node with
    | .node rune lhs rhs children prov =>
      let pad := String.ofList (List.replicate (indent * 2) ' ')
      let originStr := if prov.origin.isEmpty then "" else s!" [{prov.origin}]"
      IO.println s!"{pad}{rune.1}:{rune.2}{originStr}"
      IO.println s!"{pad}  {lhs} => {rhs}"
      if !prov.runes.isEmpty then
        let runeStrs := prov.runes.map fun (t, n) => s!"{t}:{n}"
        IO.println s!"{pad}  runes: {String.intercalate ", " runeStrs}"
      if !prov.subst.isEmpty then
        let substStrs := prov.subst.map fun (k, v) => s!"{k} → {v}"
        IO.println s!"{pad}  subst: {String.intercalate ", " substStrs}"
      if let some eq := prov.equivTerm then
        IO.println s!"{pad}  equiv: {eq}"
      if !children.isEmpty then
        printProofNodes children (indent + 1)

/-- Render one node of the reconstructed clause tree (and its subtree). -/
private partial def printClauseNode (node : ACL2.ClauseNode) (indent : Nat) : IO Unit := do
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
      "  runes: " ++ String.intercalate ", " (st.runes.map fun (t, n) => s!"{t}:{n}")
    IO.println s!"{pad}  ├─ {st.processor} ⇒ {res}{runeStr}"
    -- Rewriter detail (SIMPLIFY only): per-literal rewrite chains.
    for lp in st.literalProofs do
      if !lp.nodes.isEmpty then
        IO.println s!"{pad}  │    literal {lp.index}: {lp.literal} ⇒ {lp.result}  ({lp.nodes.length}-step rewrite)"
        printProofNodes lp.nodes (indent / 2 + 4)
    -- For processors with no rewriter trace (generalize, eliminate-destructors,
    -- fertilize, …), show the clauses they produced so the step isn't opaque.
    if st.result == ACL2.ProofResult.subgoals && st.literalProofs.all (·.nodes.isEmpty) then
      for nc in st.newClauses do
        IO.println s!"{pad}  │    ⇒ {nc}"
  -- Induction applied here: its scheme (the generated case clauses); the
  -- subgoals are the children below.
  if let some ind := node.induction then
    IO.println s!"{pad}  ╫ INDUCTION on {ind.term}  ({ind.subgoalCount} subgoals)"
    for cl in ind.scheme do
      IO.println s!"{pad}      scheme case: {cl}"
  -- Children (subgoal clauses).
  for c in node.children do
    printClauseNode c (indent + 4)

def main (args : List String) : IO Unit := do
  match args with
  | ["report"] => do
      IO.println "ACL2 to Lean 4 Bridge - Corpus Report"
      ACL2.reportSamples
  | ["eval", exprStr] => do
      match ACL2.Parse.parseSExpr exprStr.toList with
      | .error e => IO.eprintln s!"Parse error: {e}"
      | .ok (sexpr, _) =>
          let w := ACL2.World.empty
          let fuel := 100000
          match ACL2.evalOpt fuel w {} sexpr with
          | none => IO.eprintln "Eval: fuel exhaustion (try a larger fuel)"
          | some res => IO.println s!"{repr res}"
  | ["eval-in", path, exprStr] => do
      let events ← ACL2.loadEventsFromFile path
      match events with
      | .error e => IO.eprintln s!"Load error: {e}"
      | .ok evs =>
          let w := ACL2.World.replay evs
          match ACL2.Parse.parseSExpr exprStr.toList with
          | .error e => IO.eprintln s!"Parse error: {e}"
          | .ok (sexpr, _) =>
              let fuel := 100000
              match ACL2.evalOpt fuel w {} sexpr with
              | none => IO.eprintln "Eval: fuel exhaustion (try a larger fuel)"
              | some res => IO.println s!"{repr res}"
  | ["gen-world", path] => do
      let events ← ACL2.loadEventsFromFile path
      match events with
      | .error e => IO.eprintln s!"Load error: {e}"
      | .ok evs =>
          let bookName := ACL2.WorldGen.bookNameFromPath path
          IO.println (ACL2.WorldGen.generateWorld bookName evs)
  | ["metadata", path] => do
      let events ← ACL2.loadEventsFromFile path
      match events with
      | .error e => IO.eprintln s!"Load error: {e}"
      | .ok evs => do
          for ev in ACL2.Event.flattenList evs do
            match ev with
            | .defthm name info =>
                printTheoremMetadata name info
            | _ => pure ()
  | ["metadata", path, theoremName] => do
      let events ← ACL2.loadEventsFromFile path
      match events with
      | .error e => IO.eprintln s!"Load error: {e}"
      | .ok evs =>
          let flat := ACL2.Event.flattenList evs
          match flat.find? (fun
            | .defthm name _ => theoremMatches theoremName name
            | _ => false) with
          | some ev =>
              match ev with
              | .defthm name info => printTheoremMetadata name info
              | _ => IO.eprintln s!"No theorem named {theoremName} in {path}"
          | _ => IO.eprintln s!"No theorem named {theoremName} in {path}"
  | ["parse-proof-log", path] => do
      let contents ← IO.FS.readFile path
      match ACL2.ProofLog.parse contents with
      | .ok log =>
          IO.println (log.summary)
          IO.println ""
          for event in log.events do
            match event with
            | .step s =>
                IO.println s!"  STEP {s.clauseId} [{s.processor}] → {repr s.result}"
                if !s.runes.isEmpty then
                  let runeStrs := s.runes.map fun (t, n) => s!"(:{t} {n})"
                  IO.println s!"    runes: {String.intercalate " " runeStrs}"
                let rwSteps := s.rewriteSteps
                if !rwSteps.isEmpty then
                  IO.println s!"    rewrites: {rwSteps.length} steps"
                  for rw in rwSteps do
                    IO.println s!"      {rw.rune.1}:{rw.rune.2}"
            | .defun name formals body =>
                let formalStr := String.intercalate " " (formals.map (·.name))
                IO.println s!"\n  DEFUN {name} ({formalStr}) = {body}"
            | .defthm name formula source =>
                let srcStr := match source with
                  | .local => " [local]"
                  | .includeBook => " [include-book]"
                  | .unknown => ""
                IO.println s!"\n  DEFTHM {name}{srcStr}: {formula}"
            | .typePrescription name corollary basicTs leaves =>
                IO.println s!"\n  TYPE-PRESCRIPTION {name}: {corollary} (basicts={basicTs}, {leaves.length} leaves)"
            | .induction i =>
                IO.println s!"  INDUCTION {repr i.term} → {i.subgoalCount} subgoals"
            | .qed =>
                IO.println "  QED"
      | .error e => IO.eprintln s!"Parse error: {e}"
  | ["dump-proof-tree", path] => do
      let contents ← IO.FS.readFile path
      match ACL2.ProofLog.parse contents with
      | .error e => IO.eprintln s!"Parse error: {e}"
      | .ok log =>
          let proofs := ACL2.buildAllTheoremProofs log
          if proofs.isEmpty then
            IO.eprintln "No theorems found in proof log"
          else
            for proof in proofs do
              IO.println s!"\n══ THEOREM {proof.name} ══"
              IO.println s!"  goal: {proof.formula}"
              -- The TOP-LEVEL structure of the proof is the induction; the
              -- subgoals below are its cases. (A literal's node list is a local
              -- rewrite chain, NOT the proof's top level.)
              match proof.induction with
              | some ind =>
                IO.println s!"  proved by INDUCTION on {ind.term}  ({ind.subgoalCount} cases → subgoals below)"
                IO.println "    induction scheme (each case is a clause):"
                let mut ci := 0
                for clause in ind.scheme do
                  match clause.toList? with
                  | some lits =>
                    IO.println s!"      case {ci}:"
                    for lit in lits do
                      IO.println s!"        {lit}"
                  | none =>
                    IO.println s!"      case {ci}: {clause}"
                  ci := ci + 1
              | none =>
                IO.println "  (no induction — direct proof)"
              for c in proof.cases do
                IO.println s!"\n  {c.clauseId}   (one case of the induction above)"
                IO.println s!"    clause = disjunction of {c.clause.length} literals:"
                let mut li := 0
                for lit in c.clause do
                  IO.println s!"      [{li}] {lit}"
                  li := li + 1
                for lp in c.literalProofs do
                  if lp.nodes.isEmpty then
                    IO.println s!"    literal {lp.index} [carried, no rewrite]: {lp.literal}"
                  else
                    IO.println s!"    literal {lp.index} [rewritten ⇒ {lp.result}]:"
                    IO.println s!"      {lp.literal}"
                    IO.println s!"      rewrite chain ({lp.nodes.length} steps):"
                    printProofNodes lp.nodes 4
  | ["dump-clause-tree", path] => do
      let contents ← IO.FS.readFile path
      match ACL2.ProofLog.parse contents with
      | .error e => IO.eprintln s!"Parse error: {e}"
      | .ok log =>
          match ACL2.ClauseTree.buildClauseProofs log with
          | .error e => IO.eprintln s!"Reconstruction error: {e}"
          | .ok proofs =>
            if proofs.isEmpty then
              IO.eprintln "No theorems found in proof log"
            else
              for proof in proofs do
                IO.println s!"\n══ THEOREM {proof.name} ══"
                IO.println s!"  goal: {proof.formula}"
                match proof.root with
                | none => IO.println "  (no logged proof — imported or trivial)"
                | some root => printClauseNode root 2
  | "check-proof" :: logPath :: depPaths => do
      -- Load dependency proof logs first to build cumulative world/formulas
      let mut world : ACL2.World := { defs := {} }
      let mut formulas : Std.HashMap String ACL2.SExpr := ACL2.ProofChecker.builtinAxioms
      for depPath in depPaths do
        let depContents ← IO.FS.readFile depPath
        match ACL2.ProofLog.parse depContents with
        | .error e => IO.eprintln s!"Parse error in dep {depPath}: {e}"
        | .ok depLog =>
            world := ACL2.ProofChecker.buildWorldFromLog depLog world
            formulas := ACL2.ProofChecker.buildFormulaMap depLog formulas
      -- Load and check the target proof log
      let contents ← IO.FS.readFile logPath
      match ACL2.ProofLog.parse contents with
      | .error e => IO.eprintln s!"Parse error: {e}"
      | .ok log =>
          world := ACL2.ProofChecker.buildWorldFromLog log world
          formulas := ACL2.ProofChecker.buildFormulaMap log formulas
          let tpProofs := ACL2.ProofChecker.buildTypePrescriptionMap log
          let proofs := ACL2.buildAllTheoremProofs log
          IO.println s!"Checking {logPath} ({proofs.length} theorems, {formulas.size} formulas)"
          IO.println "  ⚠ HEURISTIC Boolean checker — NOT kernel-verified. A ✓ here certifies"
          IO.println "    NOTHING in the Lean kernel (no proof term, no soundness theorem)."
          let mut passed := 0
          let mut failed := 0
          for proof in proofs do
            if proof.cases.isEmpty then
              -- ⚠ counts a case-less theorem as passed WITHOUT any check.
              passed := passed + 1
            else
              let ctx : ACL2.ProofChecker.CheckerContext := {
                world, theoremFormulas := formulas
                typePrescriptions := tpProofs
                clause := [], currentLiteralIndex := 0
              }
              if ACL2.ProofChecker.checkTheoremProof ctx proof then
                IO.println s!"  ✓ {proof.name}"
                passed := passed + 1
              else
                IO.println s!"  ✗ {proof.name}"
                -- Debug: check each case
                for cp in proof.cases do
                  IO.println s!"    Case {cp.clauseId}: {cp.literalProofs.length} literals"
                  for lp in cp.literalProofs do
                    let ctx' := { ctx with clause := cp.clause, currentLiteralIndex := lp.index }
                    let nodesOk := lp.nodes.all (ACL2.ProofChecker.checkNode ctx')
                    let resultOk := ACL2.ProofChecker.isQuotedT lp.result ||
                                    ACL2.ProofChecker.isEqualSelf lp.result ||
                                    lp.result == lp.literal
                    IO.println s!"      Lit {lp.index}: nodes={nodesOk} result={resultOk} ({lp.nodes.length} nodes)"
                    if !nodesOk then
                      for node in lp.nodes do
                        match node with
                        | .node (rt, rn) _ _ children _ =>
                          let ok := ACL2.ProofChecker.checkNode ctx' node
                          if !ok then
                            IO.println s!"        FAIL: {rt}:{rn} (children={children.length})"
                            for child in children do
                              match child with
                              | .node (ct, cn) _ _ _ _ =>
                                let cok := ACL2.ProofChecker.checkNode ctx' child
                                if !cok then
                                  IO.println s!"          CHILD FAIL: {ct}:{cn}"
                                  match child with
                                  | .node _ _ _ grandchildren _ =>
                                    for gc in grandchildren do
                                      match gc with
                                      | .node (gt, gn) _ _ _ _ =>
                                        let gok := ACL2.ProofChecker.checkNode ctx' gc
                                        if !gok then
                                          IO.println s!"            GRANDCHILD FAIL: {gt}:{gn}"
                failed := failed + 1
          IO.println s!"Result: {passed} passed, {failed} failed"
  | _ => do
      IO.println "Usage:"
      IO.println "  acl2lean report"
      IO.println "  acl2lean eval \"(expr)\""
      IO.println "  acl2lean eval-in file.lisp \"(expr)\""
      IO.println "  acl2lean gen-world file.lisp"
      IO.println "  acl2lean metadata file.lisp [theorem]"
      IO.println "  acl2lean parse-proof-log file.proof-log"
      IO.println "  acl2lean dump-proof-tree file.proof-log"
      IO.println "  acl2lean check-proof file.proof-log [dep1.proof-log ...]"
