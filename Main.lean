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
      let pad := String.mk (List.replicate (indent * 2) ' ')
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
              IO.println s!"\n══ {proof.name} ══"
              if let some ind := proof.induction then
                IO.println s!"  Induction on {ind.term} → {ind.subgoalCount} subgoals"
                IO.println "  Scheme:"
                let mut ci := 0
                for clause in ind.scheme do
                  match clause.toList? with
                  | some lits =>
                    IO.println s!"    Case {ci}:"
                    for lit in lits do
                      IO.println s!"      {lit}"
                  | none =>
                    IO.println s!"    Case {ci}: {clause}"
                  ci := ci + 1
              for c in proof.cases do
                IO.println s!"\n  ── {c.clauseId} ──"
                IO.println s!"  Clause ({c.clause.length} literals):"
                let mut li := 0
                for lit in c.clause do
                  IO.println s!"    [{li}] {lit}"
                  li := li + 1
                for lp in c.literalProofs do
                  IO.println s!"\n  Literal {lp.index} (notFlg={lp.notFlg}):"
                  IO.println s!"    Input:  {lp.literal}"
                  IO.println s!"    Result: {lp.result}"
                  if lp.nodes.isEmpty then
                    IO.println "    (no rewrites)"
                  else
                    IO.println s!"    Proof tree ({lp.nodes.length} top-level nodes):"
                    printProofNodes lp.nodes 3
  | "check-proof" :: logPath :: srcPaths => do
      let contents ← IO.FS.readFile logPath
      match ACL2.ProofLog.parse contents with
      | .error e => IO.eprintln s!"Parse error: {e}"
      | .ok log =>
          -- Build world from DEFUN events in the proof log (these
          -- contain macro-expanded, normalized bodies from ACL2).
          let mut world := ACL2.ProofChecker.buildWorldFromLog log
          -- Optionally extend with source files (for definitions not
          -- in the proof log, e.g., from included books without DEFUN events).
          for srcPath in srcPaths do
            let events ← ACL2.loadEventsFromFile srcPath
            match events with
            | .error e => IO.eprintln s!"Load error for {srcPath}: {e}"
            | .ok evs => world := world.extend evs
          do
            let formulas := ACL2.ProofChecker.buildFormulaMap log
            let proofs := ACL2.buildAllTheoremProofs log
            IO.println s!"Checking {logPath} ({proofs.length} theorems, {formulas.size} formulas)"
            let mut passed := 0
            let mut failed := 0
            for proof in proofs do
              if proof.cases.isEmpty then
                passed := passed + 1
              else
                let ctx : ACL2.ProofChecker.CheckerContext := {
                  world, theoremFormulas := formulas
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
