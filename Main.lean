import ACL2Lean

private def theoremMatches (needle : String) (name : ACL2.Symbol) : Bool :=
  name.normalizedName = needle.map Char.toLower

/-- Flatten events preserving locality: returns (event, isLocal) pairs. -/
private partial def flattenWithLocality (isLocal : Bool) : ACL2.Event → List (ACL2.Event × Bool)
  | .local inner => flattenWithLocality true inner
  | .mutualRecursion events => events.flatMap (flattenWithLocality isLocal)
  | .encapsulate events => events.flatMap (flattenWithLocality isLocal)
  | .makeEvent body =>
      let generated := ACL2.Event.generatedEvents body
      if generated.isEmpty then [(.makeEvent body, isLocal)]
      else generated.flatMap (flattenWithLocality isLocal)
  | event => [(event, isLocal)]

private def flattenListWithLocality (events : List ACL2.Event) : List (ACL2.Event × Bool) :=
  events.flatMap (flattenWithLocality false)

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

private def printTheoryEvents (events : List ACL2.Event) : IO Unit := do
  let theoryExprs : List ACL2.TheoryExpr :=
    ACL2.Event.flattenList events |>.filterMap fun
      | .inTheory expr => some (ACL2.TheoryExpr.ofSExpr expr)
      | _ => none
  if !List.isEmpty theoryExprs then
    IO.println "theory-events"
    for theoryExpr in theoryExprs do
      IO.println s!"  {theoryExpr.summary}"

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
          match ACL2.Evaluator.eval w {} sexpr with
          | .error e => IO.eprintln s!"Eval error: {e}"
          | .ok res => IO.println s!"{repr res}"
  | ["eval-in", path, exprStr] => do
      let events ← ACL2.loadEventsFromFile path
      match events with
      | .error e => IO.eprintln s!"Load error: {e}"
      | .ok evs =>
          let w := ACL2.World.replay evs
          match ACL2.Parse.parseSExpr exprStr.toList with
          | .error e => IO.eprintln s!"Parse error: {e}"
          | .ok (sexpr, _) =>
              match ACL2.Evaluator.eval w {} sexpr with
              | .error e => IO.eprintln s!"Eval error: {e}"
              | .ok res => IO.println s!"{repr res}"
  | ["gen-world", path] => do
      let events ← ACL2.loadEventsFromFile path
      match events with
      | .error e => IO.eprintln s!"Load error: {e}"
      | .ok evs =>
          let bookName := ACL2.WorldGen.bookNameFromPath path
          IO.println (ACL2.WorldGen.generateWorld bookName evs)
  | ["translate", path] => do
      let events ← ACL2.loadEventsFromFile path
      match events with
      | .error e => IO.eprintln s!"Load error: {e}"
      | .ok evs =>
          IO.println "import ACL2Lean.Logic"
          IO.println "import ACL2Lean.Lexorder"
          IO.println "import ACL2Lean.Count"
          IO.println "import ACL2Lean.TermOrder"
          IO.println "import ACL2Lean.Tactics"
          -- Emit include-book as Lean imports
          for ev in ACL2.Event.flattenList evs do
            match ev with
            | .includeBook bookPath _ =>
                -- Extract the base filename (after last /) and PascalCase it
                -- "perm" -> "Perm", "ordered-perms" -> "OrderedPerms"
                -- "sorting/perm" -> "Perm", "arithmetic-3/extra/top-ext" -> "TopExt"
                let baseBook := match bookPath.splitOn "/" with
                  | [] => bookPath
                  | parts => parts.getLast!
                let baseParts := baseBook.splitOn "-"
                let capitalized := baseParts.map fun p =>
                  if p.isEmpty then p
                  else String.ofList (p.toList.head!.toUpper :: p.toList.tail!)
                let moduleName := String.intercalate "" capitalized
                IO.println s!"import ACL2Lean.Translated.{moduleName}"
            | _ => pure ()
          IO.println "open ACL2 ACL2.Logic ACL2.Tactics"
          IO.println ""
          for (ev, isLocal) in flattenListWithLocality evs do
            let priv := if isLocal then "private " else ""
            match ev with
            | .defun name formals _ _ body =>
                let defStr := ACL2.Translator.translateDefun name formals body
                let defStr := if isLocal then defStr.replace "def " s!"{priv}def " else defStr
                IO.println defStr
                IO.println ""
            | .defthm name info =>
                let thmStr := ACL2.Translator.translateDefthm name info
                let thmStr := if isLocal then thmStr.replace "theorem " s!"{priv}theorem " else thmStr
                IO.println thmStr
                IO.println ""
            | .inTheory expr =>
                IO.println s!"/- ACL2 in-theory: {(ACL2.TheoryExpr.ofSExpr expr).summary} -/"
                IO.println ""
            | _ => pure ()
  | ["metadata", path] => do
      let events ← ACL2.loadEventsFromFile path
      match events with
      | .error e => IO.eprintln s!"Load error: {e}"
      | .ok evs => do
          printTheoryEvents evs
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
            | .defthm name =>
                IO.println s!"\n  DEFTHM {name}"
            | .induction i =>
                IO.println s!"  INDUCTION {repr i.term} → {i.subgoalCount} subgoals"
            | .qed =>
                IO.println "  QED"
      | .error e => IO.eprintln s!"Parse error: {e}"
  | ["translate", path, "--proof-log", proofLogPath] => do
      let events ← ACL2.loadEventsFromFile path
      let proofContents ← IO.FS.readFile proofLogPath
      match events, ACL2.ProofLog.parse proofContents with
      | .error e, _ => IO.eprintln s!"Load error: {e}"
      | _, .error e => IO.eprintln s!"Proof log parse error: {e}"
      | .ok evs, .ok log =>
          let segments := ACL2.ProofLog.splitByTheorem log
          -- Build a map from lowercase theorem name to tactic script
          let proofMap := segments.foldl (init := ([] : List (String × String))) fun acc (name, seg) =>
            match ACL2.ProofLog.generateTacticScript seg with
            | some script => acc ++ [(name.map Char.toLower, script)]
            | none => acc
          IO.println "import ACL2Lean.Logic"
          IO.println "import ACL2Lean.Lexorder"
          IO.println "import ACL2Lean.Count"
          IO.println "import ACL2Lean.TermOrder"
          IO.println "import ACL2Lean.Tactics"
          for ev in ACL2.Event.flattenList evs do
            match ev with
            | .includeBook bookPath _ =>
                let baseBook := match bookPath.splitOn "/" with
                  | [] => bookPath
                  | parts => parts.getLast!
                let baseParts := baseBook.splitOn "-"
                let capitalized := baseParts.map fun p =>
                  if p.isEmpty then p
                  else String.ofList (p.toList.head!.toUpper :: p.toList.tail!)
                let moduleName := String.intercalate "" capitalized
                IO.println s!"import ACL2Lean.Translated.{moduleName}"
            | _ => pure ()
          IO.println "open ACL2 ACL2.Logic ACL2.Tactics"
          IO.println ""
          for (ev, isLocal) in flattenListWithLocality evs do
            let priv := if isLocal then "private " else ""
            match ev with
            | .defun name formals _ _ body =>
                let defStr := ACL2.Translator.translateDefun name formals body
                let defStr := if isLocal then defStr.replace "def " s!"{priv}def " else defStr
                IO.println defStr
                IO.println ""
            | .defthm name info =>
                let nameKey := name.normalizedName
                let proofScript := (proofMap.find? fun (k, _) => k == nameKey).map Prod.snd
                let thmStr := ACL2.Translator.translateDefthm name info proofScript
                let thmStr := if isLocal then thmStr.replace "theorem " s!"{priv}theorem " else thmStr
                IO.println thmStr
                IO.println ""
            | .inTheory expr =>
                IO.println s!"/- ACL2 in-theory: {(ACL2.TheoryExpr.ofSExpr expr).summary} -/"
                IO.println ""
            | _ => pure ()
  | ["generate-tactics", proofLogPath] => do
      let contents ← IO.FS.readFile proofLogPath
      match ACL2.ProofLog.parse contents with
      | .ok log =>
          let segments := ACL2.ProofLog.splitByTheorem log
          IO.println s!"Found {segments.length} theorem proof(s)"
          for (name, seg) in segments do
            IO.println s!"\n=== {name} ({seg.length} events) ==="
            match ACL2.ProofLog.generateTacticScript seg with
            | some script => IO.println script
            | none => IO.println "(no proof needed)"
      | .error e => IO.eprintln s!"Parse error: {e}"
  | _ => do
      IO.println "Usage:"
      IO.println "  acl2lean report"
      IO.println "  acl2lean eval \"(expr)\""
      IO.println "  acl2lean metadata file.lisp [theorem]"
      IO.println "  acl2lean gen-world file.lisp"
      IO.println "  acl2lean translate file.lisp"
      IO.println "  acl2lean parse-proof-log file.proof-log"
