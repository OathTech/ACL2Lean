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
            | .defthm name =>
                IO.println s!"\n  DEFTHM {name}"
            | .induction i =>
                IO.println s!"  INDUCTION {repr i.term} → {i.subgoalCount} subgoals"
            | .qed =>
                IO.println "  QED"
      | .error e => IO.eprintln s!"Parse error: {e}"
  | _ => do
      IO.println "Usage:"
      IO.println "  acl2lean report"
      IO.println "  acl2lean eval \"(expr)\""
      IO.println "  acl2lean eval-in file.lisp \"(expr)\""
      IO.println "  acl2lean gen-world file.lisp"
      IO.println "  acl2lean metadata file.lisp [theorem]"
      IO.println "  acl2lean parse-proof-log file.proof-log"
