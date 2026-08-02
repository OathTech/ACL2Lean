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

/-- Evaluate a STREAM of s-expression forms against a fixed world, printing one
    value per form — the same "forms in → values out" interface ACL2 presents
    when you pipe forms to its stdin. This is what makes the Lean interpreter
    differentially comparable to ACL2 as a peer: feed both the same corpus of
    forms, diff the two value streams. Each form's value is printed on its own
    line (a form that fails to converge prints `<stuck>`), so line N of the
    output corresponds to form N of the input. NOTE: this is a plain
    interpreter capability (batch evaluation) — it carries NO test/expectation
    logic; comparison lives entirely in the external differential manager. -/
private def evalFormStream (w : ACL2.World) (input : String) : IO Unit := do
  match ACL2.Parse.parseAll input with
  | .error e => throw (IO.userError s!"Parse error: {e}")
  | .ok forms =>
      let fuel := 100000
      for form in forms do
        match ACL2.evalOpt fuel w {} form with
        | none => IO.println "<stuck>"
        | some res => IO.println s!"{repr res}"

def main (args : List String) : IO Unit := do
  match args with
  | ["report"] => do
      IO.println "ACL2 to Lean 4 Bridge - Corpus Report"
      ACL2.reportSamples
  | ["eval"] => do
      -- Stream mode: forms from stdin → one value per form (empty world).
      -- Same interface as `acl2 < forms.lisp`; the peer for differential testing.
      let input ← IO.FS.Stream.readToEnd (← IO.getStdin)
      evalFormStream ACL2.World.empty input
  | ["eval", exprStr] => do
      match ACL2.Parse.parseSExpr exprStr.toList with
      | .error e => IO.eprintln s!"Parse error: {e}"
      | .ok (sexpr, _) =>
          let w := ACL2.World.empty
          let fuel := 100000
          match ACL2.evalOpt fuel w {} sexpr with
          | none => IO.eprintln "Eval: fuel exhaustion (try a larger fuel)"
          | some res => IO.println s!"{repr res}"
  | ["eval-in", path] => do
      -- Stream mode against the world loaded from `path`: forms from stdin →
      -- one value per form. Peer to `acl2 < (book then forms)`.
      let events ← ACL2.loadEventsFromFile path
      match events with
      | .error e => throw (IO.userError s!"Load error: {e}")
      | .ok evs =>
          let w := ACL2.World.replay evs
          let input ← IO.FS.Stream.readToEnd (← IO.getStdin)
          evalFormStream w input
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
          match ACL2.WorldGen.generateWorld bookName evs with
          | .error e => throw (IO.userError e)
          | .ok src => IO.println src
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
            | .encapsulateBegin sigs =>
                IO.println s!"  ENCAPSULATE-BEGIN sigs: \
                  {String.intercalate " " (sigs.map (·.name))}"
            | .encapsulateEnd =>
                IO.println "  ENCAPSULATE-END"
            | .constraints fns formulas =>
                IO.println s!"  CONSTRAINTS for \
                  {String.intercalate " " (fns.map (·.name))}: \
                  {formulas.length} formula(s)"
            | .step s =>
                IO.println s!"  STEP {s.clauseId} [{s.processor}] → {repr s.result}"
                if !s.runes.isEmpty then
                  let runeStrs := s.runes.map fun r => match r.idx with
                    | none => s!"(:{r.ty} {r.name})"
                    | some k => s!"(:{r.ty} {r.name} . {k})"
                  IO.println s!"    runes: {String.intercalate " " runeStrs}"
                let rwSteps := s.rewriteSteps
                if !rwSteps.isEmpty then
                  IO.println s!"    rewrites: {rwSteps.length} steps"
                  for rw in rwSteps do
                    let idxSuffix := match rw.rune.idx with
                      | none => ""
                      | some k => s!" . {k}"
                    IO.println s!"      {rw.rune.ty}:{rw.rune.name}{idxSuffix}"
            | .defun name formals body just =>
                let formalStr := String.intercalate " " (formals.map (·.name))
                IO.println s!"\n  DEFUN {name} ({formalStr}) = {body}"
                if let some j := just then
                  IO.println s!"    admission: measure {j.measure} under {j.wfRel.name}"
            | .defthm name formula source _ =>
                let srcStr := match source with
                  | .local => " [local]"
                  | .includeBook => " [include-book]"
                  | .unknown => ""
                IO.println s!"\n  DEFTHM {name}{srcStr}: {formula}"
            | .typePrescription name corollary basicTs leaves =>
                IO.println s!"\n  TYPE-PRESCRIPTION {name}: {corollary} (basicts={basicTs}, {leaves.length} leaves)"
            | .poolConsider name =>
                IO.println s!"  POOL-CONSIDER *{String.intercalate "." (name.map toString)}"
            | .poolSubsumed name byName =>
                IO.println s!"  POOL-SUBSUMED *{String.intercalate "." (name.map toString)} by *{String.intercalate "." (byName.map toString)}"
            | .rules specs =>
                IO.println s!"\n  RULES ({specs.length} stored):"
                for r in specs do
                  IO.println s!"    {r.name} [{r.equiv}]: {r.lhs} ⇒ {r.rhs} (hyps: {r.hyps.length})"
            | .groundZeroDefun name formals body just =>
                let formalStr := String.intercalate " " (formals.map (·.name))
                IO.println s!"\n  GROUND-ZERO DEFUN {name} ({formalStr}) = {body}"
                if let some j := just then
                  IO.println s!"    admission (recomputed): measure {j.measure} under {j.wfRel.name}"
            | .groundZeroRules specs =>
                IO.println s!"\n  GROUND-ZERO-RULES ({specs.length} snapshot):"
                for r in specs do
                  let mf := r.matchFree.elim "" (fun v => s!" match-free {v}")
                  IO.println s!"    {r.name} [{r.equiv}]: {r.lhs} ⇒ {r.rhs} (hyps: {r.hyps.length}){mf}"
            | .groundZeroFcRules specs =>
                IO.println s!"\n  GROUND-ZERO-FC-RULES ({specs.length} snapshot):"
                for r in specs do
                  IO.println s!"    {r.name}: trigger {r.trigger} ({r.hyps.length} hyps, {r.concls.length} concls)"
            | .groundZeroLinearRules specs =>
                IO.println s!"\n  GROUND-ZERO-LINEAR-RULES ({specs.length} snapshot):"
                for r in specs do
                  IO.println s!"    {r.name}: {r.hyps.length} hyps ⇒ {r.concl} (max-term {r.maxTerm})"
            | .induction i =>
                IO.println s!"  INDUCTION {repr i.term} → {i.subgoalCount} subgoals"
            | .qed =>
                IO.println "  QED"
      | .error e => IO.eprintln s!"Parse error: {e}"
  | ["dump-proof-tree", path] => do
      let contents ← IO.FS.readFile path
      match ACL2.ProofLog.parse contents with
      | .error e => throw (IO.userError s!"Parse error: {e}")
      | .ok log =>
          match ACL2.ClauseTree.buildDevelopment log with
          -- Exit non-zero so callers/CI detect the failure (a failed/truncated
          -- ACL2 proof must not look like a clean run).
          | .error e => throw (IO.userError s!"Reconstruction error: {e}")
          | .ok dev => ACL2.printDevelopment dev
  | _ => do
      IO.println "Usage:"
      IO.println "  acl2lean report"
      IO.println "  acl2lean eval \"(expr)\"            # evaluate one form"
      IO.println "  acl2lean eval                     # forms from stdin → one value/form (ACL2-peer stream)"
      IO.println "  acl2lean eval-in file.lisp \"(expr)\"  # one form against a book's world"
      IO.println "  acl2lean eval-in file.lisp        # forms from stdin against a book's world"
      IO.println "  acl2lean gen-world file.lisp"
      IO.println "  acl2lean metadata file.lisp [theorem]"
      IO.println "  acl2lean parse-proof-log file.proof-log"
      IO.println "  acl2lean dump-proof-tree file.proof-log"
