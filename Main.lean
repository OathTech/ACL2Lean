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
      if let some src := prov.equivSource then
        match src with
        | .literal idx =>
          IO.println s!"{pad}  ⮑ justified by hypothesis literal {idx} (the induction hypothesis)"
        | .branchTest =>
          IO.println s!"{pad}  ⮑ justified by the enclosing unresolved-if's test (assume-true-false branch)"
        | .segment =>
          IO.println s!"{pad}  ⮑ justified by the enclosing clausify-branch segment hypothesis (:CONTEXT-SUBST)"
      if !children.isEmpty then
        printProofNodes children (indent + 1)

/-- Render a clause step's branch tree: literals (with their rewrite chains),
    clause-level steps (branch substitutions / rewrites), and nested case
    branches. -/
private partial def printClauseItems (items : List ACL2.ClauseItem)
    (pad : String) (rwIndent : Nat) : IO Unit := do
  for item in items do
    match item with
    | .literal lp =>
      if lp.nodes.isEmpty then
        IO.println s!"{pad}  │    literal {lp.index}: {lp.literal} ⇒ {lp.result}"
      else
        IO.println s!"{pad}  │    literal {lp.index}: {lp.literal} ⇒ {lp.result}  ({lp.nodes.length}-step rewrite)"
        printProofNodes lp.nodes rwIndent
    | .step (.node rune lhs rhs children _) =>
      IO.println s!"{pad}  │    {rune.1}: {lhs} ⇒ {rhs}"
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
    | .branch segment subitems =>
      IO.println s!"{pad}  │    ┌ case branch: {segment}"
      printClauseItems subitems (pad ++ "    ") rwIndent

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
private def printClauseProof (cp : ACL2.ClauseProof) (indent : Nat) : IO Unit := do
  let pad := String.ofList (List.replicate indent ' ')
  -- The formula is the defthm statement for theorems; for termination proofs it
  -- is nil (the measure conjecture shows as the root clause below), so skip it.
  if cp.formula != .nil then IO.println s!"{pad}goal: {cp.formula}"
  match cp.root with
  | none => IO.println s!"{pad}(no logged proof — imported or trivial)"
  | some root => printClauseNode root (indent + 2)

/-- Render the whole development as one scoped proof tree: each world event in
    file order (definitions bind over the theorems that follow). -/
private partial def printDevelopment : ACL2.Development → IO Unit
  | .done => pure ()
  | .bind event rest => do
    match event with
    | .defun name formals body just termination =>
      let fs := String.intercalate " " (formals.map (·.name))
      IO.println s!"\n── def {name} ({fs}) ──"
      IO.println s!"  body: {body}"
      if let some j := just then
        let ms := String.intercalate " " (j.measuredSubset.map (·.name))
        IO.println s!"  admission: measure {j.measure} under {j.wfRel.name}; measured: ({ms})"
        for c in j.terminationClauses do
          IO.println s!"    obligation: {c}"
      if let some t := termination then
        IO.println "  termination proof:"
        printClauseProof t 4
    | .typePrescription name cor _ _ =>
      IO.println s!"\n── type-prescription {name} ──"
      IO.println s!"  {cor}"
    | .theorem proof =>
      IO.println s!"\n══ THEOREM {proof.name} ══"
      printClauseProof proof 2
    printDevelopment rest

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
            | .defun name formals body just =>
                let formalStr := String.intercalate " " (formals.map (·.name))
                IO.println s!"\n  DEFUN {name} ({formalStr}) = {body}"
                if let some j := just then
                  IO.println s!"    admission: measure {j.measure} under {j.wfRel.name}"
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
      | .error e => throw (IO.userError s!"Parse error: {e}")
      | .ok log =>
          match ACL2.ClauseTree.buildDevelopment log with
          -- Exit non-zero so callers/CI detect the failure (a failed/truncated
          -- ACL2 proof must not look like a clean run).
          | .error e => throw (IO.userError s!"Reconstruction error: {e}")
          | .ok dev => printDevelopment dev
  | _ => do
      IO.println "Usage:"
      IO.println "  acl2lean report"
      IO.println "  acl2lean eval \"(expr)\""
      IO.println "  acl2lean eval-in file.lisp \"(expr)\""
      IO.println "  acl2lean gen-world file.lisp"
      IO.println "  acl2lean metadata file.lisp [theorem]"
      IO.println "  acl2lean parse-proof-log file.proof-log"
      IO.println "  acl2lean dump-proof-tree file.proof-log"
