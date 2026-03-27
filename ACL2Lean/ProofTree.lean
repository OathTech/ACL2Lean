/-
  Proof tree types and parser.

  Converts ACL2's flat proof trace (a list of TraceEvents) into a
  structured proof tree. The tree represents ACL2's proof at three
  levels: theorem → induction cases → literal simplifications.

  Each rewrite step is enriched with its IF branch decisions, turning
  the flat interleaving of IF-TEST and REWRITE-STEP events into
  per-step justifications.
-/
import ACL2Lean.Syntax
import ACL2Lean.ProofLog

namespace ACL2

/-! ## Proof tree types -/

/-- Why an IF branch decision was made. -/
inductive BranchJustification where
  | clauseAssumption   -- test's truth follows from a negated clause literal
  | typeSet            -- test's truth follows from type reasoning
  | rewrittenConstant  -- test rewrote to a constant ('T or 'NIL)
  | unknown            -- justification not captured
  deriving Repr, BEq, Inhabited

/-- A branch decision made during IF processing inside a rewrite step. -/
inductive BranchDecision where
  | true (test : SExpr) (justification : BranchJustification)
  | false (test : SExpr) (justification : BranchJustification)
  deriving Repr, BEq, Inhabited

/-- A node in the proof tree. Each node claims `lhs = rhs` by some
    rule, and may contain child nodes that are sub-proofs (e.g., the
    steps inside a definition expansion's body rewriting). -/
inductive ProofNode where
  | node (rune : String × String) (lhs rhs : SExpr)
         (children : List ProofNode)
  deriving Repr, Inhabited

/-- Proof that a single literal simplifies to a result under clause
    assumptions. The nodes form a proof tree: top-level nodes are the
    main reasoning chain, and each node may contain sub-proofs. -/
structure LiteralProof where
  index : Nat
  literal : SExpr
  notFlg : Bool
  nodes : List ProofNode
  result : SExpr
  deriving Repr, Inhabited

/-- Proof of one clause (one induction case or a direct simplification).
    A clause is a disjunction of literals; the proof simplifies each
    literal, showing the clause is valid. -/
structure CaseProof where
  clauseId : String
  clause : List SExpr
  literalProofs : List LiteralProof
  deriving Repr, Inhabited

/-- A complete proof of a theorem. -/
structure TheoremProof where
  name : String
  formula : SExpr
  induction : Option InductionStep
  cases : List CaseProof
  deriving Repr, Inhabited

/-! ## Parser: flat trace → proof tree -/

/-- Map an IF-TEST justification SExpr to a BranchJustification. -/
private def parseBranchJustification (j : SExpr) : BranchJustification :=
  match j with
  | .atom (.keyword "rewritten-to-constant") => .rewrittenConstant
  | .atom (.keyword "type-set") => .typeSet
  | .atom (.keyword "clause") => .clauseAssumption
  | _ => .unknown

/-- Recursively parse a flat event list into a proof tree.
    Returns the parsed nodes and any remaining (unconsumed) events.

    The tree structure comes from BEGIN/END-INNER-REWRITE markers:
    events inside a BEGIN/END block become children of the next
    REWRITE-STEP at the enclosing level.

    Uses a fuel parameter for termination. -/
private def parseProofNodesAux (fuel : Nat) (events : List TraceEvent)
    (pendingChildren : List ProofNode) (nodes : List ProofNode)
    : List ProofNode × List TraceEvent :=
  match fuel with
  | 0 => (nodes.reverse, events)
  | fuel + 1 =>
    match events with
    | [] => (nodes.reverse, [])
    | .beginInnerRewrite _ :: rest =>
        let (innerNodes, rest') := parseProofNodesAux fuel rest [] []
        parseProofNodesAux fuel rest' (pendingChildren ++ innerNodes) nodes
    | .endInnerRewrite _ :: rest =>
        (nodes.reverse, rest)
    | .beginIfRewrite _ _ :: rest =>
        let (innerNodes, rest') := parseProofNodesAux fuel rest [] []
        parseProofNodesAux fuel rest' (pendingChildren ++ innerNodes) nodes
    | .endIfRewrite _ _ :: rest =>
        (nodes.reverse, rest)
    | .rewriteStep step :: rest =>
        let node := .node step.rune step.lhs step.rhs pendingChildren
        parseProofNodesAux fuel rest [] (node :: nodes)
    | .ifTestTrue _ _ _ :: rest | .ifTestFalse _ _ _ :: rest
    | .ifTestUnknown _ _ _ :: rest =>
        parseProofNodesAux fuel rest pendingChildren nodes
    | _ :: rest =>
        parseProofNodesAux fuel rest pendingChildren nodes

/-- Parse a flat event list into a proof tree using BEGIN/END-INNER-REWRITE
    markers for tree structure. Events inside a BEGIN/END block become
    children of the next REWRITE-STEP at the enclosing level. -/
def buildProofNodes (events : List TraceEvent) : List ProofNode × List TraceEvent :=
  parseProofNodesAux (events.length + 1) events [] []

/-- Collect events for a single literal from the trace. Returns events
    between BEGIN-LITERAL and END-LITERAL, and the remaining events.
    Uses a fuel bound to ensure termination. -/
private def collectLiteralEvents (index : Nat) (events : List TraceEvent)
    (fuel : Nat) : List TraceEvent × List TraceEvent :=
  match fuel, events with
  | 0, rest => ([], rest)
  | _, [] => ([], [])
  | fuel + 1, .endLiteral idx _ _ :: rest =>
      if idx == index then ([], rest)
      else
        let (inner, remaining) := collectLiteralEvents index rest fuel
        (.endLiteral idx .nil 0 :: inner, remaining)
  | fuel + 1, ev :: rest =>
      let (inner, remaining) := collectLiteralEvents index rest fuel
      (ev :: inner, remaining)

/-- Find the rewritten result for a literal from its trace events.
    Looks for a REWRITTEN-LITERAL event; falls back to the original. -/
private def findLiteralResult (events : List TraceEvent) (original : SExpr) : SExpr :=
  events.foldl (fun acc ev =>
    match ev with
    | .rewrittenLiteral _ result => result
    | _ => acc) original

/-- Build LiteralProofs from a flat event list. Extracts events between
    BEGIN-LITERAL/END-LITERAL boundaries and converts each to a
    LiteralProof with JustifiedSteps. -/
def buildLiteralProofs (events : List TraceEvent) : List LiteralProof := Id.run do
  let mut result : Array LiteralProof := #[]
  let mut remaining := events
  let mut fuel := events.length + 1  -- termination bound
  while remaining.length > 0 && fuel > 0 do
    fuel := fuel - 1
    match remaining with
    | .beginLiteral index literal notFlg :: rest =>
      let (litEvents, rest') := collectLiteralEvents index rest (rest.length + 1)
      let (nodes, _) := buildProofNodes litEvents
      let litResult := findLiteralResult litEvents literal
      result := result.push ⟨index, literal, notFlg, nodes, litResult⟩
      remaining := rest'
    | _ :: rest => remaining := rest
    | [] => break
  return result.toList

/-- Build a CaseProof from a ProofStep. -/
def buildCaseProof (step : ProofStep) : CaseProof :=
  { clauseId := step.clauseId
    clause := step.inputClause
    literalProofs := buildLiteralProofs step.traceEvents }

/-- Build all TheoremProofs from a ProofLog by walking the event list
    sequentially. Each DEFTHM starts a theorem; events up to QED (or
    the next DEFTHM) are its proof. Imported theorems (no QED) are
    leaf nodes with no cases. -/
def buildAllTheoremProofs (log : ProofLog) : List TheoremProof := Id.run do
  let mut result : Array TheoremProof := #[]
  let mut curName : Option String := none
  let mut curFormula : SExpr := .nil
  let mut curSource : TheoremSource := .unknown
  let mut curInduction : Option InductionStep := none
  let mut curCases : Array CaseProof := #[]
  let mut fuel := log.events.length + 1
  for ev in log.events do
    fuel := fuel - 1
    if fuel == 0 then break
    match ev with
    | .defthm name formula source =>
      -- Close previous theorem if any
      if let some prevName := curName then
        let cases := curCases.toList.filter fun c => c.clauseId != "Goal"
        result := result.push {
          name := prevName, formula := curFormula,
          induction := curInduction, cases }
      -- Start new theorem
      curName := some name
      curFormula := formula
      curSource := source
      curInduction := none
      curCases := #[]
    | .induction i =>
      curInduction := some i
    | .step s =>
      if s.result == .proved && !s.traceEvents.isEmpty then
        curCases := curCases.push (buildCaseProof s)
      -- Also extract formula from first step if not in DEFTHM
      if curFormula == .nil && !s.inputClause.isEmpty then
        curFormula := match s.inputClause with
          | [lit] => lit
          | lits => SExpr.ofList lits
    | .qed =>
      -- Close current theorem
      if let some prevName := curName then
        let cases := curCases.toList.filter fun c => c.clauseId != "Goal"
        result := result.push {
          name := prevName, formula := curFormula,
          induction := curInduction, cases }
      curName := none
      curFormula := .nil
      curInduction := none
      curCases := #[]
  -- Close final theorem if no QED
  if let some prevName := curName then
    let cases := curCases.toList.filter fun c => c.clauseId != "Goal"
    result := result.push {
      name := prevName, formula := curFormula,
      induction := curInduction, cases }
  return result.toList

/-! ## Tests -/

section Tests

private def proofLogText : String := include_str "../acl2_samples/simple.proof-log"

private def getProof : Option TheoremProof := do
  let log ← (ProofLog.parse proofLogText).toOption
  (buildAllTheoremProofs log).head?

-- Theorem name (lowercased by parser)
#guard (getProof.map (·.name)) == some "my-len-my-app"

-- Has induction
#guard (getProof.map (·.induction.isSome)) == some true

-- Induction on MY-APP with 2 subgoals
#guard (getProof.bind (·.induction) |>.map (·.subgoalCount)) == some 2

-- Two proved cases (base + step)
#guard (getProof.map (·.cases.length)) == some 2

-- Base case is Subgoal *1/2
#guard (getProof.map fun p => p.cases[0]!.clauseId) == some "Subgoal *1/2"

-- Base case has literal proofs
#guard (getProof.map fun p => p.cases[0]!.literalProofs.length) == some 2

-- Base case literal 2 (the EQUAL literal) has proof nodes
private def baseCaseLit2Nodes : List ProofNode :=
  match getProof with
  | some proof =>
    match proof.cases[0]!.literalProofs.find? (·.index == 2) with
    | some lp => lp.nodes
    | none => []
  | none => []

private def nodeRune : ProofNode → String × String
  | .node r _ _ _ => r

private def nodeChildren : ProofNode → List ProofNode
  | .node _ _ _ cs => cs

-- Proof tree has nodes at the top level
#guard baseCaseLit2Nodes.length > 0

-- definition:my-app and definition:my-len are top-level nodes
-- (inner steps are now children, not siblings)
#guard baseCaseLit2Nodes.any (nodeRune · == ("definition", "my-app"))
#guard baseCaseLit2Nodes.any (nodeRune · == ("definition", "my-len"))

-- Definition expansion nodes have children (the inner proof steps)
#guard baseCaseLit2Nodes.any fun n => (nodeChildren n).length > 0

-- Step case is Subgoal *1/1
#guard (getProof.map fun p => p.cases[1]!.clauseId) == some "Subgoal *1/1"

/-! ### Multi-theorem book tests -/

private def isortLogText : String := include_str "../acl2_samples/sorting/isort.proof-log"

private def isortProofs : List TheoremProof :=
  match ProofLog.parse isortLogText with
  | .ok log => buildAllTheoremProofs log
  | .error _ => []

-- Multi-theorem book: isort has theorems
#guard isortProofs.length > 0

end Tests

end ACL2
