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

/-- A rewrite step with its full justification: the rune applied,
    the before/after terms, and any IF branch decisions that were
    made during the step (e.g., inside a definition expansion). -/
structure JustifiedStep where
  rune : String × String
  lhs : SExpr
  rhs : SExpr
  branchDecisions : List BranchDecision := []
  deriving Repr, BEq, Inhabited

/-- Proof that a single literal simplifies to a result under clause
    assumptions. The steps form a chain: each step rewrites a subterm
    of the current term, producing a new term. -/
structure LiteralProof where
  index : Nat
  literal : SExpr
  notFlg : Bool
  steps : List JustifiedStep
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

/-- Convert a flat list of TraceEvents into JustifiedSteps by grouping
    IF-TEST events with the REWRITE-STEP they precede. IF-TEST-UNKNOWN
    events are skipped (they indicate undecided branches, not decisions). -/
def buildJustifiedSteps (events : List TraceEvent) : List JustifiedStep :=
  let (steps, _) := events.foldl (fun (acc, pending) ev =>
    match ev with
    | .ifTestTrue test _ justification =>
        (acc, pending ++ [.true test (parseBranchJustification justification)])
    | .ifTestFalse test _ justification =>
        (acc, pending ++ [.false test (parseBranchJustification justification)])
    | .ifTestUnknown _ _ _ =>
        (acc, pending)  -- skip: not a decision
    | .rewriteStep step =>
        (acc ++ [{ rune := step.rune, lhs := step.lhs, rhs := step.rhs,
                   branchDecisions := pending }], [])
    | _ => (acc, pending)) ([], [])
  steps

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
      let steps := buildJustifiedSteps litEvents
      let litResult := findLiteralResult litEvents literal
      result := result.push ⟨index, literal, notFlg, steps, litResult⟩
      remaining := rest'
    | _ :: rest => remaining := rest
    | [] => break
  return result.toList

/-- Build a CaseProof from a ProofStep. -/
def buildCaseProof (step : ProofStep) : CaseProof :=
  { clauseId := step.clauseId
    clause := step.inputClause
    literalProofs := buildLiteralProofs step.traceEvents }

/-- Build a TheoremProof from a segment of proof events (between one
    DEFTHM and the next, or end of log). Returns none if the segment
    has no theorem name or no formula. -/
def buildTheoremProof (events : List ProofEvent) : Option TheoremProof := do
  let name ← events.findSome? fun
    | .defthm n => some n
    | _ => none
  -- Formula: from the first step's input clause, or .nil for trivial theorems
  let formula := events.findSome? (fun
    | .step s =>
      if s.inputClause.isEmpty then none
      else match s.inputClause with
        | [lit] => some lit
        | lits => some (SExpr.ofList lits)
    | _ => none) |>.getD .nil
  let induction := events.findSome? fun
    | .induction i => some i
    | _ => none
  -- Collect steps that proved their goal and have trace events.
  let cases := events.filterMap fun
    | .step s =>
      if s.result == .proved && !s.traceEvents.isEmpty
      then some (buildCaseProof s)
      else none
    | _ => none
  -- Filter out the pre-induction push-clause step (which has traces
  -- but just echoes the formula without simplifying).
  let cases := cases.filter fun c => c.clauseId != "Goal"
  return { name, formula, induction, cases }

/-- Split a proof event list into per-theorem segments (each starting
    with a DEFTHM event). -/
private def splitOnDefthm (events : List ProofEvent) : List (List ProofEvent) :=
  let (segments, current) := events.foldl (fun (segs, cur) ev =>
    match ev with
    | .defthm _ => (if cur.isEmpty then segs else segs ++ [cur.reverse], [ev])
    | _ => (segs, ev :: cur)) ([], [])
  if current.isEmpty then segments else segments ++ [current.reverse]

/-- Build TheoremProofs for all theorems in a ProofLog. -/
def buildAllTheoremProofs (log : ProofLog) : List TheoremProof :=
  (splitOnDefthm log.events).filterMap buildTheoremProof

/-! ## Tests -/

section Tests

private def proofLogText : String := include_str "../acl2_samples/simple.proof-log"

private def getProof : Option TheoremProof := do
  let log ← (ProofLog.parse proofLogText).toOption
  buildTheoremProof log.events

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

-- Base case literal 2 (the EQUAL literal) has justified steps
private def baseCaseLit2Steps : List JustifiedStep :=
  match getProof with
  | some proof =>
    match proof.cases[0]!.literalProofs.find? (·.index == 2) with
    | some lp => lp.steps
    | none => []
  | none => []

-- With depth suppression removed from ACL2 logging, inner steps are
-- visible. The exact count depends on the trace version.
-- Check that we get steps and key runes are present.
#guard baseCaseLit2Steps.length > 0

-- definition:my-app and definition:my-len are present
#guard baseCaseLit2Steps.any (·.rune == ("definition", "my-app"))
#guard baseCaseLit2Steps.any (·.rune == ("definition", "my-len"))

-- At least one step has branch decisions
#guard baseCaseLit2Steps.any (·.branchDecisions.length > 0)

-- Step case is Subgoal *1/1
#guard (getProof.map fun p => p.cases[1]!.clauseId) == some "Subgoal *1/1"

/-! ### Multi-theorem book tests -/

private def isortLogText : String := include_str "../acl2_samples/sorting/isort.proof-log"

private def isortProofs : List TheoremProof :=
  match ProofLog.parse isortLogText with
  | .ok log => buildAllTheoremProofs log
  | .error _ => []

-- Multi-theorem book: multiple theorems in isort
#guard isortProofs.length > 10

-- First theorem's name
#guard isortProofs[0]!.name == "perm-is-an-equivalence"

end Tests

end ACL2
