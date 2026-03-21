import ACL2Lean.Syntax
import ACL2Lean.Parser

namespace ACL2

/-- Result of a waterfall step: the goal was either proved or split into subgoals. -/
inductive ProofResult where
  | proved
  | subgoals
  deriving Repr, BEq

/-- A single waterfall step from ACL2's structured proof output. -/
structure ProofStep where
  clauseId : String
  processor : String
  result : ProofResult
  /-- Runes used in this step, as (type, name) pairs, e.g. ("rewrite", "car-cons"). -/
  runes : List (String × String)
  /-- Output clauses if result is subgoals. -/
  newClauses : List SExpr := []
  deriving Repr

/-- An induction scheme choice from ACL2. -/
structure InductionStep where
  /-- The function call that triggered induction, e.g. (MY-APP A B). -/
  term : SExpr
  subgoalCount : Nat
  /-- The generated clause set (each clause is a disjunction of literals). -/
  scheme : List SExpr
  deriving Repr

/-- A single event in the proof log. -/
inductive ProofEvent where
  | step (s : ProofStep)
  | induction (i : InductionStep)
  | qed
  deriving Repr

/-- Complete proof log, a sequence of proof events. -/
structure ProofLog where
  events : List ProofEvent
  deriving Repr

namespace ProofLog

/-- Look up a keyword in a plist-style s-expression list.
    Given `[:key1, val1, :key2, val2, ...]`, returns `val` for the matching key. -/
private def lookupKeyword (kw : String) : List SExpr → Option SExpr
  | .atom (.keyword k) :: v :: rest =>
    if k == kw then some v else lookupKeyword kw rest
  | _ :: rest => lookupKeyword kw rest
  | [] => none

/-- Extract a string from a symbol or string atom. -/
private def atomString? : SExpr → Option String
  | .atom (.symbol s) => some s.name
  | .atom (.string s) => some s
  | .atom (.keyword k) => some k
  | _ => none

/-- Parse a single rune like `(:REWRITE CAR-CONS)` into a (type, name) pair. -/
private def parseRune? : SExpr → Option (String × String)
  | .cons (.atom (.keyword runeType)) (.cons nameExpr .nil) =>
    match atomString? nameExpr with
    | some name => some (runeType, name)
    | none => some (runeType, toString (repr nameExpr))
  | _ => none

/-- Parse a rune list like `((:REWRITE FOO) (:DEFINITION BAR))`. -/
private def parseRunes (s : SExpr) : List (String × String) :=
  match s.toList? with
  | some items => items.filterMap parseRune?
  | none => []

/-- Parse a (:STEP ...) s-expression. -/
private def parseStep? (items : List SExpr) : Except String ProofStep := do
  let clauseId ← match lookupKeyword "clause-id" items with
    | some s => match atomString? s with
      | some str => pure str
      | none => throw s!"STEP: bad :CLAUSE-ID value: {repr s}"
    | none => throw "STEP: missing :CLAUSE-ID"
  let processor ← match lookupKeyword "processor" items with
    | some s => match atomString? s with
      | some str => pure str
      | none => throw s!"STEP: bad :PROCESSOR value: {repr s}"
    | none => throw "STEP: missing :PROCESSOR"
  let result ← match lookupKeyword "result" items with
    | some (.atom (.keyword "proved")) => pure ProofResult.proved
    | some (.atom (.keyword "subgoals")) => pure ProofResult.subgoals
    | some s => throw s!"STEP: bad :RESULT value: {repr s}"
    | none => throw "STEP: missing :RESULT"
  let runes := match lookupKeyword "runes" items with
    | some s => parseRunes s
    | none => []
  let newClauses := match lookupKeyword "new-clauses" items with
    | some s => match s.toList? with
      | some cs => cs
      | none => [s]
    | none => []
  pure { clauseId, processor, result, runes, newClauses }

/-- Parse a (:INDUCTION ...) s-expression. -/
private def parseInduction? (items : List SExpr) : Except String InductionStep := do
  let term ← match lookupKeyword "term" items with
    | some s => pure s
    | none => throw "INDUCTION: missing :TERM"
  let subgoalCount ← match lookupKeyword "subgoal-count" items with
    | some (.atom (.number (.int n))) => pure n.toNat
    | some s => throw s!"INDUCTION: bad :SUBGOAL-COUNT: {repr s}"
    | none => throw "INDUCTION: missing :SUBGOAL-COUNT"
  let scheme := match lookupKeyword "scheme" items with
    | some s => match s.toList? with
      | some cs => cs
      | none => [s]
    | none => []
  pure { term, subgoalCount, scheme }

/-- Parse a single top-level s-expression from the proof log. -/
private def parseEvent (s : SExpr) : Except String ProofEvent := do
  match s with
  | .cons (.atom (.keyword "step")) rest =>
    match rest.toList? with
    | some items => return .step (← parseStep? items)
    | none => throw s!"STEP: expected plist, got {repr rest}"
  | .cons (.atom (.keyword "induction")) rest =>
    match rest.toList? with
    | some items => return .induction (← parseInduction? items)
    | none => throw s!"INDUCTION: expected plist, got {repr rest}"
  | .cons (.atom (.keyword "qed")) _ =>
    return .qed
  | _ => throw s!"Unknown proof log event: {repr s}"

/-- Parse a proof log from raw ACL2 output.
    Finds the (:BEGIN-PROOF-LOG) marker in the raw text and parses only
    the s-expressions after it. Everything before the marker (SBCL banner,
    ACL2 startup, prompts) is discarded as raw text.
    Everything after the marker must be valid proof log s-expressions. -/
def parse (input : String) : Except String ProofLog := do
  let marker := "(:BEGIN-PROOF-LOG)"
  let parts := input.splitOn marker
  if parts.length < 2 then
    throw "No (:BEGIN-PROOF-LOG) marker found in input"
  let proofText := String.intercalate marker parts.tail!
  let sexprs ← Parse.parseAll proofText
  let mut events := #[]
  for s in sexprs do
    events := events.push (← parseEvent s)
  pure { events := events.toList }

/-- Pretty-print a proof log summary. -/
def summary (log : ProofLog) : String :=
  let steps := log.events.filter fun e => match e with | .step _ => true | _ => false
  let inductions := log.events.filter fun e => match e with | .induction _ => true | _ => false
  let qeds := log.events.filter fun e => match e with | .qed => true | _ => false
  let processors := steps.filterMap fun e => match e with
    | .step s => some s.processor | _ => none
  let procPairs := processors.foldl (init := ([] : List (String × Nat)))
    fun acc p =>
      match acc.find? (fun (k, _) => k == p) with
      | some _ => acc.map fun (k, n) => if k == p then (k, n + 1) else (k, n)
      | none => acc ++ [(p, 1)]
  let lines := #[
    s!"Proof log: {log.events.length} events",
    s!"  Steps: {steps.length}",
    s!"  Inductions: {inductions.length}",
    s!"  QEDs: {qeds.length}",
    "  By processor:"
  ]
  let procLines := procPairs.map fun (p, n) => s!"    {p}: {n}"
  "\n".intercalate (lines.toList ++ procLines)

end ProofLog
end ACL2
