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
  | defthm (name : String)
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
  | .cons (.atom (.keyword "defthm")) (.cons nameExpr .nil) =>
    match atomString? nameExpr with
    | some name => return .defthm name
    | none => throw s!"DEFTHM: bad name: {repr nameExpr}"
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
  let defthms := log.events.filterMap fun e => match e with | .defthm n => some n | _ => none
  let processors := steps.filterMap fun e => match e with
    | .step s => some s.processor | _ => none
  let procPairs := processors.foldl (init := ([] : List (String × Nat)))
    fun acc p =>
      match acc.find? (fun (k, _) => k == p) with
      | some _ => acc.map fun (k, n) => if k == p then (k, n + 1) else (k, n)
      | none => acc ++ [(p, 1)]
  let lines := #[
    s!"Proof log: {log.events.length} events",
    s!"  Theorems: {defthms.length} ({String.intercalate ", " defthms})",
    s!"  Steps: {steps.length}",
    s!"  Inductions: {inductions.length}",
    s!"  QEDs: {qeds.length}",
    "  By processor:"
  ]
  let procLines := procPairs.map fun (p, n) => s!"    {p}: {n}"
  "\n".intercalate (lines.toList ++ procLines)

/-- Split a proof log into named per-theorem segments.
    Each segment starts with a (:DEFTHM name) event and ends with (:QED).
    Returns (name, events) pairs. -/
def splitByTheorem (log : ProofLog) : List (String × List ProofEvent) :=
  let rec go (events : List ProofEvent) (curName : Option String)
      (current : List ProofEvent) (acc : List (String × List ProofEvent)) :
      List (String × List ProofEvent) :=
    match events with
    | [] =>
      match curName with
      | some n => ((n, current.reverse) :: acc).reverse
      | none => acc.reverse
    | .defthm name :: rest =>
      -- Start a new theorem segment; flush any previous
      let acc := match curName with
        | some n => (n, current.reverse) :: acc
        | none => acc
      go rest (some name) [] acc
    | .qed :: rest =>
      match curName with
      | some n => go rest none [] ((n, (.qed :: current).reverse) :: acc)
      | none => go rest none [] acc  -- QED without defthm, skip
    | e :: rest => go rest curName (e :: current) acc
  go log.events none [] []

/-- Sanitize an ACL2 name to a Lean identifier (same as Translator.sanitizeName). -/
private def sanitize (s : String) : String :=
  let s := s.replace "-" "_"
  let s := s.replace "=" "_eq_"
  let s := s.replace "+" "_plus_"
  let s := s.replace "*" "_times_"
  s.replace "/" "_div_"

/-- Convert a rune (type, name) pair to a Lean simp lemma name.
    Returns none for rune types that don't map to simp lemmas. -/
private def runeToLeanName (runeType : String) (runeName : String) : Option String :=
  match runeType with
  | "definition" | "rewrite" | "type-prescription"
  | "forward-chaining" | "linear" | "congruence" | "compound-recognizer" =>
    some (sanitize runeName)
  | "executable-counterpart" => none  -- handled by decide/native_decide
  | "fake-rune-for-type-set" => none  -- built-in, no Lean analog
  | "fake-rune-for-linear" => none    -- handled by omega
  | "fake-rune-for-linear-equalities" => none
  | "induction" => none               -- not a simp lemma
  | "elim" => none                    -- handled structurally
  | _ => panic! s!"Unknown rune type: {runeType}"

/-- Convert a list of runes to Lean simp lemma names. -/
private def runesToSimpArgs (runes : List (String × String)) : List String :=
  runes.filterMap fun (t, n) => runeToLeanName t n

/-- Check if a rune list includes linear arithmetic fake runes. -/
private def hasLinearArith (runes : List (String × String)) : Bool :=
  runes.any fun (t, _) => t == "fake-rune-for-linear" || t == "fake-rune-for-linear-equalities"

/-- Generate a tactic string for a single simp step. -/
private def simpStepTactic (runes : List (String × String)) : String :=
  let simpArgs := runesToSimpArgs runes
  let omega := if hasLinearArith runes then "; try omega" else ""
  if simpArgs.isEmpty then
    s!"simp{omega}"
  else
    s!"simp only [{String.intercalate ", " simpArgs}]{omega}"

/-- Extract function name and argument variable names from an induction term
    like (PERM X Y) → ("perm", ["x", "y"]). -/
private def parseInductionTerm (term : SExpr) : String × List String :=
  match term with
  | .cons (.atom (.symbol s)) rest =>
    let funcName := sanitize s.normalizedName
    let args := match rest.toList? with
      | some items => items.filterMap fun
          | .atom (.symbol v) => some (sanitize v.normalizedName)
          | _ => none
      | none => []
    (funcName, args)
  | _ => ("unknown", [])

/-- Generate a tactic string for a single theorem's proof events.
    Returns `none` if the events are empty (no proof needed). -/
def generateTacticScript (events : List ProofEvent) : Option String :=
  if events.isEmpty then none
  else
    -- Find the first induction (if any)
    let inductionStep := events.findSome? fun
      | .induction i => some i
      | _ => none
    -- Collect ALL runes from all steps (not just proved — intermediate runes matter)
    let allRunes := events.foldl (init := ([] : List (String × String))) fun acc e =>
      match e with
      | .step s => acc ++ s.runes
      | _ => acc
    -- Deduplicate runes
    let uniqueRunes := allRunes.foldl (init := ([] : List (String × String))) fun acc r =>
      if acc.contains r then acc else acc ++ [r]
    let simpArgs := runesToSimpArgs uniqueRunes
    let hasOmega := hasLinearArith uniqueRunes
    let simpStr := if simpArgs.isEmpty then "simp" else
      s!"simp only [{String.intercalate ", " simpArgs}]"
    let omegaStr := if hasOmega then "\n  try omega" else ""
    match inductionStep with
    | some indStep =>
      let (funcName, argNames) := parseInductionTerm indStep.term
      let argsStr := if argNames.isEmpty then "" else
        " " ++ String.intercalate " " argNames
      -- Generate induction with args from the induction term.
      -- Try all args first; if the .induct principle wants fewer targets,
      -- fall back to just the last arg (the typical decreasing parameter).
      let argsComma := String.intercalate ", " argNames
      let lastArg := argNames.getLast!
      let inductTactic := if argNames.length <= 1 then
        s!"induction {argsComma} using {funcName}.induct"
      else
        s!"first | induction {argsComma} using {funcName}.induct | induction {lastArg} using {funcName}.induct"
      some s!"by\n  {inductTactic}\n  all_goals {simpStr}{omegaStr}\n  all_goals acl2_grind"
    | none =>
      some s!"by\n  {simpStr}{omegaStr}"

end ProofLog
end ACL2
