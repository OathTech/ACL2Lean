import ACL2Lean.Syntax
import ACL2Lean.Parser

namespace ACL2

/-- Result of a waterfall step: the goal was either proved or split into subgoals. -/
inductive ProofResult where
  | proved
  | subgoals
  deriving Repr, BEq, Inhabited

/-- One frame of a rewrite's congruence path (from the log's `:PATH`),
    literal-root-first. `.arg n fn` = this frame's term (head `fn`) sits at the
    one-based argument position `n` of its parent — a real congruence position.
    `.boundary kind fn` = a descent through an unfold / rule-RHS (symbolic bkptr,
    e.g. `BODY`/`RHS`/`EXPANSION`), where the term structure changed; these align
    with the proof tree's child-nesting. Emitted by `structured-rewrite-path` in
    the instrumented ACL2 (read from the rewriter's gstack). -/
inductive PathFrame where
  | arg (idx : Nat) (fn : Symbol)
  | boundary (kind : Symbol) (fn : Symbol)
  deriving Repr, Inhabited, BEq

/-- A single rewrite application from ACL2's rewriter. -/
structure RewriteStep where
  /-- The rune applied, as (type, name) e.g. ("rewrite", "car-cons"). -/
  rune : String × String
  /-- The term before rewriting. -/
  lhs : SExpr
  /-- The term AFTER rewriting — note (B3): for a `with-lemma`/recursive-definition
      step this is the rule's instantiated RHS *after it is itself recursively
      rewritten* (those inner rewrites are logged separately as this step's
      children, under BEGIN/END-INNER-REWRITE). So `rhs` is the cumulative result,
      NOT `(apply rune once to lhs)`. A replay must treat the children as the
      sub-derivation that produced `rhs`. -/
  rhs : SExpr
  /-- Which code path produced this step (e.g., "fncall/non-recursive"). -/
  origin : String := ""
  /-- Note (B2): this is the CUMULATIVE rune set in the ttree on ENTRY to the
      step (`all-runes-in-ttree`), i.e. rules accumulated by prior steps — NOT
      the rule this step applied. THIS step's rule is `rune`. Do not read `runes`
      as "this step's dependencies." (Exception: on a `type-set` node — built by
      ProofTree, not from a RewriteStep — `runes` IS the per-step justification.) -/
  runes : List (String × String) := []
  /-- Clause literal parent indices from the ttree. -/
  parents : List SExpr := []
  /-- Formal→actual substitution for definition expansions. -/
  subst : List (SExpr × SExpr) := []
  /-- The equivalence formula for rewriting-equivalence steps. -/
  equivTerm : Option SExpr := none
  /-- Type-set of the argument (for recognizer steps). -/
  typeSet : Option Int := none
  /-- True type-set of the recognizer (type-set bits where it returns T). -/
  trueTs : Option Int := none
  /-- The redex's congruence path within the literal (from `:PATH`),
      literal-root-first. Lets a replay lift this step by composing congruences
      along the path instead of locating the redex by subterm match. -/
  path : List PathFrame := []
  deriving Repr

/-- A trace event from ACL2's detailed rewriter output.
    These appear inside the :REWRITES field of a waterfall step. -/
inductive TraceEvent where
  | rewriteStep (step : RewriteStep)
  | ifTestTrue (test : SExpr) (unrewrittenTest : SExpr) (justification : SExpr)
  | ifTestFalse (test : SExpr) (unrewrittenTest : SExpr) (justification : SExpr)
  | ifTestUnknown (test : SExpr) (unrewrittenTest : SExpr) (justification : SExpr)
  | beginLiteral (index : Nat) (literal : SExpr) (notFlg : Bool)
  | endLiteral (index : Nat) (result : SExpr) (branches : Nat)
  | rewrittenLiteral (original : SExpr) (result : SExpr)
  | beginBranch (segment : SExpr)
  | endBranch
  | caseSplit (literalIndex : Nat) (numBranches : Nat)
  | branchSubstitution (equivalence : SExpr) (lhs : SExpr) (rhs : SExpr)
  | contextSubst (var : SExpr) (value : SExpr) (justification : SExpr)
  | typeSetReasoning (term : SExpr) (result : SExpr) (notFlg : Bool) (justification : SExpr)
  | beginInnerRewrite (kind : String)
  | endInnerRewrite (kind : String)
  | beginIfRewrite (test : SExpr) (unrewrittenTest : SExpr)
  | endIfRewrite (test : SExpr) (result : SExpr)
  deriving Repr

/-- A single waterfall step from ACL2's structured proof output. -/
structure ProofStep where
  clauseId : String
  processor : String
  result : ProofResult
  /-- Runes used in this step, as (type, name) pairs, e.g. ("rewrite", "car-cons"). -/
  runes : List (String × String)
  /-- Full detailed trace events from ACL2's rewriter. -/
  traceEvents : List TraceEvent := []
  /-- Input clause (disjunction of literals). -/
  inputClause : List SExpr := []
  /-- Output clauses if result is subgoals. -/
  newClauses : List SExpr := []
  /-- Every STEP plist field not otherwise modeled above, captured verbatim as
      (keyword, value) — so nothing is silently dropped. This is where the
      processor-specific justifications live: `:FERTILIZE` (:bullet/:target/
      :equiv), `:ELIMSEQUENCE`/`:ELIMVARS` (destructor elimination), `:GENERALIZE`
      (:terms/:vars). The replay reads these to mirror fertilize/eliminate/
      generalize steps. -/
  extraFields : List (String × SExpr) := []
  deriving Repr

namespace ProofStep

/-- Extract just the rewrite steps from the trace events. -/
def rewriteSteps (s : ProofStep) : List RewriteStep :=
  s.traceEvents.filterMap fun
    | .rewriteStep step => some step
    | _ => none

end ProofStep

/-- One case of an induction scheme: the governing `tests` (the conditions under which this
    case applies) and, per induction hypothesis, the substitution `alist` (var ↦ term) giving
    the IH instance. A base case has `alists = []`; a step case has one alist per recursive call.
    From ACL2's `tests-and-alists`. -/
structure InductionCase where
  tests : List SExpr
  alists : List (List (Symbol × SExpr))
  deriving Repr, Inhabited

/-- An induction scheme choice from ACL2, with its MEASURE JUSTIFICATION (from the winning
    candidate's `justification`): what decreases (`measure`) under the well-founded relation
    `rel` on domain `mp`, over the controller variables `controllers`; plus the per-case structure
    (`cases`: tests + IH substitutions). The justification fields default to empty so legacy
    proof-logs (pre measure-emission) still parse. -/
structure InductionStep where
  /-- The function call that triggered induction, e.g. (MY-APP A B). -/
  term : SExpr
  subgoalCount : Nat
  /-- The generated clause set (each clause is a disjunction of literals). -/
  scheme : List SExpr
  /-- User-level induction term (`:XTERM`; `term` may be an induction-rule alias). -/
  xterm : SExpr := .nil
  /-- The measure term that decreases, e.g. `(acl2-count x)`. -/
  measure : SExpr := .nil
  /-- The well-founded relation, e.g. `o<`. -/
  rel : SExpr := .nil
  /-- The relation's domain predicate, e.g. `o-p`. -/
  mp : SExpr := .nil
  /-- The conjecture-level controller variables the induction is on (the measure's measured
      formals, instantiated to the conjecture's actuals). -/
  controllers : List Symbol := []
  /-- Per-case tests + IH substitution alists. -/
  cases : List InductionCase := []
  deriving Repr

/-- Where a theorem comes from in the proof log. -/
inductive TheoremSource where
  | local       -- proved in this file
  | includeBook -- imported from another book
  | unknown     -- source not specified (old trace format)
  deriving Repr, BEq

/-- A single event in the proof log. -/
inductive ProofEvent where
  | defun (name : String) (formals : List Symbol) (body : SExpr)
  | defthm (name : String) (formula : SExpr := .nil) (source : TheoremSource := .unknown)
  | typePrescription (name : String) (corollary : SExpr)
      (basicTs : Option Int := none) (leaves : List (SExpr × Int) := [])
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

/-- All (keyword, value) pairs of a plist whose key is NOT in `known` — used to
    capture unmodeled fields verbatim rather than silently dropping them. -/
private def plistExtras (known : List String) : List SExpr → List (String × SExpr)
  | .atom (.keyword k) :: v :: rest =>
    if known.contains k then plistExtras known rest
    else (k, v) :: plistExtras known rest
  | _ :: rest => plistExtras known rest
  | [] => []

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

/-- Parse a rune list like `((:REWRITE FOO) (:DEFINITION BAR))`. Hard-fails on a
    malformed rune or a non-list (no silent drop). -/
def parseRunes (s : SExpr) : Except String (List (String × String)) :=
  match s.toList? with
  | some items => items.mapM fun r => match parseRune? r with
    | some rune => pure rune
    | none => throw s!"bad rune in rune list: {repr r}"
  | none => throw s!"rune list is not a list: {repr s}"

/-- Parse one `(bkptr . fn)` frame of a `:PATH`. Numeric `bkptr` → `.arg`; symbolic
    `bkptr` (BODY/RHS/EXPANSION/…) → `.boundary`. Hard-fails on a non-symbol `fn`
    (lambda/quote paths not yet supported) or a malformed pair (no silent drop). -/
private def parsePathFrame (pair : SExpr) : Except String PathFrame := do
  -- Each frame is the dotted pair `(bkptr . fn)` = `.cons bkptr fn`.
  let (bk, fn) ← match pair with
    | .cons bk fn => pure (bk, fn)
    | _ => throw s!"REWRITE-STEP :PATH frame not a (bkptr . fn) pair: {repr pair}"
  let fsym ← match fn with
    | .atom (.symbol s) => pure s
    | _ => throw s!"REWRITE-STEP :PATH frame fn not a symbol (lambda/quote unsupported): {repr fn}"
  match bk with
  | .atom (.number (.int n)) => pure (.arg n.toNat fsym)
  | .atom (.symbol k) => pure (.boundary k fsym)
  | _ => throw s!"REWRITE-STEP :PATH frame bkptr not a number/symbol: {repr bk}"

/-- Parse a single (:REWRITE-STEP :RUNE r :LHS l :RHS r …) s-expression. -/
private def parseRewriteStep? (s : SExpr) : Except String RewriteStep := do
  match s.toList? with
  | some items =>
    match items with
    | .atom (.keyword "rewrite-step") :: rest =>
      let rune ← match lookupKeyword "rune" rest with
        | some r => match parseRune? r with
          | some rune => pure rune
          | none => throw s!"REWRITE-STEP: bad :RUNE: {repr r}"
        | none => throw "REWRITE-STEP: missing :RUNE"
      let lhs ← match lookupKeyword "lhs" rest with
        | some s => pure s
        | none => throw "REWRITE-STEP: missing :LHS"
      let rhs ← match lookupKeyword "rhs" rest with
        | some s => pure s
        | none => throw "REWRITE-STEP: missing :RHS"
      -- Optional provenance fields
      let origin := match lookupKeyword "origin" rest with
        | some (.atom (.symbol s)) => s.name
        | _ => ""
      let runes ← match lookupKeyword "runes" rest with
        | some r => match r.toList? with
          | some items => items.mapM fun r => match parseRune? r with
            | some rune => pure rune
            | none => throw s!"REWRITE-STEP: bad rune in :RUNES: {repr r}"
          | none => throw s!"REWRITE-STEP: :RUNES not a list: {repr r}"
        | none => pure []
      let parents := match lookupKeyword "parents" rest with
        | some r => match r.toList? with
          | some items => items
          | none => []
        | none => []
      let subst ← match lookupKeyword "subst" rest with
        | some r => match r.toList? with
          | some items => items.mapM fun pair =>
            match pair.toList? with
            | some [k, v] => pure (k, v)
            | _ => match pair with  -- dotted pair (k . v) or (k . (v ...))
              | .cons k v => pure (k, v)
              | _ => throw s!"REWRITE-STEP: bad :SUBST pair: {repr pair}"
          | none => throw s!"REWRITE-STEP: :SUBST not a list: {repr r}"
        | none => pure []
      let equivTerm := lookupKeyword "equiv-term" rest
      let typeSet := match lookupKeyword "typeset" rest with
        | some (.atom (.number (.int n))) => some n
        | _ => none
      let trueTs := match lookupKeyword "truets" rest with
        | some (.atom (.number (.int n))) => some n
        | _ => none
      let path ← match lookupKeyword "path" rest with
        | some r => match r.toList? with
          | some items => items.mapM parsePathFrame
          | none => throw s!"REWRITE-STEP: :PATH not a list: {repr r}"
        | none => pure []
      pure { rune, lhs, rhs, origin, runes, parents, subst, equivTerm, typeSet, trueTs, path }
    | _ => throw s!"REWRITE-STEP: expected :REWRITE-STEP keyword, got {repr s}"
  | none => throw s!"REWRITE-STEP: expected list, got {repr s}"

/-- Parse a single trace event from the :REWRITES field. -/
private def parseTraceEvent (s : SExpr) : Except String TraceEvent := do
  match s.toList? with
  | some items =>
    match items with
    | .atom (.keyword "rewrite-step") :: _ =>
        pure (.rewriteStep (← parseRewriteStep? s))
    | .atom (.keyword "if-test-true") :: rest =>
        let test ← lookupKeyword "test" rest |>.elim (throw "IF-TEST-TRUE: missing :TEST") pure
        let unrewritten ← lookupKeyword "unrewritten-test" rest
          |>.elim (throw "IF-TEST-TRUE: missing :UNREWRITTEN-TEST") pure
        let justification := (lookupKeyword "justification" rest).getD .nil
        pure (.ifTestTrue test unrewritten justification)
    | .atom (.keyword "if-test-false") :: rest =>
        let test ← lookupKeyword "test" rest |>.elim (throw "IF-TEST-FALSE: missing :TEST") pure
        let unrewritten ← lookupKeyword "unrewritten-test" rest
          |>.elim (throw "IF-TEST-FALSE: missing :UNREWRITTEN-TEST") pure
        let justification := (lookupKeyword "justification" rest).getD .nil
        pure (.ifTestFalse test unrewritten justification)
    | .atom (.keyword "if-test-unknown") :: rest =>
        let test ← lookupKeyword "test" rest |>.elim (throw "IF-TEST-UNKNOWN: missing :TEST") pure
        let unrewritten ← lookupKeyword "unrewritten-test" rest
          |>.elim (throw "IF-TEST-UNKNOWN: missing :UNREWRITTEN-TEST") pure
        let justification := (lookupKeyword "justification" rest).getD .nil
        pure (.ifTestUnknown test unrewritten justification)
    | .atom (.keyword "begin-literal") :: rest =>
        let index ← match lookupKeyword "index" rest with
          | some (.atom (.number (.int n))) => pure n.toNat
          | some s => throw s!"BEGIN-LITERAL: bad :INDEX: {repr s}"
          | none => throw "BEGIN-LITERAL: missing :INDEX"
        let literal ← lookupKeyword "literal" rest
          |>.elim (throw "BEGIN-LITERAL: missing :LITERAL") pure
        let notFlg := match lookupKeyword "not-flg" rest with
          | some .nil => false
          | _ => true
        pure (.beginLiteral index literal notFlg)
    | .atom (.keyword "end-literal") :: rest =>
        let index ← match lookupKeyword "index" rest with
          | some (.atom (.number (.int n))) => pure n.toNat
          | some s => throw s!"END-LITERAL: bad :INDEX: {repr s}"
          | none => throw "END-LITERAL: missing :INDEX"
        let result ← lookupKeyword "result" rest
          |>.elim (throw "END-LITERAL: missing :RESULT") pure
        let branches ← match lookupKeyword "branches" rest with
          | some (.atom (.number (.int n))) => pure n.toNat
          | some s => throw s!"END-LITERAL: bad :BRANCHES: {repr s}"
          | none => throw "END-LITERAL: missing :BRANCHES"
        pure (.endLiteral index result branches)
    | .atom (.keyword "rewritten-literal") :: rest =>
        let original ← lookupKeyword "original" rest
          |>.elim (throw "REWRITTEN-LITERAL: missing :ORIGINAL") pure
        let result ← lookupKeyword "result" rest
          |>.elim (throw "REWRITTEN-LITERAL: missing :RESULT") pure
        pure (.rewrittenLiteral original result)
    | .atom (.keyword "begin-branch") :: rest =>
        let segment := (lookupKeyword "segment" rest).getD .nil
        pure (.beginBranch segment)
    | .atom (.keyword "end-branch") :: _ =>
        pure .endBranch
    | .atom (.keyword "case-split") :: rest =>
        let litIdx ← match lookupKeyword "literal-index" rest with
          | some (.atom (.number (.int n))) => pure n.toNat
          | some s => throw s!"CASE-SPLIT: bad :LITERAL-INDEX: {repr s}"
          | none => throw "CASE-SPLIT: missing :LITERAL-INDEX"
        let numBranches ← match lookupKeyword "num-branches" rest with
          | some (.atom (.number (.int n))) => pure n.toNat
          | some s => throw s!"CASE-SPLIT: bad :NUM-BRANCHES: {repr s}"
          | none => throw "CASE-SPLIT: missing :NUM-BRANCHES"
        pure (.caseSplit litIdx numBranches)
    | .atom (.keyword "branch-substitution") :: rest =>
        let equivalence ← lookupKeyword "equivalence" rest
          |>.elim (throw "BRANCH-SUBSTITUTION: missing :EQUIVALENCE") pure
        let lhs ← lookupKeyword "lhs" rest
          |>.elim (throw "BRANCH-SUBSTITUTION: missing :LHS") pure
        let rhs ← lookupKeyword "rhs" rest
          |>.elim (throw "BRANCH-SUBSTITUTION: missing :RHS") pure
        pure (.branchSubstitution equivalence lhs rhs)
    | .atom (.keyword "context-subst") :: rest =>
        let var ← lookupKeyword "variable" rest
          |>.elim (throw "CONTEXT-SUBST: missing :VARIABLE") pure
        let value ← lookupKeyword "value" rest
          |>.elim (throw "CONTEXT-SUBST: missing :VALUE") pure
        let justification := (lookupKeyword "justification" rest).getD .nil
        pure (.contextSubst var value justification)
    | .atom (.keyword "type-set-reasoning") :: rest =>
        let term ← lookupKeyword "term" rest
          |>.elim (throw "TYPE-SET-REASONING: missing :TERM") pure
        let result ← lookupKeyword "result" rest
          |>.elim (throw "TYPE-SET-REASONING: missing :RESULT") pure
        let notFlg := match lookupKeyword "not-flg" rest with
          | some .nil => false
          | _ => true
        let justification := (lookupKeyword "justification" rest).getD .nil
        pure (.typeSetReasoning term result notFlg justification)
    | .atom (.keyword "begin-inner-rewrite") :: rest =>
        let kind := match lookupKeyword "kind" rest with
          | some (.atom (.symbol s)) => s.name
          | some (.atom (.keyword k)) => k
          | _ => "unknown"
        pure (.beginInnerRewrite kind)
    | .atom (.keyword "end-inner-rewrite") :: rest =>
        let kind := match lookupKeyword "kind" rest with
          | some (.atom (.symbol s)) => s.name
          | some (.atom (.keyword k)) => k
          | _ => "unknown"
        pure (.endInnerRewrite kind)
    | .atom (.keyword "begin-if-rewrite") :: rest =>
        let test ← lookupKeyword "test" rest
          |>.elim (throw "BEGIN-IF-REWRITE: missing :TEST") pure
        let unrewrittenTest := (lookupKeyword "unrewritten-test" rest).getD .nil
        pure (.beginIfRewrite test unrewrittenTest)
    | .atom (.keyword "end-if-rewrite") :: rest =>
        let test ← lookupKeyword "test" rest
          |>.elim (throw "END-IF-REWRITE: missing :TEST") pure
        let result := (lookupKeyword "result" rest).getD .nil
        pure (.endIfRewrite test result)
    | _ => throw s!"Unknown trace event: {repr s}"
  | none => throw s!"Expected list trace event, got: {repr s}"

/-- Parse a list of trace events from the :REWRITES field. -/
private def parseTraceEvents (s : SExpr) : Except String (List TraceEvent) := do
  match s.toList? with
  | some items =>
    let mut result := #[]
    for item in items do
      result := result.push (← parseTraceEvent item)
    pure result.toList
  | none => throw s!"REWRITES: expected list, got {repr s}"

/-- Parse a (:STEP ...) s-expression. -/
private def parseStep? (items : List SExpr) : Except String ProofStep := do
  let clauseId ← match lookupKeyword "clauseid" items with
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
  let runes ← match lookupKeyword "runes" items with
    | some s => parseRunes s
    | none => pure []
  let traceEvents ← match lookupKeyword "rewrites" items with
    | some s => parseTraceEvents s
    | none => pure []
  let inputClause ← match lookupKeyword "inputclause" items with
    | some s => match s.toList? with
      | some cs => pure cs
      | none => throw s!"STEP: :INPUTCLAUSE is not a list: {repr s}"
    | none => pure []
  let newClauses ← match lookupKeyword "newclauses" items with
    | some s => match s.toList? with
      | some cs => pure cs
      | none => throw s!"STEP: :NEWCLAUSES is not a list: {repr s}"
    | none => pure []
  let extraFields := plistExtras
    ["clauseid", "processor", "result", "runes", "rewrites", "inputclause", "newclauses"] items
  pure { clauseId, processor, result, runes, traceEvents, inputClause, newClauses, extraFields }

/-- Parse one IH substitution alist `((var . term) …)`. ACL2 prints a pair `(v . t)` as
    `(v . t)` or, when `t` is a list, as `(v t…)` — both are `.cons (symbol v) t`. -/
private def parseAlist (s : SExpr) : Except String (List (Symbol × SExpr)) := do
  match s.toList? with
  | some pairs => pairs.mapM fun p => match p with
      | .cons (.atom (.symbol v)) term => pure (v, term)
      | _ => throw s!"INDUCTION :ALISTS: bad pair (expected (var . term)): {repr p}"
  | none => throw s!"INDUCTION :ALISTS: alist not a list: {repr s}"

/-- Parse one `(:TESTS (test…) :ALISTS (alist…))` induction case. -/
private def parseCase (s : SExpr) : Except String InductionCase := do
  match s.toList? with
  | some items =>
    let tests ← match lookupKeyword "tests" items with
      | some t => t.toList?.elim (throw s!"INDUCTION case :TESTS not a list: {repr t}") pure
      | none => pure []
    let alists ← match lookupKeyword "alists" items with
      | some a => match a.toList? with
        | some als => als.mapM parseAlist
        | none => throw s!"INDUCTION case :ALISTS not a list: {repr a}"
      | none => pure []
    pure { tests, alists }
  | none => throw s!"INDUCTION case not a plist: {repr s}"

/-- Parse a (:INDUCTION ...) s-expression. The measure-justification fields
    (:XTERM/:MEASURE/:REL/:MP/:SUBSET/:CASES) are optional — absent in legacy logs. -/
private def parseInduction? (items : List SExpr) : Except String InductionStep := do
  let term ← match lookupKeyword "term" items with
    | some s => pure s
    | none => throw "INDUCTION: missing :TERM"
  let subgoalCount ← match lookupKeyword "subgoals" items with
    | some (.atom (.number (.int n))) => pure n.toNat
    | some s => throw s!"INDUCTION: bad :SUBGOALS: {repr s}"
    | none => throw "INDUCTION: missing :SUBGOALS"
  let scheme ← match lookupKeyword "scheme" items with
    | some s => match s.toList? with
      | some cs => pure cs
      | none => throw s!"INDUCTION: :SCHEME is not a list: {repr s}"
    | none => pure []
  let xterm := (lookupKeyword "xterm" items).getD .nil
  let measure := (lookupKeyword "measure" items).getD .nil
  let rel := (lookupKeyword "rel" items).getD .nil
  let mp := (lookupKeyword "mp" items).getD .nil
  let controllers ← match lookupKeyword "controllers" items with
    | some s => match s.toList? with
      | some xs => xs.mapM fun x => match x with
        | .atom (.symbol v) => pure v
        | _ => throw s!"INDUCTION: :CONTROLLERS non-symbol element: {repr x}"
      | none => throw s!"INDUCTION: :CONTROLLERS not a list: {repr s}"
    | none => pure []
  let cases ← match lookupKeyword "cases" items with
    | some c => match c.toList? with
      | some cs => cs.mapM parseCase
      | none => throw s!"INDUCTION: :CASES not a list: {repr c}"
    | none => pure []
  pure { term, subgoalCount, scheme, xterm, measure, rel, mp, controllers, cases }

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
  | .cons (.atom (.keyword "defthm")) rest =>
    match rest.toList? with
    | some (nameExpr :: fields) =>
      match atomString? nameExpr with
      | some name =>
        let formula ← (lookupKeyword "formula" fields).elim
          (throw s!"DEFTHM {name}: missing :FORMULA") pure
        let source := match lookupKeyword "source" fields with
          | some (.atom (.keyword "include-book")) => TheoremSource.includeBook
          | some (.atom (.keyword "local")) => TheoremSource.local
          | _ => TheoremSource.unknown
        return .defthm name formula source
      | none => throw s!"DEFTHM: bad name: {repr nameExpr}"
    | some [] => throw s!"DEFTHM: missing name"
    | none => throw s!"DEFTHM: expected plist, got {repr rest}"
  | .cons (.atom (.keyword "defun")) rest =>
    match rest.toList? with
    | some (nameExpr :: fields) =>
      match atomString? nameExpr with
      | some name =>
        let formals := match lookupKeyword "formals" fields with
          | some f => match f.toList? with
            | some syms => syms.filterMap fun
              | .atom (.symbol s) => some s
              | _ => none
            | none => []
          | none => []
        let body ← (lookupKeyword "body" fields).elim
          (throw s!"DEFUN {name}: missing :BODY") pure
        return .defun name formals body
      | none => throw s!"DEFUN: bad name: {repr nameExpr}"
    | _ => throw s!"DEFUN: expected plist, got {repr rest}"
  | .cons (.atom (.keyword "type-prescription")) rest =>
    match rest.toList? with
    | some (nameExpr :: fields) =>
      match atomString? nameExpr with
      | some name =>
        let corollary ← (lookupKeyword "corollary" fields).elim
          (throw s!"TYPE-PRESCRIPTION {name}: missing :COROLLARY") pure
        let basicTs := match lookupKeyword "basicts" fields with
          | some (.atom (.number (.int n))) => some n
          | _ => none
        let leaves ← match lookupKeyword "leaves" fields with
          | some l => match l.toList? with
            | some items => items.mapM fun pair =>
              -- Each leaf is a proper list (term type-set-bits)
              match pair.toList? with
              | some [term, .atom (.number (.int ts))] => pure (term, ts)
              | _ => throw s!"TYPE-PRESCRIPTION {name}: bad leaf: {repr pair}"
            | none => throw s!"TYPE-PRESCRIPTION {name}: :LEAVES not a list: {repr l}"
          | none => pure []
        return .typePrescription name corollary basicTs leaves
      | none => throw s!"TYPE-PRESCRIPTION: bad name: {repr nameExpr}"
    | _ => throw s!"TYPE-PRESCRIPTION: expected plist, got {repr rest}"
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
  let defthms := log.events.filterMap fun e => match e with | .defthm n _ _ => some n | _ => none
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
    | .defthm name _ _ :: rest =>
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

end ProofLog
end ACL2
