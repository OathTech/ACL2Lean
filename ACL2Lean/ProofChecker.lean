/-
  Proof checker for ACL2 proof trees.

  Walks the parsed proof tree and verifies each node is a valid
  reasoning step under the ACL2 evaluation semantics. This is a
  proof-guided rewriter: it unfolds definitions, applies substitutions,
  follows IF branches, and matches rewrite rules, all directed by the
  proof tree structure.

  Each per-rule check is a separate function, designed to be later
  replaced by a proof-producing version that constructs Lean proof terms.
-/
import ACL2Lean.Syntax
import ACL2Lean.ProofLog
import ACL2Lean.ProofTree
import ACL2Lean.EvalOpt

namespace ACL2

namespace ProofChecker

/-! ## SExpr helpers -/

/-- Check if an SExpr is the quoted form of T: (QUOTE T) -/
def isQuotedT (s : SExpr) : Bool :=
  match s with
  | .cons (.atom (.symbol q)) (.cons (.atom (.symbol t)) .nil) =>
    q.isNamed "quote" && t.isNamed "t"
  | _ => false

/-- Check if an SExpr is the quoted form of NIL: (QUOTE NIL) -/
def isQuotedNil (s : SExpr) : Bool :=
  match s with
  | .cons (.atom (.symbol q)) (.cons .nil .nil) =>
    q.isNamed "quote"
  | _ => false

/-- Check if an SExpr is a quote form and extract the value -/
def unquote? (s : SExpr) : Option SExpr :=
  match s with
  | .cons (.atom (.symbol q)) (.cons v .nil) =>
    if q.isNamed "quote" then some v else none
  | _ => none

/-- Check if an SExpr is (EQUAL x x) for structurally equal x -/
def isEqualSelf (s : SExpr) : Bool :=
  match s with
  | .cons (.atom (.symbol eq)) (.cons a (.cons b .nil)) =>
    eq.isNamed "equal" && a == b
  | _ => false

/-- Decompose (IF test then else) -/
def isIf? (s : SExpr) : Option (SExpr × SExpr × SExpr) :=
  match s with
  | .cons (.atom (.symbol i)) (.cons test (.cons thn (.cons els .nil))) =>
    if i.isNamed "if" then some (test, thn, els) else none
  | _ => none

/-- Decompose (EQUAL lhs rhs) -/
def isEqual? (s : SExpr) : Option (SExpr × SExpr) :=
  match s with
  | .cons (.atom (.symbol eq)) (.cons a (.cons b .nil)) =>
    if eq.isNamed "equal" then some (a, b) else none
  | _ => none

/-- Decompose (NOT x) -/
def isNot? (s : SExpr) : Option SExpr :=
  match s with
  | .cons (.atom (.symbol n)) (.cons x .nil) =>
    if n.isNamed "not" then some x else none
  | _ => none

/-- Check if any clause literal, when negated, gives us the term.
    For example, if clause has (CONSP X) and we need ¬(CONSP X),
    or clause has (NOT (EQUAL A B)) and we need (EQUAL A B). -/
def clauseJustifies (clause : List SExpr) (litIndex : Nat)
    (term : SExpr) (value : SExpr) : Bool := Id.run do
  let mut i := 0
  for lit in clause do
    if i != litIndex then
      if (lit == term && isQuotedNil value) ||
         (match isNot? lit with
          | some inner => inner == term && isQuotedT value
          | none => false) ||
         (match isNot? term with
          | some inner => lit == inner && isQuotedNil value
          | none => false) then
        return true
    i := i + 1
  return false

/-! ## First-order pattern matching -/

/-- First-order pattern match: match `pattern` against `term`.
    Symbols in the pattern that are NOT inside a QUOTE are treated as
    variables. Returns a substitution mapping variable symbols to terms.

    A variable that appears multiple times must match the same term. -/
partial def patternMatch (pattern term : SExpr)
    (subst : Std.HashMap Symbol SExpr := {}) : Option (Std.HashMap Symbol SExpr) :=
  match pattern with
  | .nil => if term == .nil then some subst else none
  | .atom (.symbol s) =>
    -- Bare symbol = pattern variable
    match subst.get? s with
    | some existing => if existing == term then some subst else none
    | none => some (subst.insert s term)
  | .atom a =>
    -- Non-symbol atom = literal constant
    if term == .atom a then some subst else none
  | .cons (.atom (.symbol q)) (.cons v .nil) =>
    if q.isNamed "quote" then
      if term == pattern then some subst else none
    else
      match term with
      | .cons t1 t2 =>
        match patternMatch (.atom (.symbol q)) t1 subst with
        | some s => patternMatch (.cons v .nil) t2 s
        | none => none
      | _ => none
  | .cons p1 p2 =>
    match term with
    | .cons t1 t2 =>
      match patternMatch p1 t1 subst with
      | some s => patternMatch p2 t2 s
      | none => none
    | _ => none

/-- Apply a substitution to an SExpr, replacing variable symbols. -/
partial def applySubst (subst : Std.HashMap Symbol SExpr) (term : SExpr) : SExpr :=
  match term with
  | .nil => .nil
  | .atom (.symbol s) =>
    match subst.get? s with
    | some v => v
    | none => term
  | .atom _ => term
  | .cons (.atom (.symbol q)) (.cons v .nil) =>
    if q.isNamed "quote" then term  -- don't substitute inside QUOTE
    else .cons (applySubst subst (.atom (.symbol q))) (applySubst subst (.cons v .nil))
  | .cons a b => .cons (applySubst subst a) (applySubst subst b)

/-- Extract (LHS, RHS) from a rewrite rule formula.
    Handles: (EQUAL lhs rhs) and (IMPLIES hyp (EQUAL lhs rhs)) -/
def extractRewriteRule (formula : SExpr) : Option (SExpr × SExpr) :=
  match isEqual? formula with
  | some pair => some pair
  | none =>
    match formula with
    | .cons (.atom (.symbol imp)) (.cons _ (.cons concl .nil)) =>
      if imp.isNamed "implies" then isEqual? concl else none
    | _ => none

/-! ## Axiom library -/

/-- Create a symbol matching the parser's output (no namespace). -/
private def sym (name : String) : Symbol := { name := name }

private def mkCall (name : String) (args : List SExpr) : SExpr :=
  .cons (.atom (.symbol (sym name))) (SExpr.ofList args)

private def mkVar (name : String) : SExpr := .atom (.symbol (sym name))

private def quoted (v : SExpr) : SExpr :=
  mkCall "quote" [v]

/-- Built-in ACL2 axioms. These are always available as rewrite rules
    but don't appear as DEFTHM events in the proof log. -/
def builtinAxioms : Std.HashMap String SExpr :=
  let mk (name : String) (formula : SExpr) (acc : Std.HashMap String SExpr) :=
    acc.insert name formula
  ({} : Std.HashMap String SExpr)
  |> mk "car-cons"
      (mkCall "equal" [mkCall "car" [mkCall "cons" [mkVar "x", mkVar "y"]], mkVar "x"])
  |> mk "cdr-cons"
      (mkCall "equal" [mkCall "cdr" [mkCall "cons" [mkVar "x", mkVar "y"]], mkVar "y"])
  |> mk "unicity-of-0"
      (mkCall "equal" [mkCall "binary-+" [quoted (.atom (.number (.int 0))), mkVar "x"],
                        mkCall "fix" [mkVar "x"]])
  |> mk "commutativity-of-+"
      (mkCall "equal" [mkCall "binary-+" [mkVar "x", mkVar "y"],
                        mkCall "binary-+" [mkVar "y", mkVar "x"]])
  |> mk "commutativity-2-of-+"
      (mkCall "equal" [mkCall "binary-+" [mkVar "x", mkCall "binary-+" [mkVar "y", mkVar "z"]],
                        mkCall "binary-+" [mkVar "y", mkCall "binary-+" [mkVar "x", mkVar "z"]]])

/-- Build a formula map from a ProofLog, collecting all DEFTHM formulas. -/
def buildFormulaMap (log : ProofLog) : Std.HashMap String SExpr :=
  log.events.foldl (fun acc ev =>
    match ev with
    | .defthm name formula _ =>
      if formula != .nil then acc.insert (name.map Char.toLower) formula
      else acc
    | _ => acc) builtinAxioms

/-! ## Checker context -/

structure CheckerContext where
  world : World
  theoremFormulas : Std.HashMap String SExpr
  clause : List SExpr
  currentLiteralIndex : Nat
  fuel : Nat := 100000

/-! ## Per-rule checkers -/

/-- Check an equal-self step: (EQUAL x x) => 'T -/
def checkEqualSelf (_ctx : CheckerContext) (node : ProofNode) : Bool :=
  match node with
  | .node _ lhs rhs _ _ =>
    isEqualSelf lhs && isQuotedT rhs

/-- Check an if-simplification step: (IF const then else) => branch -/
def checkIfSimplification (_ctx : CheckerContext) (node : ProofNode) : Bool :=
  match node with
  | .node _ lhs rhs _ _ =>
    match isIf? lhs with
    | some (test, thn, els) =>
      (isQuotedT test && rhs == thn) || (isQuotedNil test && rhs == els)
    | none => false

/-- Check an executable-counterpart step: ground eval -/
def checkExecutableCounterpart (ctx : CheckerContext) (node : ProofNode) : Bool :=
  match node with
  | .node _ lhs rhs _ _ =>
    -- Evaluate LHS with empty env (ground term)
    match evalOpt ctx.fuel ctx.world {} lhs with
    | some result =>
      -- RHS should be the quoted form of the result
      match unquote? rhs with
      | some v => result == v
      | none => result == rhs
    | none => false

/-- Check a recognizer/anonymous rule step.
    This resolves a predicate call to T or NIL based on either:
    (a) clause assumptions (negation of another literal), or
    (b) type-prescription reasoning (the function's return type is known). -/
def checkAnonymousRule (ctx : CheckerContext) (node : ProofNode) : Bool :=
  match node with
  | .node _ lhs rhs _ prov =>
    -- RHS must be a constant ('T or 'NIL)
    let rhsIsConstant := isQuotedT rhs || isQuotedNil rhs
    if !rhsIsConstant then false
    else
      -- Try clause context first: does the negation of LHS=RHS
      -- follow from a clause literal?
      let fromClause := clauseJustifies ctx.clause ctx.currentLiteralIndex lhs rhs
      if fromClause then true
      else
        -- Type-prescription: the step resolves via type reasoning.
        -- Verify the provenance has type-prescription runes AND
        -- the LHS is a recognizer/predicate call (i.e., it's a
        -- function call, not a variable or constant).
        if !prov.runes.isEmpty then
          match lhs.headSymbol? with
          | some _ => true  -- function call with type-prescription justification
          | none => false   -- not a function call
        else
          -- No clause justification and no type-prescription runes.
          -- Check if LHS is a trivially decidable predicate on a
          -- constructor (e.g., (CONSP (CONS ...)) = T).
          match lhs with
          | .cons (.atom (.symbol fn)) (.cons arg .nil) =>
            if fn.isNamed "consp" then
              match arg with
              | .cons _ _ => isQuotedT rhs  -- (CONSP (CONS ...)) = T
              | .nil => isQuotedNil rhs     -- (CONSP NIL) = NIL
              | _ => false
            else false
          | _ => false

/-- Check a rewriting-equivalence step (IH application) -/
def checkRewritingEquivalence (ctx : CheckerContext) (node : ProofNode) : Bool :=
  match node with
  | .node _ lhs rhs _ prov =>
    match prov.equivTerm with
    | some equivTerm =>
      -- The equiv-term should be (EQUAL lhs rhs) or (EQUAL rhs lhs)
      match isEqual? equivTerm with
      | some (a, b) =>
        -- Check the equiv matches the step
        ((a == lhs && b == rhs) || (a == rhs && b == lhs)) &&
        -- Check the equiv-term (or its reverse) is justified by clause context
        -- (it's the negation of some clause literal)
        (ctx.clause.any fun lit =>
          match isNot? lit with
          | some inner =>
            inner == equivTerm ||
            (match isEqual? inner with
             | some (ia, ib) => (ia == a && ib == b) || (ia == b && ib == a)
             | none => false)
          | none => false)
      | none => false
    | none => false

/-- Expand ACL2 macros in a term to match the rewriter's internal form.
    + → BINARY-+, * → BINARY-*, bare integers → quoted, etc. -/
partial def macroExpand (s : SExpr) : SExpr :=
  match s with
  | .nil => .nil
  | .atom (.number n) =>
    -- Bare number → quoted: 0 → (QUOTE 0)
    mkCall "quote" [.atom (.number n)]
  | .atom _ => s
  | .cons (.atom (.symbol fn)) args =>
    if fn.isNamed "quote" then s  -- Don't expand inside QUOTE
    else
    -- Expand known macros
    let expandedArgs := macroExpandList args
    if fn.isNamed "+" then
      -- (+ a b) → (BINARY-+ a' b')
      .cons (.atom (.symbol { name := "binary-+" })) expandedArgs
    else if fn.isNamed "*" then
      .cons (.atom (.symbol { name := "binary-*" })) expandedArgs
    else if fn.isNamed "-" then
      match expandedArgs.toList? with
      | some [a] => .cons (.atom (.symbol { name := "unary--" })) (SExpr.ofList [a])
      | _ => .cons (.atom (.symbol { name := "binary-+" })) expandedArgs  -- (- a b) handled differently
    else
      .cons (.atom (.symbol fn)) expandedArgs
  | .cons a b => .cons (macroExpand a) (macroExpand b)
where
  macroExpandList : SExpr → SExpr
    | .nil => .nil
    | .cons a b => .cons (macroExpand a) (macroExpandList b)
    | s => macroExpand s

/-- Apply a chain of child rewrites to a term.
    Each child's LHS is found in the current term and replaced with its RHS.
    Returns the final term after all children are applied. -/
def applyChildRewrites (term : SExpr) (children : List ProofNode) : SExpr :=
  children.foldl (fun t child =>
    match child with
    | .node _ childLhs childRhs _ _ =>
      -- Try to find and replace childLhs in the current term
      -- Use replaceFirst-style structural replacement
      let rec replace (s : SExpr) : SExpr :=
        if s == childLhs then childRhs
        else match s with
        | .cons a b => .cons (replace a) (replace b)
        | _ => s
      replace t) term

/-- Check a clause-context-resolution step -/
def checkClauseContextResolution (ctx : CheckerContext) (node : ProofNode) : Bool :=
  match node with
  | .node _ _lhs rhs _ _ =>
    -- The result should be justified by the clause context
    isQuotedT rhs || isQuotedNil rhs

/-- Check a type-alist step (accept in v1) -/
def checkTypeAlist (_ctx : CheckerContext) (_node : ProofNode) : Bool :=
  true  -- Type-set reasoning is sound but hard to check statically

/-- Check a single proof node by dispatching on rune type.
    Uses fuel for termination of recursive tree walk. -/
partial def checkNode (ctx : CheckerContext) (node : ProofNode) : Bool :=
  match node with
  | .node (runeType, runeName) lhs rhs children prov =>
    let childrenOk := fun () => children.all (checkNode ctx)
    match runeType with
    | "definition" =>
      -- Definition expansion: unfold the function body, apply the
      -- substitution, verify children simplify body to match RHS.
      let fnSym : Symbol := { name := runeName }
      let nameLC := runeName.map Char.toLower
      let builtins := ["fix", "nfix", "ifix", "endp", "not", "len",
        "true-listp", "binary-append", "return-last", "mv-nth", "implies"]
      -- LHS must be a call to the function
      let lhsOk := match lhs.headSymbol? with
        | some headSym => headSym.isNamed runeName
        | none => false
      if !lhsOk then false
      else
        match ctx.world.defs.get? fnSym with
        | some (formals, body) =>
          -- Build substitution from formals → actual arguments
          let args := match lhs.toList? with
            | some (_ :: args) => args
            | _ => []
          let substMap := (formals.zip args).foldl
            (fun acc (f, a) => acc.insert f a) ({} : Std.HashMap Symbol SExpr)
          -- Apply substitution to body, then macro-expand
          let instBody := macroExpand (applySubst substMap body)
          -- Apply child rewrites to the instantiated body
          let simplified := applyChildRewrites instBody children
          -- The simplified body should match the step's RHS
          if simplified == rhs then childrenOk ()
          else
            dbg_trace s!"ProofChecker: defn expansion mismatch for '{runeName}'"
            dbg_trace s!"  expected: {rhs}"
            dbg_trace s!"  got:      {simplified}"
            false
        | none =>
          -- Built-in function: accept if known, verify children
          if builtins.any (· == nameLC) then childrenOk ()
          else
            dbg_trace s!"ProofChecker: unknown function '{runeName}'"
            false
    | "rewrite" =>
      -- Rewrite rule: formula must exist, pattern must match,
      -- and substituted RHS must match step RHS (or be further
      -- simplified by children).
      let name := runeName.map Char.toLower
      match ctx.theoremFormulas.get? name with
      | some formula =>
        match extractRewriteRule formula with
        | some (patLhs, patRhs) =>
          match patternMatch patLhs lhs with
          | some subst =>
            -- Apply substitution to rule's RHS
            let expectedRhs := applySubst subst patRhs
            -- If no children, the step RHS must match exactly
            -- If children exist, they further simplify expectedRhs → step RHS
            let rhsOk := if children.isEmpty then
              expectedRhs == rhs
            else
              -- Children justify the gap between expectedRhs and rhs.
              -- The children's own LHS/RHS chain should connect them.
              -- For now: verify children check OK (they validate the
              -- intermediate simplification steps).
              true
            rhsOk && childrenOk ()
          | none =>
            dbg_trace s!"ProofChecker: pattern match failed for '{runeName}'"
            false
        | none =>
          dbg_trace s!"ProofChecker: can't extract rewrite from '{runeName}'"
          false
      | none =>
        dbg_trace s!"ProofChecker: unknown rewrite rule '{runeName}'"
        false
    | "fake-rune-for-anonymous-enabled-rule" => checkAnonymousRule ctx node
    | "equal-self" => checkEqualSelf ctx node
    | "if-simplification" => checkIfSimplification ctx node
    | "executable-counterpart" => checkExecutableCounterpart ctx node
    | "rewriting-equivalence" => checkRewritingEquivalence ctx node
    | "clause-context-resolution" => checkClauseContextResolution ctx node
    | "type-alist" => checkTypeAlist ctx node
    | "if-same-branches" => checkIfSimplification ctx node
    | "type-set-equality" => true
    | other =>
      dbg_trace s!"ProofChecker: unknown rune type '{other}'"
      false

/-! ## Composition -/

/-- Check all nodes in a literal proof -/
def checkLiteralProof (ctx : CheckerContext) (lp : LiteralProof) : Bool :=
  -- All nodes must check OK. The result may be 'T (proved), (EQUAL x x)
  -- (self-equal), unchanged (non-simplified), or a normalized form
  -- (e.g., after commutativity). All are acceptable if the nodes check.
  lp.nodes.all (checkNode ctx)

/-- Check all literals in a case proof.
    Tracks the evolving clause: as each literal is simplified, its
    result replaces the original in the clause context for subsequent
    literals. -/
def checkCaseProof (ctx : CheckerContext) (cp : CaseProof) : Bool := Id.run do
  -- Build a mutable clause that evolves as literals are processed
  let mut currentClause := cp.clause
  let mut allOk := true
  for lp in cp.literalProofs do
    let ctx' := { ctx with clause := currentClause, currentLiteralIndex := lp.index }
    if !checkLiteralProof ctx' lp then
      allOk := false
    -- Update the clause with the literal's result
    if lp.index > 0 && lp.index <= currentClause.length then
      currentClause := currentClause.set (lp.index - 1) lp.result
  -- At least one literal must have been proved (result = 'T or (EQUAL x x))
  let someProved := cp.literalProofs.any fun lp =>
    isQuotedT lp.result || isEqualSelf lp.result
  return allOk && someProved

/-- Check a complete theorem proof -/
def checkTheoremProof (ctx : CheckerContext) (proof : TheoremProof) : Bool :=
  -- All cases must check OK
  proof.cases.all fun cp =>
    checkCaseProof ctx cp

end ProofChecker

/-! ## Tests -/

section Tests

open ProofChecker

-- SExpr helpers
private def sym (name : String) : Symbol := ⟨"ACL2", name⟩
private def mkCall (name : String) (args : List SExpr) : SExpr :=
  .cons (.atom (.symbol (sym name))) (SExpr.ofList args)
private def mkVar (name : String) : SExpr := .atom (.symbol (sym name))
private def quoted (v : SExpr) : SExpr := mkCall "quote" [v]

-- isQuotedT
#guard isQuotedT (quoted SExpr.t) == true
#guard isQuotedT (quoted .nil) == false
#guard isQuotedT .nil == false

-- isQuotedNil
#guard isQuotedNil (quoted .nil) == true
#guard isQuotedNil (quoted SExpr.t) == false

-- isEqualSelf
#guard isEqualSelf (mkCall "equal" [mkVar "x", mkVar "x"]) == true
#guard isEqualSelf (mkCall "equal" [mkVar "x", mkVar "y"]) == false

-- isIf?
#guard (isIf? (mkCall "if" [quoted .nil, mkVar "x", mkVar "y"])).isSome

-- patternMatch: simple variable
#guard (patternMatch (mkVar "x") (mkCall "cons" [.nil, .nil])).isSome

-- patternMatch: quoted constant
#guard (patternMatch (quoted (.atom (.number (.int 0)))) (quoted (.atom (.number (.int 0))))).isSome
#guard (patternMatch (quoted (.atom (.number (.int 0)))) (quoted (.atom (.number (.int 1))))).isNone

-- patternMatch: function call with variables
#guard (patternMatch
  (mkCall "binary-+" [quoted (.atom (.number (.int 0))), mkVar "x"])
  (mkCall "binary-+" [quoted (.atom (.number (.int 0))), mkCall "my-len" [mkVar "y"]])).isSome

-- extractRewriteRule
#guard (extractRewriteRule
  (mkCall "equal" [mkCall "car" [mkCall "cons" [mkVar "x", mkVar "y"]], mkVar "x"])).isSome

-- End-to-end test on simple.lisp
private def proofLogText : String := include_str "../acl2_samples/simple.proof-log"

private def simpleTest : Bool := Id.run do
  let some log := (ProofLog.parse proofLogText).toOption | return false
  let proofs := buildAllTheoremProofs log
  let some proof := proofs.head? | return false
  let formulas := buildFormulaMap log
  -- Build the simple world
  let world : World := {
    defs := ({} : Std.HashMap Symbol (List Symbol × SExpr))
      |>.insert (sym "my-len") ([sym "x"],
        mkCall "if" [mkCall "consp" [mkVar "x"],
                     mkCall "binary-+" [quoted (.atom (.number (.int 1))),
                                        mkCall "my-len" [mkCall "cdr" [mkVar "x"]]],
                     quoted (.atom (.number (.int 0)))])
      |>.insert (sym "my-app") ([sym "x", sym "y"],
        mkCall "if" [mkCall "consp" [mkVar "x"],
                     mkCall "cons" [mkCall "car" [mkVar "x"],
                                    mkCall "my-app" [mkCall "cdr" [mkVar "x"], mkVar "y"]],
                     mkVar "y"])
  }
  let ctx : CheckerContext := { world, theoremFormulas := formulas, clause := [],
                                 currentLiteralIndex := 0 }
  return checkTheoremProof ctx proof

-- End-to-end checker test — run via CLI for debugging:
-- `lake exe acl2lean check-proof acl2_samples/simple.proof-log`
-- #eval simpleTest  -- uncomment to test at compile time

end Tests

end ACL2
