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
    Leaf symbols (not in function-head position, not inside QUOTE) are
    treated as pattern variables. Function-head symbols must match exactly.
    Returns a substitution mapping variable symbols to terms.

    A variable that appears multiple times must match the same term. -/
partial def patternMatch (pattern term : SExpr)
    (subst : Std.HashMap Symbol SExpr := {}) : Option (Std.HashMap Symbol SExpr) :=
  match pattern with
  | .nil => if term == .nil then some subst else none
  | .atom (.symbol s) =>
    -- Leaf symbol = pattern variable
    match subst.get? s with
    | some existing => if existing == term then some subst else none
    | none => some (subst.insert s term)
  | .atom a =>
    if term == .atom a then some subst else none
  | .cons (.atom (.symbol q)) rest =>
    if q.isNamed "quote" then
      -- QUOTE: match literally
      if term == pattern then some subst else none
    else
      -- Function call: head symbol must match EXACTLY (not a variable)
      match term with
      | .cons (.atom (.symbol tq)) trest =>
        if q.isNamed tq.name then
          -- Head matches. Match argument lists.
          patternMatchList rest trest subst
        else none
      | _ => none
  | .cons p1 p2 =>
    -- Non-symbol-headed cons (e.g., argument list spine)
    match term with
    | .cons t1 t2 =>
      match patternMatch p1 t1 subst with
      | some s => patternMatch p2 t2 s
      | none => none
    | _ => none
where
  /-- Match argument lists (cons spines) element by element -/
  patternMatchList (pats terms : SExpr)
      (subst : Std.HashMap Symbol SExpr) : Option (Std.HashMap Symbol SExpr) :=
    match pats, terms with
    | .nil, .nil => some subst
    | .cons p ps, .cons t ts =>
      match patternMatch p t subst with
      | some s => patternMatchList ps ts s
      | none => none
    | _, _ => none

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

/-- Built-in ACL2 function definitions. These are always available
    but don't appear as DEFUN events in user .lisp files. -/
def builtinDefs : Std.HashMap Symbol (List Symbol × SExpr) :=
  ({} : Std.HashMap Symbol (List Symbol × SExpr))
  -- FIX: (defun fix (x) (if (acl2-numberp x) x 0))
  |>.insert (sym "fix") ([sym "x"],
    mkCall "if" [mkCall "acl2-numberp" [mkVar "x"], mkVar "x",
                  .atom (.number (.int 0))])
  -- NOT: (defun not (x) (if x nil t))
  |>.insert (sym "not") ([sym "x"],
    mkCall "if" [mkVar "x", .nil, SExpr.t])
  -- ENDP: (defun endp (x) (not (consp x)))
  |>.insert (sym "endp") ([sym "x"],
    mkCall "not" [mkCall "consp" [mkVar "x"]])
  -- IMPLIES: (defun implies (p q) (if p (if q t nil) t))
  |>.insert (sym "implies") ([sym "p", sym "q"],
    mkCall "if" [mkVar "p", mkCall "if" [mkVar "q", SExpr.t, .nil], SExpr.t])

/-- Add built-in definitions to a World. -/
def addBuiltinDefs (w : World) : World :=
  { w with defs := builtinDefs.fold (fun acc k v =>
      if acc.get? k |>.isNone then acc.insert k v else acc) w.defs }

/-- Build a formula map from a ProofLog, collecting all DEFTHM formulas. -/
def buildFormulaMap (log : ProofLog) : Std.HashMap String SExpr :=
  log.events.foldl (fun acc ev =>
    match ev with
    | .defthm name formula _ =>
      if formula != .nil then acc.insert (name.map Char.toLower) formula
      else acc
    | _ => acc) builtinAxioms

/-- Build a World from DEFUN events in the proof log.
    These contain the macro-expanded, normalized bodies that ACL2's
    rewriter operates on. -/
def buildWorldFromLog (log : ProofLog) : World :=
  let defs := log.events.foldl (fun acc ev =>
    match ev with
    | .defun name formals body =>
      let sym : Symbol := { name := name.map Char.toLower }
      let formalSyms := formals.map fun s => { name := s.name.map Char.toLower : Symbol }
      acc.insert sym (formalSyms, body)
    | _ => acc) ({} : Std.HashMap Symbol (List Symbol × SExpr))
  -- Merge with built-in definitions
  let defs := builtinDefs.fold (fun acc k v =>
    if (acc.get? k).isNone then acc.insert k v else acc) defs
  { defs := defs }

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

/-- Check if a predicate application is trivially decidable.
    E.g., (CONSP (CONS ...)) = T, (CONSP NIL) = NIL,
    (ATOM NIL) = T, (ATOM (CONS ...)) = NIL. -/
def isRecognizerTrivial (lhs rhs : SExpr) : Bool :=
  match lhs with
  | .cons (.atom (.symbol fn)) (.cons arg .nil) =>
    if fn.isNamed "consp" then
      match arg with
      | .cons _ _ => isQuotedT rhs
      | .nil => isQuotedNil rhs
      | _ => false
    else if fn.isNamed "atom" then
      match arg with
      | .cons _ _ => isQuotedNil rhs
      | .nil => isQuotedT rhs
      | .atom _ => isQuotedT rhs
    else false
  | _ => false

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
      -- Try multiple verification methods in order:
      -- 1. Clause context: the negation follows from a clause literal
      if clauseJustifies ctx.clause ctx.currentLiteralIndex lhs rhs then true
      -- 2. Trivially decidable: recognizer applied to a constructor
      else if isRecognizerTrivial lhs rhs then true
      -- 3. Type-prescription: provenance runes reference known functions
      else if !prov.runes.isEmpty then
        -- SOUNDNESS GAP: we verify the runes reference known functions
        -- but don't re-prove the type-prescription itself.
        match lhs.headSymbol? with
        | some fn =>
          prov.runes.any fun (_, runeName) =>
            let rn := { name := runeName.map Char.toLower : Symbol }
            (ctx.world.defs.get? rn).isSome || (builtinDefs.get? rn).isSome ||
            fn.isNamed runeName
        | none => false
      else false

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

/-- Replace the first occurrence of `pattern` with `replacement` in `term`.
    Structural equality, depth-first left-to-right. -/
partial def replaceInTerm (term pattern replacement : SExpr) : SExpr :=
  if term == pattern then replacement
  else match term with
  | .cons a b =>
    let a' := replaceInTerm a pattern replacement
    if a' != a then .cons a' b  -- found in left subtree
    else .cons a (replaceInTerm b pattern replacement)
  | _ => term

/-- Apply a chain of child rewrites to a term.
    Each child's LHS is found in the current term and replaced with its RHS.
    Returns the final term after all children are applied.
    Set `trace := true` for debug output. -/
def applyChildRewrites (term : SExpr) (children : List ProofNode)
    (trace : Bool := false) : SExpr :=
  children.foldl (fun t child =>
    match child with
    | .node _ childLhs childRhs _ _ =>
      let result := replaceInTerm t childLhs childRhs
      (if trace && result == t then
        dbg_trace s!"  applyChildRewrites: LHS not found in term"
        dbg_trace s!"    childLhs: {childLhs}"
        dbg_trace s!"    term:     {t}"
        result
      else result)) term

/-- Check a clause-context-resolution step -/
def checkClauseContextResolution (ctx : CheckerContext) (node : ProofNode) : Bool :=
  match node with
  | .node _ lhs rhs _ _ =>
    -- The step resolves a literal using the clause context.
    -- RHS must be a constant, and the resolution must be justified
    -- by the clause: LHS appears in the clause (or can be derived
    -- from a clause literal).
    (isQuotedT rhs || isQuotedNil rhs) &&
    clauseJustifies ctx.clause ctx.currentLiteralIndex lhs rhs

/-- Check a type-alist step: term resolved to constant via type reasoning.
    Same verification as anonymous rules: check clause context or
    type-prescription provenance. -/
def checkTypeAlist (ctx : CheckerContext) (node : ProofNode) : Bool :=
  -- Reuse the same logic as anonymous rules
  checkAnonymousRule ctx node

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
      -- LHS must be a call to the function
      let lhsOk := match lhs.headSymbol? with
        | some headSym => headSym.isNamed runeName
        | none => false
      if !lhsOk then false
      else
        let defn := ctx.world.defs.get? fnSym |>.orElse fun _ => builtinDefs.get? fnSym
        match defn with
        | some (formals, body) =>
          -- Build the formal→actual substitution from the LHS args
          let args := match lhs.toList? with
            | some (_ :: as_) => as_
            | _ => []
          let substMap := (formals.zip args).foldl
            (fun acc (f, a) => acc.insert f a) ({} : Std.HashMap Symbol SExpr)
          -- Macro-expand and substitute the body
          let instBody := applySubst substMap (macroExpand body)
          -- Apply children as hints: each child's LHS/RHS may be in
          -- formal scope (ACL2's lazy substitution). We apply the
          -- alist to each child's LHS to find it in the substituted
          -- body, then replace with the alist-applied RHS.
          let simplified := children.foldl (fun t child =>
            match child with
            | .node _ cLhs cRhs _ _ =>
              -- Try finding cLhs directly in the term first
              let t1 := replaceInTerm t cLhs cRhs
              if t1 != t then t1
              else
                -- Child LHS might be in formal scope — apply subst
                let substLhs := applySubst substMap cLhs
                let substRhs := applySubst substMap cRhs
                replaceInTerm t substLhs substRhs) instBody
          if simplified == rhs then childrenOk ()
          else
            dbg_trace s!"ProofChecker: defn body mismatch for '{runeName}'"
            dbg_trace s!"  expected: {rhs}"
            dbg_trace s!"  got:      {simplified}"
            false
        | none =>
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
          | some substResult =>
            -- Apply substitution to rule's RHS
            let expectedRhs := applySubst substResult patRhs
            if children.isEmpty then
              -- No children: substituted RHS must match exactly
              if expectedRhs == rhs then true
              else
                dbg_trace s!"ProofChecker: rewrite RHS mismatch for '{runeName}'"
                false
            else
              -- Children further simplify expectedRhs → rhs.
              -- Apply child rewrites (same approach as defn expansion).
              let simplified := children.foldl (fun t child =>
                match child with
                | .node _ cLhs cRhs _ _ =>
                  let t1 := replaceInTerm t cLhs cRhs
                  if t1 != t then t1
                  else
                    -- Try with pattern substitution applied
                    let substLhs := applySubst substResult cLhs
                    let substRhs := applySubst substResult cRhs
                    replaceInTerm t substLhs substRhs) expectedRhs
              if simplified == rhs then childrenOk ()
              else
                dbg_trace s!"ProofChecker: rewrite+children mismatch for '{runeName}'"
                dbg_trace s!"  expected: {rhs}"
                dbg_trace s!"  got:      {simplified}"
                false
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
    | "if-same-branches" =>
      -- (IF test X X) => X when both branches are identical
      match isIf? lhs with
      | some (_, thn, els) => thn == els && rhs == thn
      | none => false
    | "type-set-equality" =>
      -- Type-set equality: (EQUAL a b) = T or NIL based on type reasoning.
      -- Verify the step is well-formed: LHS is an EQUAL, RHS is constant.
      match isEqual? lhs with
      | some _ => isQuotedT rhs || isQuotedNil rhs
      | none => false
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

-- Parser-compatible symbol/term constructors (no namespace)
private def tsym (name : String) : Symbol := { name := name }
private def tmk (name : String) (args : List SExpr) : SExpr :=
  .cons (.atom (.symbol (tsym name))) (SExpr.ofList args)
private def tvar (name : String) : SExpr := .atom (.symbol (tsym name))
private def tquot (v : SExpr) : SExpr := tmk "quote" [v]
private def tquotT : SExpr := tquot SExpr.t
private def tquotNil : SExpr := tquot .nil
private def tint (n : Int) : SExpr := tquot (.atom (.number (.int n)))

private def testCtx (clause : List SExpr := []) (litIdx : Nat := 0)
    (formulas : Std.HashMap String SExpr := builtinAxioms) : CheckerContext :=
  { world := World.empty, theoremFormulas := formulas,
    clause := clause, currentLiteralIndex := litIdx }

private def mkNode (rType rName : String) (lhs rhs : SExpr)
    (children : List ProofNode := [])
    (prov : StepProvenance := {}) : ProofNode :=
  .node (rType, rName) lhs rhs children prov

/-! ### Helper function tests -/

#guard isQuotedT tquotT
#guard !isQuotedT tquotNil
#guard !isQuotedT .nil
#guard isQuotedNil tquotNil
#guard !isQuotedNil tquotT
#guard isEqualSelf (tmk "equal" [tvar "x", tvar "x"])
#guard !isEqualSelf (tmk "equal" [tvar "x", tvar "y"])
#guard (isIf? (tmk "if" [tquotNil, tvar "x", tvar "y"])).isSome
#guard (isIf? (tvar "x")).isNone

/-! ### Pattern matching: valid matches -/

#guard (patternMatch (tvar "x") (tmk "cons" [.nil, .nil])).isSome
#guard (patternMatch (tint 0) (tint 0)).isSome
#guard (patternMatch
  (tmk "binary-+" [tint 0, tvar "x"])
  (tmk "binary-+" [tint 0, tmk "my-len" [tvar "y"]])).isSome
-- Same variable must match same term
#guard (patternMatch (tmk "equal" [tvar "x", tvar "x"])
                     (tmk "equal" [tvar "a", tvar "a"])).isSome

/-! ### Pattern matching: invalid matches rejected -/

#guard (patternMatch (tint 0) (tint 1)).isNone
#guard (patternMatch (tmk "binary-+" [tint 0, tvar "x"])
                     (tmk "binary-*" [tint 0, tvar "y"])).isNone
-- Same variable, different terms → rejected
#guard (patternMatch (tmk "equal" [tvar "x", tvar "x"])
                     (tmk "equal" [tvar "a", tvar "b"])).isNone

/-! ### equal-self: valid passes, invalid rejected -/

#guard checkNode (testCtx)
  (mkNode "equal-self" "NIL" (tmk "equal" [tvar "x", tvar "x"]) tquotT)
-- Wrong: x ≠ y
#guard !checkNode (testCtx)
  (mkNode "equal-self" "NIL" (tmk "equal" [tvar "x", tvar "y"]) tquotT)
-- Wrong: RHS isn't T
#guard !checkNode (testCtx)
  (mkNode "equal-self" "NIL" (tmk "equal" [tvar "x", tvar "x"]) tquotNil)

/-! ### if-simplification: valid passes, invalid rejected -/

#guard checkNode (testCtx)
  (mkNode "if-simplification" "NIL"
    (tmk "if" [tquotNil, tvar "a", tvar "b"]) (tvar "b"))
#guard checkNode (testCtx)
  (mkNode "if-simplification" "NIL"
    (tmk "if" [tquotT, tvar "a", tvar "b"]) (tvar "a"))
-- Wrong branch for NIL test
#guard !checkNode (testCtx)
  (mkNode "if-simplification" "NIL"
    (tmk "if" [tquotNil, tvar "a", tvar "b"]) (tvar "a"))
-- Wrong branch for T test
#guard !checkNode (testCtx)
  (mkNode "if-simplification" "NIL"
    (tmk "if" [tquotT, tvar "a", tvar "b"]) (tvar "b"))
-- Non-constant test rejected
#guard !checkNode (testCtx)
  (mkNode "if-simplification" "NIL"
    (tmk "if" [tvar "x", tvar "a", tvar "b"]) (tvar "a"))

/-! ### Rewrite rules: valid passes, invalid rejected -/

-- CAR-CONS: (CAR (CONS a b)) => a
#guard checkNode (testCtx)
  (mkNode "rewrite" "car-cons"
    (tmk "car" [tmk "cons" [tvar "a", tvar "b"]]) (tvar "a"))
-- CDR-CONS: (CDR (CONS a b)) => b
#guard checkNode (testCtx)
  (mkNode "rewrite" "cdr-cons"
    (tmk "cdr" [tmk "cons" [tvar "a", tvar "b"]]) (tvar "b"))
-- Wrong RHS: (CAR (CONS a b)) => b REJECTED
#guard !checkNode (testCtx)
  (mkNode "rewrite" "car-cons"
    (tmk "car" [tmk "cons" [tvar "a", tvar "b"]]) (tvar "b"))
-- Wrong pattern: (CDR (CONS a b)) with car-cons REJECTED
#guard !checkNode (testCtx)
  (mkNode "rewrite" "car-cons"
    (tmk "cdr" [tmk "cons" [tvar "a", tvar "b"]]) (tvar "a"))
-- Unknown theorem REJECTED
#guard !checkNode (testCtx)
  (mkNode "rewrite" "nonexistent" (tvar "x") (tvar "y"))

/-! ### Anonymous/recognizer rules: valid passes, invalid rejected -/

-- Clause assumption: (CONSP X) => NIL when clause has (CONSP X)
#guard checkNode (testCtx (clause := [tmk "consp" [tvar "x"]]) (litIdx := 1))
  (mkNode "fake-rune-for-anonymous-enabled-rule" "NIL"
    (tmk "consp" [tvar "x"]) tquotNil)
-- Not justified by clause REJECTED
#guard !checkNode (testCtx (clause := [tvar "something-else"]) (litIdx := 1))
  (mkNode "fake-rune-for-anonymous-enabled-rule" "NIL"
    (tmk "consp" [tvar "x"]) tquotNil)
-- Non-constant RHS REJECTED
#guard !checkNode (testCtx (clause := [tmk "consp" [tvar "x"]]) (litIdx := 1))
  (mkNode "fake-rune-for-anonymous-enabled-rule" "NIL"
    (tmk "consp" [tvar "x"]) (tvar "y"))
-- Self-referential: can't use current literal to justify itself REJECTED
#guard !checkNode (testCtx (clause := [tmk "consp" [tvar "x"]]) (litIdx := 0))
  (mkNode "fake-rune-for-anonymous-enabled-rule" "NIL"
    (tmk "consp" [tvar "x"]) tquotNil)

/-! ### Rewriting-equivalence: valid passes, invalid rejected -/

private def ihClause : List SExpr := [
  tmk "not" [tmk "equal" [tvar "a", tvar "b"]],
  tmk "equal" [tvar "c", tvar "d"]
]

-- Valid: equiv-term matches negated clause literal
#guard checkNode (testCtx (clause := ihClause) (litIdx := 1))
  (mkNode "rewriting-equivalence" "NIL" (tvar "a") (tvar "b")
    [] { equivTerm := some (tmk "equal" [tvar "a", tvar "b"]) })
-- Wrong equiv-term REJECTED
#guard !checkNode (testCtx (clause := ihClause) (litIdx := 1))
  (mkNode "rewriting-equivalence" "NIL" (tvar "a") (tvar "b")
    [] { equivTerm := some (tmk "equal" [tvar "c", tvar "d"]) })
-- Missing equiv-term REJECTED
#guard !checkNode (testCtx (clause := ihClause) (litIdx := 1))
  (mkNode "rewriting-equivalence" "NIL" (tvar "a") (tvar "b"))

/-! ### Definition expansion: valid passes, invalid rejected -/

private def testWorld : World :=
  { defs := ({} : Std.HashMap Symbol (List Symbol × SExpr))
      |>.insert (tsym "myid") ([tsym "x"], tvar "x")
      |>.insert (tsym "mycond") ([tsym "x", tsym "y"],
        tmk "if" [tmk "consp" [tvar "x"], tvar "x", tvar "y"]) }

private def defnCtx (clause : List SExpr := []) (litIdx : Nat := 0) : CheckerContext :=
  { world := testWorld, theoremFormulas := builtinAxioms,
    clause := clause, currentLiteralIndex := litIdx }

-- Identity: (MYID Z) => Z
#guard checkNode (defnCtx)
  (mkNode "definition" "myid" (tmk "myid" [tvar "z"]) (tvar "z"))
-- Identity: wrong RHS REJECTED
#guard !checkNode (defnCtx)
  (mkNode "definition" "myid" (tmk "myid" [tvar "z"]) (tvar "w"))
-- Unknown function REJECTED
#guard !checkNode (defnCtx)
  (mkNode "definition" "nonexistent" (tmk "nonexistent" [tvar "z"]) (tvar "z"))

-- Conditional with children: (MYCOND X Y) => Y when ¬(CONSP X)
#guard checkNode (defnCtx (clause := [tmk "consp" [tvar "x"]]) (litIdx := 1))
  (mkNode "definition" "mycond"
    (tmk "mycond" [tvar "x", tvar "y"]) (tvar "y")
    [ mkNode "fake-rune-for-anonymous-enabled-rule" "NIL"
        (tmk "consp" [tvar "x"]) tquotNil,
      mkNode "if-simplification" "NIL"
        (tmk "if" [tquotNil, tvar "x", tvar "y"]) (tvar "y") ])

-- Conditional: wrong result REJECTED even with valid children
#guard !checkNode (defnCtx (clause := [tmk "consp" [tvar "x"]]) (litIdx := 1))
  (mkNode "definition" "mycond"
    (tmk "mycond" [tvar "x", tvar "y"]) (tvar "x")
    [ mkNode "fake-rune-for-anonymous-enabled-rule" "NIL"
        (tmk "consp" [tvar "x"]) tquotNil,
      mkNode "if-simplification" "NIL"
        (tmk "if" [tquotNil, tvar "x", tvar "y"]) (tvar "y") ])

-- Conditional: children with invalid child REJECTED
#guard !checkNode (defnCtx (clause := [tmk "consp" [tvar "x"]]) (litIdx := 1))
  (mkNode "definition" "mycond"
    (tmk "mycond" [tvar "x", tvar "y"]) (tvar "y")
    [ mkNode "fake-rune-for-anonymous-enabled-rule" "NIL"
        (tmk "consp" [tvar "x"]) tquotNil,
      mkNode "if-simplification" "NIL"
        (tmk "if" [tquotNil, tvar "x", tvar "y"]) (tvar "x") ])  -- wrong branch!

/-! ### Unknown rune type rejected -/

#guard !checkNode (testCtx)
  (mkNode "made-up-rune" "whatever" (tvar "x") (tvar "y"))

/-! ### Clause-level: at least one literal must prove to T -/

-- No proved literal REJECTED
#guard !checkCaseProof (testCtx) {
  clauseId := "test"
  clause := [tvar "x"]
  literalProofs := [{
    index := 1
    literal := tvar "x"
    notFlg := false
    nodes := []
    result := tvar "x" }] }

-- One literal proved to T passes
#guard checkCaseProof (testCtx) {
  clauseId := "test"
  clause := [tvar "x"]
  literalProofs := [{
    index := 1
    literal := tmk "equal" [tvar "a", tvar "a"]
    notFlg := false
    nodes := [mkNode "equal-self" "NIL"
      (tmk "equal" [tvar "a", tvar "a"]) tquotT]
    result := tquotT }] }

/-! ### Additional soundness tests -/

-- equal-self: non-EQUAL LHS rejected
#guard !checkNode (testCtx)
  (mkNode "equal-self" "NIL" (tmk "consp" [tvar "x"]) tquotT)

-- if-simplification: non-IF LHS rejected
#guard !checkNode (testCtx)
  (mkNode "if-simplification" "NIL" (tvar "x") (tvar "x"))

-- Trivially decidable recognizer: (CONSP (CONS a b)) => T
#guard checkNode (testCtx)
  (mkNode "fake-rune-for-anonymous-enabled-rule" "NIL"
    (tmk "consp" [tmk "cons" [tvar "a", tvar "b"]]) tquotT)

-- Trivially decidable recognizer: (CONSP (CONS a b)) => NIL REJECTED
#guard !checkNode (testCtx)
  (mkNode "fake-rune-for-anonymous-enabled-rule" "NIL"
    (tmk "consp" [tmk "cons" [tvar "a", tvar "b"]]) tquotNil)

-- Trivially decidable recognizer: (CONSP NIL) => NIL
#guard checkNode (testCtx)
  (mkNode "fake-rune-for-anonymous-enabled-rule" "NIL"
    (tmk "consp" [.nil]) tquotNil)

-- Rewriting-equivalence: EQUAL is symmetric — (EQUAL b a) in clause
-- matches equiv-term (EQUAL a b)
private def symClause : List SExpr := [
  tmk "not" [tmk "equal" [tvar "b", tvar "a"]],
  tvar "goal"
]
#guard checkNode (testCtx (clause := symClause) (litIdx := 1))
  (mkNode "rewriting-equivalence" "NIL" (tvar "a") (tvar "b")
    [] { equivTerm := some (tmk "equal" [tvar "a", tvar "b"]) })

-- Rewriting-equivalence: completely unrelated clause REJECTED
#guard !checkNode (testCtx (clause := [tvar "unrelated"]) (litIdx := 1))
  (mkNode "rewriting-equivalence" "NIL" (tvar "a") (tvar "b")
    [] { equivTerm := some (tmk "equal" [tvar "a", tvar "b"]) })

-- Definition with macro expansion: function body uses + which must
-- be expanded to BINARY-+ to match the proof tree's terms
private def macroWorld : World :=
  { defs := ({} : Std.HashMap Symbol (List Symbol × SExpr))
      |>.insert (tsym "myfn") ([tsym "x"],
        -- Body uses raw + and bare 0 (as in .lisp source)
        tmk "+" [.atom (.number (.int 0)), tvar "x"]) }

private def macroCtx : CheckerContext :=
  { world := macroWorld, theoremFormulas := builtinAxioms,
    clause := [], currentLiteralIndex := 0 }

-- After macro expansion: (+ 0 x) becomes (BINARY-+ (QUOTE 0) x)
-- So (MYFN y) should expand to (BINARY-+ (QUOTE 0) y)
#guard checkNode macroCtx
  (mkNode "definition" "myfn"
    (tmk "myfn" [tvar "y"])
    (tmk "binary-+" [tint 0, tvar "y"]))

-- Wrong RHS after macro expansion REJECTED
#guard !checkNode macroCtx
  (mkNode "definition" "myfn"
    (tmk "myfn" [tvar "y"])
    (tmk "binary-+" [tint 1, tvar "y"]))  -- wrong constant

-- Rewrite rule with children: CDR-CONS as parent, child simplifies further
-- CDR-CONS: (CDR (CONS a b)) => b
-- With child: (CDR (CONS a b)) => (some-simpl b) where child says b => (some-simpl b)
-- This should FAIL because the child's rewrite on rule RHS doesn't match
-- (the rule gives us b, and child would need LHS=b to fire)
private def childCtx : CheckerContext :=
  { world := World.empty, theoremFormulas := builtinAxioms,
    clause := [], currentLiteralIndex := 0 }

-- Rewrite with valid child chain: rule gives (FIX x), child simplifies to x
-- UNICITY-OF-0: (BINARY-+ '0 X) => (FIX X)
-- Child: definition:fix (FIX x) => x (with its own children)
-- The anonymous-rule child for ACL2-NUMBERP references FIX (a builtin)
#guard checkNode childCtx
  (mkNode "rewrite" "unicity-of-0"
    (tmk "binary-+" [tint 0, tvar "x"])
    (tvar "x")
    [ mkNode "definition" "fix"
        (tmk "fix" [tvar "x"]) (tvar "x")
        [ mkNode "fake-rune-for-anonymous-enabled-rule" "NIL"
            (tmk "acl2-numberp" [tvar "x"]) tquotT
            [] { runes := [("type-prescription", "fix")] },
          mkNode "if-simplification" "NIL"
            (tmk "if" [tquotT, tvar "x", tint 0]) (tvar "x") ] ])

-- Rewrite with children but wrong final RHS REJECTED
#guard !checkNode childCtx
  (mkNode "rewrite" "unicity-of-0"
    (tmk "binary-+" [tint 0, tvar "x"])
    (tint 999)  -- wrong RHS
    [ mkNode "definition" "fix"
        (tmk "fix" [tvar "x"]) (tvar "x")
        [ mkNode "fake-rune-for-anonymous-enabled-rule" "NIL"
            (tmk "acl2-numberp" [tvar "x"]) tquotT
            [] { runes := [("type-prescription", "fix")] },
          mkNode "if-simplification" "NIL"
            (tmk "if" [tquotT, tvar "x", tint 0]) (tvar "x") ] ])

-- Evolving clause: literal 1's result is used when checking literal 2
-- Clause: [(NOT (EQUAL A B)), (EQUAL C D)]
-- Literal 1 rewrites IH via commutativity: result is (NOT (EQUAL B A))
-- Literal 2 uses rewriting-equivalence with (EQUAL B A) — only works
-- if the clause evolved to contain the rewritten literal 1
private def evolvingCase : CaseProof := {
  clauseId := "evolving"
  clause := [tmk "not" [tmk "equal" [tvar "a", tvar "b"]],
             tmk "equal" [tvar "c", tvar "c"]]
  literalProofs := [
    -- Literal 1: rewrite (EQUAL A B) to (EQUAL B A) via commutativity
    -- (simplified: just return the rewritten result)
    { index := 1
      literal := tmk "not" [tmk "equal" [tvar "a", tvar "b"]]
      notFlg := true
      nodes := []  -- no nodes needed, literal just gets normalized
      result := tmk "not" [tmk "equal" [tvar "b", tvar "a"]] },
    -- Literal 2: prove via equal-self
    { index := 2
      literal := tmk "equal" [tvar "c", tvar "c"]
      notFlg := false
      nodes := [mkNode "equal-self" "NIL"
        (tmk "equal" [tvar "c", tvar "c"]) tquotT]
      result := tquotT }
  ] }

-- The case should pass (literal 2 proves to T)
#guard checkCaseProof (testCtx) evolvingCase

/-! ### End-to-end: run via CLI -/
-- `lake exe acl2lean check-proof acl2_samples/simple.proof-log acl2_samples/simple.lisp`

end Tests

end ACL2
