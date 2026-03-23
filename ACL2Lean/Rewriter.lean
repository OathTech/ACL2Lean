/-
  Rewriter core: applies ACL2 proof trace steps to SExpr terms.

  The key operation is subterm replacement guided by the proof trace.
  Each REWRITE-STEP in the trace gives an exact LHS and RHS. We find
  the LHS in the current term and replace it with the RHS.

  Steps whose LHS doesn't appear in the current term are intermediate
  rewrites internal to ACL2's rewriter (e.g., simplifications applied
  to the RHS of a rewrite rule). These are safely skipped because the
  outermost step's RHS already incorporates the intermediate results.
-/
import ACL2Lean.Syntax
import ACL2Lean.ProofLog
import ACL2Lean.Eval
import ACL2Lean.Parser

namespace ACL2

namespace Rewriter

/-- Find and replace the first occurrence of `pattern` in `term`
    (left-to-right, depth-first).
    Returns `some newTerm` if pattern was found, `none` otherwise. -/
def replaceFirstOpt (term pattern replacement : SExpr) : Option SExpr :=
  if term == pattern then some replacement
  else match term with
  | .cons a b =>
      match replaceFirstOpt a pattern replacement with
      | some a' => some (.cons a' b)
      | none =>
        match replaceFirstOpt b pattern replacement with
        | some b' => some (.cons a b')
        | none => none
  | _ => none

/-- Find and replace the first occurrence of `pattern` in `term`.
    Returns the original term unchanged if `pattern` is not found. -/
def replaceFirst (term pattern replacement : SExpr) : SExpr :=
  (replaceFirstOpt term pattern replacement).getD term

/-- Check whether `pattern` occurs as a subterm of `term`. -/
def containsSubterm (term pattern : SExpr) : Bool :=
  if term == pattern then true
  else match term with
  | .cons a b => containsSubterm a pattern || containsSubterm b pattern
  | _ => false

/-- Apply a single rewrite step: find LHS in term, replace with RHS.
    If LHS is not found (intermediate ACL2 rewrite), term is unchanged. -/
def applyRewriteStep (step : RewriteStep) (term : SExpr) : SExpr :=
  replaceFirst term step.lhs step.rhs

/-- Apply a sequence of rewrite steps to a term.
    Steps whose LHS is not found in the current term are skipped. -/
def applyRewriteSteps (steps : List RewriteStep) (term : SExpr) : SExpr :=
  steps.foldl (fun t s => applyRewriteStep s t) term

/-- Replace all occurrences of `pattern` with `replacement` in `term`. -/
def replaceAll (term pattern replacement : SExpr) : SExpr :=
  if term == pattern then replacement
  else match term with
  | .cons a b => .cons (replaceAll a pattern replacement) (replaceAll b pattern replacement)
  | _ => term

/-- Apply context substitutions from trace events to a term.
    BRANCH-SUBSTITUTION events come from remove-trivial-equivalences.
    CONTEXT-SUBST events come from IF branch processing where an equality
    is known (e.g., from (equal x1 a) in a branch, substitute x1→a).
    Both are applied via replaceAll (they hold for all occurrences). -/
def applyContextSubstitutions (events : List TraceEvent) (term : SExpr) : SExpr :=
  events.foldl (fun t ev =>
    match ev with
    | .branchSubstitution _equiv lhs rhs => replaceAll t lhs rhs
    | .contextSubst var value _justification => replaceAll t var value
    | _ => t) term

/-- Apply a full literal rewrite: first apply context substitutions
    (from branch assumptions and IF-equality resolution), then apply
    per-literal rewrite steps. -/
def rewriteLiteral (contextEvents : List TraceEvent) (literalSteps : List RewriteStep)
    (term : SExpr) : SExpr :=
  let substituted := applyContextSubstitutions contextEvents term
  applyRewriteSteps literalSteps substituted

end Rewriter

/-! ## Tests -/

section Tests

open Rewriter

private def sym (name : String) : Symbol := ⟨"ACL2", name⟩

private def mkCall (name : String) (args : List SExpr) : SExpr :=
  .cons (.atom (.symbol (sym name))) (SExpr.ofList args)

private def mkVar (name : String) : SExpr := .atom (.symbol (sym name))

-- Helper: build the test world (same as in Eval.lean)
private def myLenBody : SExpr :=
  mkCall "if" [mkCall "consp" [mkVar "x"],
               mkCall "+" [.atom (.number (.int 1)),
                           mkCall "my-len" [mkCall "cdr" [mkVar "x"]]],
               .atom (.number (.int 0))]

private def myAppBody : SExpr :=
  mkCall "if" [mkCall "consp" [mkVar "x"],
               mkCall "cons" [mkCall "car" [mkVar "x"],
                              mkCall "my-app" [mkCall "cdr" [mkVar "x"], mkVar "y"]],
               mkVar "y"]

private def simpleWorld : World :=
  { defs := ({} : Std.HashMap Symbol (List Symbol × SExpr))
      |>.insert (sym "my-len") ([sym "x"], myLenBody)
      |>.insert (sym "my-app") ([sym "x", sym "y"], myAppBody) }

-- Helper: quote a value (produces the SExpr for 'val)
private def quoted (v : SExpr) : SExpr :=
  mkCall "quote" [v]

/-! ### Basic replaceFirst tests -/

-- Replace a simple subterm
#guard replaceFirst (mkCall "f" [mkVar "x"]) (mkVar "x") (mkVar "y")
    == mkCall "f" [mkVar "y"]

-- Replace in nested position
#guard replaceFirst (mkCall "f" [mkCall "g" [mkVar "x"]]) (mkVar "x") (mkVar "y")
    == mkCall "f" [mkCall "g" [mkVar "y"]]

-- Pattern not found — returns original
#guard replaceFirst (mkCall "f" [mkVar "x"]) (mkVar "z") (mkVar "y")
    == mkCall "f" [mkVar "x"]

-- Replace whole term
#guard replaceFirst (mkVar "x") (mkVar "x") (mkVar "y") == mkVar "y"

-- Replace first occurrence only (left-to-right)
#guard replaceFirst (mkCall "f" [mkVar "x", mkVar "x"]) (mkVar "x") (mkVar "y")
    == mkCall "f" [mkVar "y", mkVar "x"]

/-! ### Base case rewrite steps -/

-- Base case literal: (EQUAL (MY-LEN (MY-APP X Y)) (BINARY-+ (MY-LEN X) (MY-LEN Y)))
private def baseLit : SExpr :=
  mkCall "equal" [mkCall "my-len" [mkCall "my-app" [mkVar "x", mkVar "y"]],
                  mkCall "binary-+" [mkCall "my-len" [mkVar "x"],
                                     mkCall "my-len" [mkVar "y"]]]

-- Steps from the proof trace (base case, ¬CONSP X):
-- 1. MY-APP unfolds to Y (since ¬CONSP X, else branch)
-- 2. MY-LEN X unfolds to 0 (since ¬CONSP X, else branch)
-- 3. FIX (MY-LEN Y) → MY-LEN Y  [intermediate, will be skipped]
-- 4. (BINARY-+ 0 (MY-LEN Y)) → (MY-LEN Y)  via UNICITY-OF-0
private def baseSteps : List RewriteStep := [
  ⟨("definition", "my-app"), mkCall "my-app" [mkVar "x", mkVar "y"], mkVar "y"⟩,
  ⟨("definition", "my-len"), mkCall "my-len" [mkVar "x"], quoted (.atom (.number (.int 0)))⟩,
  ⟨("definition", "fix"), mkCall "fix" [mkCall "my-len" [mkVar "y"]], mkCall "my-len" [mkVar "y"]⟩,
  ⟨("rewrite", "unicity-of-0"),
    mkCall "binary-+" [quoted (.atom (.number (.int 0))), mkCall "my-len" [mkVar "y"]],
    mkCall "my-len" [mkVar "y"]⟩
]

-- After rewriting: (EQUAL (MY-LEN Y) (MY-LEN Y))
private def expectedBase : SExpr :=
  mkCall "equal" [mkCall "my-len" [mkVar "y"], mkCall "my-len" [mkVar "y"]]

#guard applyRewriteSteps baseSteps baseLit == expectedBase

-- The rewritten term evaluates to T for any Y
private def envNilNil : Env :=
  ({} : Env).insert (sym "x") .nil |>.insert (sym "y") .nil

#guard eval 100 simpleWorld envNilNil (applyRewriteSteps baseSteps baseLit) == SExpr.t

-- Also works for non-trivial Y
private def envNilList : Env :=
  ({} : Env).insert (sym "x") .nil
    |>.insert (sym "y") (.cons (.atom (.symbol (sym "a"))) .nil)

#guard eval 100 simpleWorld envNilList (applyRewriteSteps baseSteps baseLit) == SExpr.t

/-! ### Inductive case rewrite steps -/

-- Inductive case literal 3: same starting term as base case
-- Steps (from the trace, literal 3 only):
-- 1. MY-APP X Y → (CONS (CAR X) (MY-APP (CDR X) Y))
-- 2. (CDR (CONS (CAR X) (MY-APP (CDR X) Y))) → (MY-APP (CDR X) Y) [intermediate]
-- 3. (MY-LEN (CONS (CAR X) (MY-APP (CDR X) Y))) → (BINARY-+ '1 (MY-LEN (MY-APP (CDR X) Y)))
-- 4. (MY-LEN X) → (BINARY-+ '1 (MY-LEN (CDR X)))
-- 5. COMMUTATIVITY-2-OF-+: intermediate, skipped
-- 6. COMMUTATIVITY-OF-+: (BINARY-+ (BINARY-+ '1 (MY-LEN (CDR X))) (MY-LEN Y))
--    → (BINARY-+ '1 (MY-LEN (MY-APP (CDR X) Y)))
private def stepSteps : List RewriteStep := [
  ⟨("definition", "my-app"),
    mkCall "my-app" [mkVar "x", mkVar "y"],
    mkCall "cons" [mkCall "car" [mkVar "x"],
                   mkCall "my-app" [mkCall "cdr" [mkVar "x"], mkVar "y"]]⟩,
  ⟨("rewrite", "cdr-cons"),
    mkCall "cdr" [mkCall "cons" [mkCall "car" [mkVar "x"],
                                 mkCall "my-app" [mkCall "cdr" [mkVar "x"], mkVar "y"]]],
    mkCall "my-app" [mkCall "cdr" [mkVar "x"], mkVar "y"]⟩,
  ⟨("definition", "my-len"),
    mkCall "my-len" [mkCall "cons" [mkCall "car" [mkVar "x"],
                                    mkCall "my-app" [mkCall "cdr" [mkVar "x"], mkVar "y"]]],
    mkCall "binary-+" [quoted (.atom (.number (.int 1))),
                       mkCall "my-len" [mkCall "my-app" [mkCall "cdr" [mkVar "x"], mkVar "y"]]]⟩,
  ⟨("definition", "my-len"),
    mkCall "my-len" [mkVar "x"],
    mkCall "binary-+" [quoted (.atom (.number (.int 1))),
                       mkCall "my-len" [mkCall "cdr" [mkVar "x"]]]⟩,
  -- COMMUTATIVITY-2: intermediate (LHS not in term), skipped
  ⟨("rewrite", "commutativity-2-of-+"),
    mkCall "binary-+" [mkCall "my-len" [mkVar "y"],
                       mkCall "binary-+" [quoted (.atom (.number (.int 1))),
                                          mkCall "my-len" [mkCall "cdr" [mkVar "x"]]]],
    mkCall "binary-+" [quoted (.atom (.number (.int 1))),
                       mkCall "my-len" [mkCall "my-app" [mkCall "cdr" [mkVar "x"], mkVar "y"]]]⟩,
  -- COMMUTATIVITY: the actual outermost rewrite
  ⟨("rewrite", "commutativity-of-+"),
    mkCall "binary-+" [mkCall "binary-+" [quoted (.atom (.number (.int 1))),
                                          mkCall "my-len" [mkCall "cdr" [mkVar "x"]]],
                       mkCall "my-len" [mkVar "y"]],
    mkCall "binary-+" [quoted (.atom (.number (.int 1))),
                       mkCall "my-len" [mkCall "my-app" [mkCall "cdr" [mkVar "x"], mkVar "y"]]]⟩
]

-- After rewriting: (EQUAL (BINARY-+ '1 (MY-LEN (MY-APP (CDR X) Y)))
--                         (BINARY-+ '1 (MY-LEN (MY-APP (CDR X) Y))))
private def expectedStep : SExpr :=
  let inner := mkCall "binary-+" [quoted (.atom (.number (.int 1))),
                                   mkCall "my-len" [mkCall "my-app" [mkCall "cdr" [mkVar "x"], mkVar "y"]]]
  mkCall "equal" [inner, inner]

#guard applyRewriteSteps stepSteps baseLit == expectedStep

-- The rewritten term evaluates to T for a concrete cons value
private def envConsList : Env :=
  ({} : Env).insert (sym "x") (.cons (.atom (.number (.int 1))) .nil)
    |>.insert (sym "y") .nil

#guard eval 200 simpleWorld envConsList (applyRewriteSteps stepSteps baseLit) == SExpr.t

/-! ### Edge cases -/

-- Empty step list is identity
#guard applyRewriteSteps [] (mkVar "x") == mkVar "x"
#guard applyRewriteSteps [] baseLit == baseLit

-- Replacing nil itself
#guard replaceFirst (.cons .nil .nil) .nil (mkVar "y")
    == .cons (mkVar "y") .nil

-- replaceFirstOpt returns none when not found
#guard replaceFirstOpt (mkCall "f" [mkVar "x"]) (mkVar "z") (mkVar "y") == none

-- replaceFirstOpt returns some when found
#guard (replaceFirstOpt (mkCall "f" [mkVar "x"]) (mkVar "x") (mkVar "y")).isSome

-- containsSubterm
#guard containsSubterm (mkCall "f" [mkCall "g" [mkVar "x"]]) (mkVar "x") == true
#guard containsSubterm (mkCall "f" [mkVar "y"]) (mkVar "x") == false
#guard containsSubterm .nil .nil == true

-- Three-level nesting
#guard replaceFirst
    (mkCall "f" [mkCall "g" [mkCall "h" [mkVar "x"]]])
    (mkVar "x") (mkVar "z")
  == mkCall "f" [mkCall "g" [mkCall "h" [mkVar "z"]]]

-- Step with no match is no-op
private def noopStep : RewriteStep := ⟨("rewrite", "foo"), mkVar "nonexistent", mkVar "y"⟩
#guard applyRewriteStep noopStep baseLit == baseLit

/-! ### End-to-end: parsed proof trace → rewriter -/

-- Parse the real proof log at compile time
private def proofLogText : String := include_str "../acl2_samples/simple.proof-log"

private def getStepsForClause (clauseId : String) : List RewriteStep := Id.run do
  let .ok log := ProofLog.parse proofLogText | return []
  let steps := log.events.filterMap fun
    | ProofEvent.step s => some s
    | _ => none
  for (s : ProofStep) in steps do
    if s.clauseId == clauseId then return s.rewriteSteps
  return []

-- Extract the EQUAL literal from the base case input clause
private def formulaFromLog : SExpr := Id.run do
  let .ok log := ProofLog.parse proofLogText | return .nil
  let steps := log.events.filterMap fun
    | ProofEvent.step s => some s
    | _ => none
  for (s : ProofStep) in steps do
    if s.clauseId == "Subgoal *1/2" then
      for lit in s.inputClause do
        match lit with
        | .cons (.atom (.symbol head)) _ =>
          if head.isNamed "equal" then return lit
        | _ => pure ()
  return .nil

-- Helper: check if result is (EQUAL a a) for some a
private def isEqualSelf : SExpr → Bool
  | .cons (.atom (.symbol eq)) (.cons a (.cons b .nil)) => eq.isNamed "equal" && a == b
  | _ => false

-- Base case: parsed trace steps reduce formula to (EQUAL X X)
#guard isEqualSelf (applyRewriteSteps (getStepsForClause "Subgoal *1/2") formulaFromLog)

-- Inductive case: drop literal-2 step, remaining steps reduce formula to (EQUAL X X)
#guard isEqualSelf (applyRewriteSteps ((getStepsForClause "Subgoal *1/1").drop 1) formulaFromLog)

-- Verify the parsed steps match our hand-constructed base case steps
#guard (getStepsForClause "Subgoal *1/2").length == 4
#guard (getStepsForClause "Subgoal *1/1").length == 7

-- Verify parsed base case result matches hand-constructed result
#guard applyRewriteSteps (getStepsForClause "Subgoal *1/2") formulaFromLog == expectedBase

end Tests

end ACL2
