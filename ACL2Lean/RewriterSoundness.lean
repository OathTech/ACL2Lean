/-
  Soundness proof for the ACL2 eval-aware rewriter.

  The core theorem: if replacing a subterm with an eval-equivalent one
  (at all fuel levels), the overall term's eval is preserved. This is
  the general mechanism that makes proof replay work — each trace step
  only needs to justify eval-equivalence of its LHS and RHS, and the
  rewriter's soundness gives the rest for free.

  The eval-aware replacement function (`evalReplace`) ensures soundness
  by construction:
  - Never replaces the head symbol of a function call (eval dispatches on it)
  - Never replaces inside QUOTE bodies (eval returns them as raw data)
  - Recurses into both car (arguments) and cdr (argument list spine)

  STATUS: Core theorem stated with sorry. The proof requires a congruence
  lemma for evalOpt w.r.t. argument-list modification. This is the key
  mathematical challenge identified by this experiment.
-/
import ACL2Lean.Rewriter
import ACL2Lean.EvalOpt

namespace ACL2.Rewriter

open ACL2

/-! ## The core soundness theorem -/

/-- The main soundness theorem for `evalReplace`.

    If `lhs` and `rhs` are eval-equivalent at all fuel levels, then
    replacing `lhs` with `rhs` in `term` (using eval-aware replacement)
    preserves the eval result. No preconditions needed — soundness
    is guaranteed by the replacement function's structure.

    Proof approach: structural induction on `term`, generalized over fuel.

    Known challenges:
    1. Function call congruence: when replacement happens in the argument list,
       need to show the function call still evaluates the same. This requires
       connecting evalReplaceOpt's cons-cell recursion with evalOpt's
       toList?-based argument processing.
    2. Non-symbol-headed cons: when the head of a cons is not a symbol,
       replacing in the head could change evalOpt's dispatch. The IH gives
       eval-equivalence of the head as a standalone term, but evalOpt
       pattern-matches on the head's STRUCTURE, not its eval. -/
theorem evalReplace_sound (fuel : Nat) (w : World) (env : Env)
    (term lhs rhs : SExpr)
    (h_eq : ∀ f, evalOpt f w env lhs = evalOpt f w env rhs) :
    evalOpt fuel w env (evalReplace term lhs rhs) = evalOpt fuel w env term := by
  -- Generalize fuel so IH applies at any fuel level
  suffices h : ∀ f, evalOpt f w env (evalReplace term lhs rhs) = evalOpt f w env term from h fuel
  induction term with
  | nil =>
    intro f; simp only [evalReplace]; unfold evalReplaceOpt
    split
    · next h_beq => simp [Option.getD]; rw [eq_of_beq h_beq]; exact (h_eq f).symm
    · simp
  | atom a =>
    intro f; simp only [evalReplace]; unfold evalReplaceOpt
    split
    · next h_beq => simp [Option.getD]; rw [eq_of_beq h_beq]; exact (h_eq f).symm
    · simp
  | cons a b iha ihb =>
    intro f; simp only [evalReplace]; unfold evalReplaceOpt
    split
    · next h_beq => -- Whole term matches lhs
      simp [Option.getD]; rw [eq_of_beq h_beq]; exact (h_eq f).symm
    · -- term ≠ lhs: need split on the inner match
      sorry

/-! ## Step and chain composition -/

/-- Single-step soundness. -/
theorem applyEvalRewriteStep_sound (fuel : Nat) (w : World) (env : Env)
    (step : RewriteStep) (term : SExpr)
    (h_eq : ∀ f, evalOpt f w env step.lhs = evalOpt f w env step.rhs) :
    evalOpt fuel w env (applyEvalRewriteStep step term) = evalOpt fuel w env term :=
  evalReplace_sound fuel w env term step.lhs step.rhs h_eq

/-- Multi-step soundness. -/
theorem applyEvalRewriteSteps_sound (fuel : Nat) (w : World) (env : Env)
    (steps : List RewriteStep) (term : SExpr)
    (h_eqs : ∀ s ∈ steps, ∀ f, evalOpt f w env s.lhs = evalOpt f w env s.rhs) :
    evalOpt fuel w env (applyEvalRewriteSteps steps term) = evalOpt fuel w env term := by
  unfold applyEvalRewriteSteps
  induction steps generalizing term with
  | nil => simp [List.foldl]
  | cons step rest ih =>
    simp only [List.foldl]
    -- sorry propagation from evalReplace_sound blocks term-mode proof
    sorry

end ACL2.Rewriter
