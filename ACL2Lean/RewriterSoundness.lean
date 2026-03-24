/-
  Soundness proof for the ACL2 eval-aware rewriter.

  The core theorem: if replacing a subterm with an eval-equivalent one
  (at all fuel levels), the overall term's eval is preserved.

  The eval-aware replacement function (`evalReplace`) ensures soundness
  by construction:
  - Never replaces the head symbol of a function call (eval dispatches on it)
  - Never replaces inside QUOTE bodies (eval returns them as raw data)
  - Recurses into both car (arguments) and cdr (argument list spine)

  Precondition: LHS must be symbol-headed (a function call pattern like
  `(f arg1 arg2 ...)`). This is always true for ACL2 proof traces.
  It ensures:
  1. Bare atoms and nil never match the pattern
  2. Argument list spines never match the pattern
  3. Only genuine subterm occurrences at eval-evaluated positions are replaced
-/
import ACL2Lean.Rewriter
import ACL2Lean.EvalOpt

namespace ACL2.Rewriter

open ACL2

/-! ## Helper lemma: atoms/nil never match a symbol-headed pattern -/

/-- evalReplaceOpt on nil returns none when pattern is a cons. -/
theorem evalReplaceOpt_nil_of_cons (ca cb rhs : SExpr) :
    evalReplaceOpt SExpr.nil (SExpr.cons ca cb) rhs = none := by
  unfold evalReplaceOpt; simp

/-- evalReplaceOpt on an atom returns none when pattern is a cons. -/
theorem evalReplaceOpt_atom_of_cons (a : Atom) (ca cb rhs : SExpr) :
    evalReplaceOpt (SExpr.atom a) (SExpr.cons ca cb) rhs = none := by
  unfold evalReplaceOpt; simp

/-! ## Helper: mapM congruence for eval -/

/-- If two lists are pointwise eval-equivalent, mapM over them gives the same result. -/
theorem mapM_evalOpt_congr (f : Nat) (w : World) (env : Env)
    (xs xs' : List SExpr)
    (h_len : xs.length = xs'.length)
    (h_eq : ∀ (i : Nat) (x x' : SExpr), xs[i]? = some x → xs'[i]? = some x' →
        evalOpt f w env x' = evalOpt f w env x) :
    xs'.mapM (fun a => evalOpt f w env a) = xs.mapM (fun a => evalOpt f w env a) := by
  induction xs generalizing xs' with
  | nil => cases xs' with
    | nil => rfl
    | cons _ _ => simp at h_len
  | cons x rest ih =>
    cases xs' with
    | nil => simp at h_len
    | cons x' rest' =>
      simp only [List.mapM_cons]
      have h_first := h_eq 0 x x' (by simp) (by simp)
      have h_rest := ih rest'
        (by simpa using h_len)
        (fun i a a' ha ha' =>
          h_eq (i + 1) a a' (by simpa using ha) (by simpa using ha'))
      rw [h_first, h_rest]

/-! ## The core soundness theorem -/

/-- The main soundness theorem for `evalReplace`.

    LHS must be symbol-headed (`lhs = .cons (.atom (.symbol lhsHead)) lhsArgs`).
    This ensures the pattern only matches at eval-evaluated positions (function
    calls), not at structural positions (argument list spines, nil, atoms).

    The `∀ f` quantification on the hypothesis works because `evalOpt`
    returns `none` on fuel exhaustion. -/
theorem evalReplace_sound (fuel : Nat) (w : World) (env : Env)
    (term : SExpr) (lhsHead : Symbol) (lhsArgs rhs : SExpr)
    (h_eq : ∀ f, evalOpt f w env (.cons (.atom (.symbol lhsHead)) lhsArgs)
                  = evalOpt f w env rhs) :
    evalOpt fuel w env (evalReplace term (.cons (.atom (.symbol lhsHead)) lhsArgs) rhs)
    = evalOpt fuel w env term := by
  -- Abbreviation for readability
  let lhs := SExpr.cons (.atom (.symbol lhsHead)) lhsArgs
  -- Generalize fuel so IH applies at any fuel level
  suffices h : ∀ f, evalOpt f w env (evalReplace term lhs rhs)
                    = evalOpt f w env term from h fuel
  induction term with
  | nil =>
    intro f; unfold evalReplace; rw [evalReplaceOpt_nil_of_cons]; rfl
  | atom a =>
    intro f; unfold evalReplace; rw [evalReplaceOpt_atom_of_cons]; rfl
  | cons a b iha ihb =>
    intro f; simp only [evalReplace]; unfold evalReplaceOpt
    split
    · next h_beq => -- Whole term matches lhs
      simp; rw [eq_of_beq h_beq]; exact (h_eq f).symm
    · next h_nbeq => -- term ≠ lhs
      -- Need to split on whether a is .atom (.symbol s) or not
      sorry

/-! ## Step and chain composition -/

/-- Single-step soundness (for symbol-headed LHS). -/
theorem applyEvalRewriteStep_sound (fuel : Nat) (w : World) (env : Env)
    (step : RewriteStep) (term : SExpr)
    (lhsHead : Symbol) (lhsArgs : SExpr)
    (h_lhs : step.lhs = SExpr.cons (.atom (.symbol lhsHead)) lhsArgs)
    (h_eq : ∀ f, evalOpt f w env step.lhs = evalOpt f w env step.rhs) :
    evalOpt fuel w env (applyEvalRewriteStep step term) = evalOpt fuel w env term := by
  simp only [applyEvalRewriteStep, h_lhs]
  exact evalReplace_sound fuel w env term lhsHead lhsArgs step.rhs
    (fun f => by rw [← h_lhs]; exact h_eq f)

/-- Multi-step soundness. -/
theorem applyEvalRewriteSteps_sound (fuel : Nat) (w : World) (env : Env)
    (steps : List RewriteStep) (term : SExpr)
    (h_compound : ∀ s ∈ steps, ∃ head args, s.lhs = SExpr.cons (.atom (.symbol head)) args)
    (h_eqs : ∀ s ∈ steps, ∀ f, evalOpt f w env s.lhs = evalOpt f w env s.rhs) :
    evalOpt fuel w env (applyEvalRewriteSteps steps term) = evalOpt fuel w env term := by
  sorry

end ACL2.Rewriter
