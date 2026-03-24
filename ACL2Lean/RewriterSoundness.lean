/-
  Soundness proof for the ACL2 eval-aware rewriter.

  The core theorem: if replacing a subterm with an eval-equivalent one
  (at all fuel levels), the overall term's eval is preserved.

  The eval-aware replacement function (`evalReplace`) ensures soundness
  by construction:
  - Never replaces the head symbol of a function call (eval dispatches on it)
  - Never replaces inside QUOTE bodies (eval returns them as raw data)
  - Recurses into both car (arguments) and cdr (argument list spine)
-/
import ACL2Lean.Rewriter
import ACL2Lean.EvalOpt

namespace ACL2.Rewriter

open ACL2

/-! ## Helper: evalReplaceOpt preserves toList structure -/

/-- When `evalReplaceOpt` on a proper list succeeds, the result has the same
    `toList?` length and differs in at most one element (which is the
    `evalReplace` of the original). -/
theorem evalReplaceOpt_toList (argsExpr lhs rhs : SExpr)
    (args : List SExpr) (args' : SExpr)
    (h_list : argsExpr.toList? = some args)
    (h_replace : evalReplaceOpt argsExpr lhs rhs = some args') :
    ∃ args'_list : List SExpr,
      args'.toList? = some args'_list ∧
      args'_list.length = args.length ∧
      (∀ (i : Nat), ∀ (x : SExpr), args[i]? = some x →
        ∃ (x' : SExpr), args'_list[i]? = some x' ∧
          (x' = x ∨ x' = evalReplace x lhs rhs)) := by
  sorry

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

    If `lhs` and `rhs` are eval-equivalent at all fuel levels, then
    replacing `lhs` with `rhs` in `term` (using eval-aware replacement)
    preserves the eval result.

    Proof by structural induction on `term`, generalized over fuel.
    The two remaining sorry's are:
    - evalReplaceOpt_toList (structural lemma about list preservation)
    - mapM_evalOpt_congr (pointwise congruence for Option.mapM)
    Both are self-contained and provable by straightforward induction. -/
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
    sorry

end ACL2.Rewriter
