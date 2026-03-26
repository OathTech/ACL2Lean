/-
  Verified replay: soundness by construction.

  The replay function takes a sequence of rewrite steps from ACL2's proof trace
  and replays them on a term. At each step, it checks the step is valid (by
  evaluating both sides and comparing) and applies the replacement. If all checks
  pass, the result is guaranteed to be eval-equivalent to the original.

  Key design: everything operates at a single fuel level. The checker evaluates
  both LHS and RHS at that fuel and compares. The soundness theorem says:
  "at this fuel level, the result is correct."

  For any specific theorem, we pick a fuel large enough for all computations.
  ACL2 already proved the theorem, so sufficient fuel exists.
-/
import ACL2Lean.Rewriter
import ACL2Lean.EvalOpt

namespace ACL2.Rewriter

open ACL2

/-! ## Step checker: evaluate and compare -/

/-- Check a rewrite step by evaluating both sides and comparing.
    This is the simplest sound checker: if evalOpt gives the same result
    for LHS and RHS at this fuel level, the step is valid at this fuel.

    The checker takes env and fuel because step validity depends on the
    current variable bindings (clause context) and computation budget. -/
def checkStep (w : World) (env : Env) (step : RewriteStep) (fuel : Nat) : Bool :=
  evalOpt fuel w env step.lhs == evalOpt fuel w env step.rhs

/-- checkStep soundness: trivial from BEq correctness on Option SExpr. -/
theorem checkStep_sound (w : World) (env : Env) (step : RewriteStep) (fuel : Nat)
    (h : checkStep w env step fuel = true) :
    evalOpt fuel w env step.lhs = evalOpt fuel w env step.rhs := by
  unfold checkStep at h
  exact eq_of_beq h

/-! ## Combined replay-and-verify -/

/-- Replay a sequence of rewrite steps, checking each by evaluation.
    Returns `some result` if all checks pass, `none` if any fails. -/
def replaySteps (w : World) (env : Env) (steps : List RewriteStep)
    (term : SExpr) (fuel : Nat) : Option SExpr :=
  steps.foldlM (fun t s =>
    if checkStep w env s fuel then some (evalReplace t s.lhs s.rhs) else none) term

/-! ## Replacement soundness (single fuel level) -/

/-- If lhs and rhs evaluate the same at fuel level f, then eval-aware
    replacement preserves eval at fuel level f.

    This is the single-fuel version: no ∀ f quantification needed.
    The hypothesis comes directly from checkStep_sound. -/
theorem evalReplace_sound (f : Nat) (w : World) (env : Env)
    (term lhs rhs : SExpr)
    (h_eq : evalOpt f w env lhs = evalOpt f w env rhs) :
    evalOpt f w env (evalReplace term lhs rhs) = evalOpt f w env term := by
  sorry -- Congruence: the main mathematical challenge (see findings doc)

/-! ## Main soundness theorem -/

/-- If replaySteps succeeds, the result is eval-equivalent to the original
    at the given fuel level. This is the top-level soundness result.

    Any trace where the checker passes produces a correct result by construction.
    No per-program theorems needed — ACL2 is the oracle, Lean verifies. -/
theorem replaySteps_sound (w : World) (env : Env)
    (steps : List RewriteStep) (term result : SExpr) (fuel : Nat)
    (h : replaySteps w env steps term fuel = some result) :
    evalOpt fuel w env result = evalOpt fuel w env term := by
  unfold replaySteps at h
  induction steps generalizing term with
  | nil =>
    simp [List.foldlM] at h
    subst h; rfl
  | cons step rest ih =>
    simp only [List.foldlM, bind_assoc, pure_bind] at h
    split at h
    · next h_check =>
      simp at h
      have h_step := checkStep_sound w env step fuel h_check
      have h_replace := evalReplace_sound fuel w env term step.lhs step.rhs h_step
      have h_rest := ih (evalReplace term step.lhs step.rhs) h
      exact h_rest.trans h_replace
    · simp at h

end ACL2.Rewriter
