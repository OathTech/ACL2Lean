import ACL2Lean.EvalOpt

namespace ACL2.Replay
open ACL2

/-- Literal values handled directly by evalOptStep, without a variable
lookup or application. Internal clause construction also contains bare
keyword literals, unlike ordinary translated quoted constants. -/
def selfEvaluatingLiteral : SExpr → Bool
  | .nil | .atom (.number _) | .atom (.string _) | .atom (.keyword _) | .atom (.char _) => true
  | .atom (.symbol _) | .cons _ _ => false

theorem re_val_selfEvaluating (w : World) (env : Env) (t : SExpr)
    (h : selfEvaluatingLiteral t = true) :
    ∃ N, ∀ f ≥ N, evalOpt f w env t = some t := by
  refine ⟨1, ?_⟩
  intro f hf
  cases f with
  | zero => simp at hf
  | succ n =>
    cases t with
    | nil => rfl
    | cons a d => simp [selfEvaluatingLiteral] at h
    | atom a => cases a <;> simp_all [selfEvaluatingLiteral, evalOpt, evalOptStep]

end ACL2.Replay
