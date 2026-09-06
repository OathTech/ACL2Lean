import ACL2Lean.Replay.Lemmas.Core

/-! Congruence inside an unopened translated LET body. Its proof must hold
in every environment; actuals converge before that environment is bound. -/

namespace ACL2.Replay
open ACL2

theorem evalOpt_congr_lam_body (w : World) (env : Env) (lam : Symbol)
    (formalsE body body' argsE : SExpr) (formals : List Symbol)
    (actuals vals : List SExpr)
    (hlam : lam.isNamed "LAMBDA" = true)
    (hform : lamFormals? formalsE = some formals)
    (hargs : argsE.toList? = some actuals)
    (hlenA : actuals.length = vals.length)
    (hconv : ∀ p ∈ actuals.zip vals, ∃ N, ∀ f ≥ N, evalOpt f w env p.1 = some p.2)
    (hbody : ∀ env', ∃ N, ∀ f ≥ N, evalOpt f w env' body = evalOpt f w env' body') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.cons (.atom (.symbol lam))
        (.cons formalsE (.cons body .nil))) argsE) =
      evalOpt f w env (.cons (.cons (.atom (.symbol lam))
        (.cons formalsE (.cons body' .nil))) argsE) := by
  obtain ⟨Nm, hm⟩ := mapM_conv_of_zip w env actuals vals hlenA hconv
  obtain ⟨Nb, hb⟩ := hbody (bindArgsOver env formals vals)
  refine ⟨max Nm Nb + 1, fun f hf => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
  change evalOptStep (evalOpt m) w env _ = evalOptStep (evalOpt m) w env _
  simp only [evalOptStep_cons_lam, hlam, if_true, hform, hargs]
  rw [hm m (by omega)]
  change (if formals.length = vals.length then
    evalOpt m w (bindArgsOver env formals vals) body else none) =
    (if formals.length = vals.length then
    evalOpt m w (bindArgsOver env formals vals) body' else none)
  split
  · exact hb m (by omega)
  · rfl

theorem re_lam_body1_eq (w : World) (env : Env) (lam : Symbol)
    (formalsE body body' a : SExpr) (lf : Symbol)
    (hlam : lam.isNamed "LAMBDA" = true)
    (hform : lamFormals? formalsE = some [lf])
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av)
    (hbody : ∀ env', ∃ N, ∀ f ≥ N, evalOpt f w env' body = evalOpt f w env' body') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.cons (.atom (.symbol lam))
        (.cons formalsE (.cons body .nil))) (.cons a .nil)) =
      evalOpt f w env (.cons (.cons (.atom (.symbol lam))
        (.cons formalsE (.cons body' .nil))) (.cons a .nil)) := by
  obtain ⟨Na, av, ha⟩ := ha
  exact evalOpt_congr_lam_body w env lam formalsE body body' (.cons a .nil)
    [lf] [a] [av] hlam hform rfl rfl
    (by intro p hp; simp only [List.zip_cons_cons, List.zip_nil_right,
          List.mem_singleton] at hp; subst hp; exact ⟨Na, ha⟩) hbody

theorem re_lam_body2_eq (w : World) (env : Env) (lam : Symbol)
    (formalsE body body' a b : SExpr) (f1 f2 : Symbol)
    (hlam : lam.isNamed "LAMBDA" = true)
    (hform : lamFormals? formalsE = some [f1, f2])
    (ha : ∃ N, ∃ av, ∀ f ≥ N, evalOpt f w env a = some av)
    (hb : ∃ N, ∃ bv, ∀ f ≥ N, evalOpt f w env b = some bv)
    (hbody : ∀ env', ∃ N, ∀ f ≥ N, evalOpt f w env' body = evalOpt f w env' body') :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.cons (.atom (.symbol lam))
        (.cons formalsE (.cons body .nil))) (.cons a (.cons b .nil))) =
      evalOpt f w env (.cons (.cons (.atom (.symbol lam))
        (.cons formalsE (.cons body' .nil))) (.cons a (.cons b .nil))) := by
  obtain ⟨Na, av, ha⟩ := ha
  obtain ⟨Nb, bv, hb⟩ := hb
  exact evalOpt_congr_lam_body w env lam formalsE body body' (.cons a (.cons b .nil))
    [f1, f2] [a, b] [av, bv] hlam hform rfl rfl
    (by intro p hp; simp only [List.zip_cons_cons, List.zip_nil_right,
          List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact ⟨Na, ha⟩
        · exact ⟨Nb, hb⟩) hbody

end ACL2.Replay
