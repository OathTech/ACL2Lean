/-
  Replay/Lemmas/TotalityArity — the measure table's ARITY rows
  (T1+2 sprint phase 2, 2026-08-14).

  The overspecialization audit's F6/F7/F8 found `proveTotality`'s
  admission gate accepting exactly ONE (measure, arity, measured-position)
  combination while its sibling fragments understood several more. These
  are the wrapper lemmas the missing rows need, each the μ-generic twin of
  an existing `totality_*_rec_mu` (`Replay/Lemmas/Judgments.lean`):

  - `totality_2_rec_sum_mu` — TWO measured formals under one `Nat` measure
    of BOTH values (`MERGE2`/`INTERLEAVE`'s
    `(BINARY-+ (ACL2-COUNT X) (ACL2-COUNT Y))` with `:MEASURED (Y X)`);
    audit F6's single largest table cell.
  - `totality_3_rec_fst_mu` — 3-ary measured on the FIRST formal
    (`ZIP3`, `recon-tests/16-three-way`); audit F7's missing twin of
    `totality_3_rec_snd_mu`.

  μ is proof bookkeeping (design I1): it appears in no statement.
-/
import ACL2Lean.Replay.Lemmas.Judgments

namespace ACL2.Replay

open ACL2

/-- Strong induction over an arbitrary `Nat` measure of a PAIR of values —
    the two-measured-formal twin of `measure_strong_induction_val`. The IH
    covers every pair of strictly smaller measure, which is exactly what a
    sum-measure decrease obligation (`(O< (+ c(σx) c(σy)) (+ c(x) c(y)))`)
    licenses at a self-call that moves both arguments. -/
theorem measure_strong_induction_val2 (μ : SExpr → SExpr → Nat)
    (P : SExpr → SExpr → Prop)
    (step : ∀ x y, (∀ x' y', μ x' y' < μ x y → P x' y') → P x y) :
    ∀ x y, P x y := by
  intro x y
  generalize h : μ x y = n
  induction n using Nat.strong_induction_on generalizing x y with
  | _ n ih => exact step x y (fun x' y' hlt => ih (μ x' y') (h ▸ hlt) x' y' rfl)

/-- 2-ary RECURSIVE totality under a measure of BOTH argument values
    (the `sumCount` measure-table row). Unlike `totality_2_rec_mu`, which
    inducts on ONE formal and universally quantifies the other inside, the
    IH here is over the PAIR — required because a sum-measure self-call
    (`(merge2 x (cdr y))`) decreases the sum while INCREASING neither
    component's own count on its own. -/
theorem totality_2_rec_sum_mu (μ : SExpr → SExpr → Nat)
    (w : World) (s : Symbol) (formal1 formal2 : Symbol) (body : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2], body))
    (step : ∀ av1 av2 : SExpr,
      (∀ bv cv : SExpr, μ bv cv < μ av1 av2 →
        ∃ N, ∃ v, ∀ f ≥ N,
          evalOpt f w (bindArgs [formal1, formal2] [bv, cv]) body = some v) →
      ∃ N, ∃ v, ∀ f ≥ N,
        evalOpt f w (bindArgs [formal1, formal2] [av1, av2]) body = some v) :
    ∀ (env' : Env) (a0 a1 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a1 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N,
        evalOpt f w env'
          (.cons (.atom (.symbol s)) (.cons a0 (.cons a1 .nil))) = some v := by
  have hbody := measure_strong_induction_val2 μ
    (fun av1 av2 => ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w (bindArgs [formal1, formal2] [av1, av2]) body = some v) step
  exact totality_2_of_body w s formal1 formal2 body h_ns h_def hbody

/-- 3-ary RECURSIVE totality, measured on the FIRST formal (`ZIP3`:
    `(zip3 (cdr x) (cdr y) (cdr z))` measured on `X`) — audit F7's
    missing twin of `totality_3_rec_snd_mu`; the other two argument values
    are universally quantified INSIDE the induction. μ-generic. -/
theorem totality_3_rec_fst_mu (μ : SExpr → Nat)
    (w : World) (s : Symbol) (formal1 formal2 formal3 : Symbol) (body : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h_def : w.defs.get? s = some ([formal1, formal2, formal3], body))
    (step : ∀ av1 : SExpr,
      (∀ bv : SExpr, μ bv < μ av1 → ∀ av2 av3 : SExpr,
        ∃ N, ∃ v, ∀ f ≥ N,
          evalOpt f w (bindArgs [formal1, formal2, formal3] [bv, av2, av3])
            body = some v) →
      ∀ av2 av3 : SExpr,
      ∃ N, ∃ v, ∀ f ≥ N,
        evalOpt f w (bindArgs [formal1, formal2, formal3] [av1, av2, av3])
          body = some v) :
    ∀ (env' : Env) (a0 a1 a2 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a1 = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a2 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N,
        evalOpt f w env'
          (.cons (.atom (.symbol s))
            (.cons a0 (.cons a1 (.cons a2 .nil)))) = some v := by
  have hbody := measure_strong_induction_val μ
    (fun av1 => ∀ av2 av3, ∃ N, ∃ v, ∀ f ≥ N,
      evalOpt f w (bindArgs [formal1, formal2, formal3] [av1, av2, av3]) body
        = some v) step
  exact totality_3_of_body w s formal1 formal2 formal3 body h_ns h_def
    (fun av1 av2 av3 => hbody av1 av2 av3)

end ACL2.Replay
