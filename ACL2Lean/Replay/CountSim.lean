/-
  #37 S4 — SIMULATION lemmas for corpus measure functions (Route A,
  MDD-ratified 2026-07-18): the Lean model functions (`Logic.evens`,
  `Logic.odds`) are PROVED to coincide with the world's defuns — the
  models stay ordinary Lean functions that merely happen to compute what
  the ACL2 definitions compute; nothing is added to the trusted core.
  Consumed by the decrease-prover registry
  (docs/plans/2026-07-18_decrease-prover-rework.md, S4).

  Shape, per function: a BODY-level forward convergence (`…_body_conv`,
  by strong induction on the argument value's acl2Count — pure
  intro-direction composition of the EvalLemmas conv kit) and a CALL-level
  `…_sim` that turns a pinned convergence `eval (EVENS a) = some v` into
  `v = Logic.evens xv` by determinism (`conv_unique`). World-parametric
  (invariant L3): the defun body and the four builtin no-shadow facts are
  hypotheses, discharged by kernel decision at the use site after the
  registry checks the world's ACTUAL body against these exact constants.
-/
import ACL2Lean.Count
import ACL2Lean.Replay.EvalLemmas

namespace ACL2.Replay

open ACL2 Logic

/-! ## The corpus shapes (checked verbatim by the registry before use) -/

def evensSym : Symbol := { name := "EVENS" }
def oddsSym : Symbol := { name := "ODDS" }
/-- Both corpus defuns use formal `L`. -/
def simL : Symbol := { name := "L" }

private def vL : SExpr := .atom (.symbol simL)

/-- `(IF (CONSP L) (CONS (CAR L) (EVENS (CDR (CDR L)))) 'NIL)` — EVENS'
    body exactly as the world defines it (ACL2's ground-zero `evens`,
    normalized). -/
def evensBody : SExpr :=
  .cons (.atom (.symbol { name := "IF" }))
    (.cons (.cons (.atom (.symbol { name := "CONSP" })) (.cons vL .nil))
    (.cons (.cons (.atom (.symbol { name := "CONS" }))
             (.cons (.cons (.atom (.symbol { name := "CAR" })) (.cons vL .nil))
             (.cons (.cons (.atom (.symbol evensSym))
                      (.cons (.cons (.atom (.symbol { name := "CDR" }))
                               (.cons (.cons (.atom (.symbol { name := "CDR" }))
                                        (.cons vL .nil)) .nil))
                      .nil))
             .nil)))
    (.cons (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.nil .nil))
      .nil)))

/-- `(EVENS (CDR L))` — ODDS' body exactly as the world defines it. -/
def oddsBody : SExpr :=
  .cons (.atom (.symbol evensSym))
    (.cons (.cons (.atom (.symbol { name := "CDR" })) (.cons vL .nil)) .nil)

/-! ## Small conv-kit completions -/

/-- Two convergences of the same term agree. -/
theorem conv_unique {w : World} {e : Env} {t v v' : SExpr}
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e t = some v)
    (h' : ∃ N, ∀ f ≥ N, evalOpt f w e t = some v') : v = v' := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨N', hN'⟩ := h'
  have h1 := hN (max N N') (le_max_left _ _)
  have h2 := hN' (max N N') (le_max_right _ _)
  rw [h1] at h2
  exact Option.some.inj h2

/-- Bound-variable convergence. -/
theorem conv_var (w : World) (e : Env) (s : Symbol) (v : SExpr)
    (h : e.get? s = some v) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (.atom (.symbol s)) = some v :=
  ⟨1, fun f hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact evalOpt_var g w e s v h⟩

/-- Quote convergence. -/
theorem conv_quote (w : World) (e : Env) (v : SExpr) :
    ∃ N, ∀ f ≥ N, evalOpt f w e
      (.cons (.atom (.symbol { name := "QUOTE" })) (.cons v .nil)) = some v :=
  ⟨1, fun f hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact evalOpt_quote g w e v⟩

/-- IF with a converging NIL test converges to the else-branch's value
    (the conv-level counterpart of `evalOpt_if_false`; the truthy version
    is EvalLemmas' `conv_if_true`). -/
theorem conv_if_false (w : World) (env : Env) (c t el v : SExpr)
    (htest : ∃ N, ∀ f ≥ N, evalOpt f w env c = some SExpr.nil)
    (helse : ∃ N, ∀ f ≥ N, evalOpt f w env el = some v) :
    ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol { name := "IF" }))
        (.cons c (.cons t (.cons el .nil)))) = some v := by
  obtain ⟨Nc, hc⟩ := htest
  obtain ⟨Ne, he⟩ := helse
  refine ⟨max Nc Ne + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [evalOpt_if_false g w env c t el (hc g (by omega))]
  exact he g (by omega)

/-- Fact-shape normalizer: a falsy value IS `toBool = false`. -/
theorem toBool_false_of_eq_nil {v : SExpr} (h : v = SExpr.nil) :
    Logic.toBool v = false := h ▸ rfl

/-- Cast a model-level count decrease through a sim equality. -/
theorem count_lt_of_eq {v m xv : SExpr} (h : v = m)
    (hlt : m.acl2Count < xv.acl2Count) : v.acl2Count < xv.acl2Count :=
  h ▸ hlt

/-! ## EVENS -/

/-- The model side of the body's then-branch:
    `evens (cons a b) = cons a (evens (cdr b))`. -/
theorem evens_cons_eq (a b : SExpr) :
    Logic.evens (.cons a b) = .cons a (Logic.evens (Logic.cdr b)) := by
  cases b <;> rfl

/-- The one-formal environment binds the formal to the argument value. -/
private theorem bindArgs_get_simL (xv : SExpr) :
    (bindArgs [simL] [xv]).get? simL = some xv := by
  simp [bindArgs]

/-- Body-level convergence for a NON-cons argument: the else branch. -/
private theorem evens_body_conv_noncons (w : World)
    (hnC : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (xv : SExpr) (hx : Logic.consp xv = SExpr.nil) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w (bindArgs [simL] [xv]) evensBody = some SExpr.nil := by
  have hvar := conv_var w (bindArgs [simL] [xv]) simL xv (bindArgs_get_simL xv)
  have htest := conv_builtin1 w (bindArgs [simL] [xv]) { name := "CONSP" }
    vL xv (Logic.consp xv) (by decide) hnC hvar (callBuiltin_consp xv)
  rw [hx] at htest
  exact conv_if_false w (bindArgs [simL] [xv]) _ _ _ SExpr.nil htest
    (conv_quote w (bindArgs [simL] [xv]) SExpr.nil)

/-- BODY-level simulation: the world's EVENS body, evaluated on any
    argument value, converges to `Logic.evens` of it. Strong induction on
    the argument's `acl2Count` (the recursive call's argument is
    `cdr (cdr xv)`, strictly smaller on a cons). -/
theorem evens_body_conv (w : World)
    (hdef : w.defs.get? evensSym = some ([simL], evensBody))
    (hnC : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (hnCar : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (hnCdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (hnCons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (xv : SExpr) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w (bindArgs [simL] [xv]) evensBody
        = some (Logic.evens xv) := by
  suffices H : ∀ n (xv : SExpr), xv.acl2Count ≤ n →
      ∃ N, ∀ f ≥ N,
        evalOpt f w (bindArgs [simL] [xv]) evensBody
          = some (Logic.evens xv) from H xv.acl2Count xv le_rfl
  intro n
  induction n with
  | zero =>
    intro xv hc
    match xv with
    | .cons a b => simp [SExpr.acl2Count] at hc
    | .nil => exact evens_body_conv_noncons w hnC .nil rfl
    | .atom x => exact evens_body_conv_noncons w hnC (.atom x) rfl
  | succ n ih =>
    intro xv hc
    match xv with
    | .nil => exact evens_body_conv_noncons w hnC .nil rfl
    | .atom x => exact evens_body_conv_noncons w hnC (.atom x) rfl
    | .cons a b =>
      have hbnd : (Logic.cdr b).acl2Count ≤ n := by
        have h1 := acl2Count_cdr_le b
        simp only [SExpr.acl2Count] at hc
        omega
      have hvar := conv_var w (bindArgs [simL] [.cons a b]) simL (.cons a b)
        (bindArgs_get_simL (.cons a b))
      have htest := conv_builtin1 w (bindArgs [simL] [.cons a b])
        { name := "CONSP" } vL (.cons a b) (Logic.consp (.cons a b))
        (by decide) hnC hvar (callBuiltin_consp (.cons a b))
      have hcar := conv_builtin1 w (bindArgs [simL] [.cons a b])
        { name := "CAR" } vL (.cons a b) (Logic.car (.cons a b))
        (by decide) hnCar hvar (callBuiltin_car (.cons a b))
      have hcdr1 := conv_builtin1 w (bindArgs [simL] [.cons a b])
        { name := "CDR" } vL (.cons a b) (Logic.cdr (.cons a b))
        (by decide) hnCdr hvar (callBuiltin_cdr (.cons a b))
      have hcdr2 := conv_builtin1 w (bindArgs [simL] [.cons a b])
        { name := "CDR" }
        (.cons (.atom (.symbol { name := "CDR" })) (.cons vL .nil))
        (Logic.cdr (.cons a b)) (Logic.cdr (Logic.cdr (.cons a b)))
        (by decide) hnCdr hcdr1 (callBuiltin_cdr (Logic.cdr (.cons a b)))
      -- the recursive call: `cdr (cdr (cons a b))` is definitionally
      -- `cdr b`, whose count is ≤ n — the induction hypothesis applies
      have hrec := conv_defn_1 w (bindArgs [simL] [.cons a b]) evensSym
        (.cons (.atom (.symbol { name := "CDR" }))
          (.cons (.cons (.atom (.symbol { name := "CDR" }))
            (.cons vL .nil)) .nil))
        (Logic.cdr (Logic.cdr (.cons a b))) simL evensBody
        (Logic.evens (Logic.cdr b))
        (by decide) hdef hcdr2 (ih (Logic.cdr b) hbnd)
      have hcons := conv_builtin2 w (bindArgs [simL] [.cons a b])
        { name := "CONS" } _ _ (Logic.car (.cons a b))
        (Logic.evens (Logic.cdr b))
        (.cons (Logic.car (.cons a b)) (Logic.evens (Logic.cdr b)))
        (by decide) hnCons hcar hrec rfl
      have hout := conv_if_true w (bindArgs [simL] [.cons a b])
        (.cons (.atom (.symbol { name := "CONSP" })) (.cons vL .nil))
        (.cons (.atom (.symbol { name := "CONS" }))
          (.cons (.cons (.atom (.symbol { name := "CAR" })) (.cons vL .nil))
          (.cons (.cons (.atom (.symbol evensSym))
                   (.cons (.cons (.atom (.symbol { name := "CDR" }))
                            (.cons (.cons (.atom (.symbol { name := "CDR" }))
                                     (.cons vL .nil)) .nil))
                   .nil))
          .nil)))
        (.cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.nil .nil))
        (Logic.consp (.cons a b))
        (.cons (Logic.car (.cons a b)) (Logic.evens (Logic.cdr b)))
        htest rfl hcons
      rw [evens_cons_eq]
      exact hout

/-- CALL-level simulation: a pinned convergence of `(EVENS a)` yields
    `v = Logic.evens xv` for the argument's pinned value `xv`. -/
theorem evens_sim (w : World) (e : Env)
    (hdef : w.defs.get? evensSym = some ([simL], evensBody))
    (hnC : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (hnCar : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (hnCdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (hnCons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (a xv v : SExpr)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w e a = some xv)
    (hv : ∃ N, ∀ f ≥ N,
      evalOpt f w e (.cons (.atom (.symbol evensSym)) (.cons a .nil))
        = some v) :
    v = Logic.evens xv :=
  conv_unique hv
    (conv_defn_1 w e evensSym a xv simL evensBody (Logic.evens xv)
      (by decide) hdef ha (evens_body_conv w hdef hnC hnCar hnCdr hnCons xv))

/-! ## ODDS -/

/-- CALL-level simulation for ODDS (`(EVENS (CDR L))`): a pinned
    convergence of `(ODDS a)` yields `v = Logic.odds xv`. -/
theorem odds_sim (w : World) (e : Env)
    (hdefE : w.defs.get? evensSym = some ([simL], evensBody))
    (hdefO : w.defs.get? oddsSym = some ([simL], oddsBody))
    (hnC : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (hnCar : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (hnCdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (hnCons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (a xv v : SExpr)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w e a = some xv)
    (hv : ∃ N, ∀ f ≥ N,
      evalOpt f w e (.cons (.atom (.symbol oddsSym)) (.cons a .nil))
        = some v) :
    v = Logic.odds xv := by
  -- odds' body under `L ↦ xv`: `(CDR L)` → `cdr xv`, then the EVENS call
  -- → `evens (cdr xv) = odds xv`
  have hvar := conv_var w (bindArgs [simL] [xv]) simL xv (bindArgs_get_simL xv)
  have hcdr := conv_builtin1 w (bindArgs [simL] [xv]) { name := "CDR" }
    vL xv (Logic.cdr xv) (by decide) hnCdr hvar (callBuiltin_cdr xv)
  have hbody : ∃ N, ∀ f ≥ N,
      evalOpt f w (bindArgs [simL] [xv]) oddsBody
        = some (Logic.evens (Logic.cdr xv)) :=
    conv_defn_1 w (bindArgs [simL] [xv]) evensSym
      (.cons (.atom (.symbol { name := "CDR" })) (.cons vL .nil))
      (Logic.cdr xv) simL evensBody (Logic.evens (Logic.cdr xv))
      (by decide) hdefE hcdr
      (evens_body_conv w hdefE hnC hnCar hnCdr hnCons (Logic.cdr xv))
  exact conv_unique hv
    (conv_defn_1 w e oddsSym a xv simL oddsBody (Logic.odds xv)
      (by decide) hdefO ha hbody)

end ACL2.Replay
