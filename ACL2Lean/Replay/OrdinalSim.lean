/-
  Replay/OrdinalSim — SIMULATION lemmas for ACL2's ground-zero ORDINAL
  destructors (`O-RST`, `O-FIRST-EXPT`) and the `O-FINP` recognizer
  duality (T1+2 sprint P3b, 2026-08-15).

  Why this family exists. `O<` and `O-P` are RECURSIVE ground-zero defuns
  whose admission decreases are stated over destructor COMPOSITES rather
  than bare `CAR`/`CDR` chains:

      O<   :  (O< (ACL2-COUNT (O-RST X))        (ACL2-COUNT X))
              (O< (ACL2-COUNT (O-FIRST-EXPT X)) (ACL2-COUNT X))
      O-P  :  the same two obligations

  (the emitted `:TERMINATION-CLAUSES` of the ground-zero snapshot —
  RT2 ask 4 verified they have been emitted since 006bebce9f, which is
  why `total:O<` / `total:O-P` are a CONSUMPTION item and not an
  emission gap). `chainLt`'s destructor walk cannot state either
  argument, so the decrease prover needs the same S4 REGISTRY treatment
  `EVENS`/`ODDS` already get: a proved Lean model of what the world's
  own defun computes, plus the count lemma for that model.

  Shape, exactly as `Replay/CountSim`: the world's defun body and the
  builtin no-shadow facts are HYPOTHESES (invariant L3 —
  world-parametric), discharged by kernel decision at the use site
  after the registry byte-checks the world's ACTUAL entry against the
  literal shapes here. A world whose `O-RST` is not `(CDR X)` simply
  fails the check and the decrease stays an honest frontier.

  The third lemma is the `O-FINP` RECOGNIZER DUALITY: ACL2's ordinal
  bodies branch on `(O-FINP X)`, whose ground-zero body is literally
  `(IF (CONSP X) 'NIL 'T)`, so a REFUTED `(O-FINP b)` branch fact IS the
  `(consp b)` evidence both decreases need. That bridge is the ordinal
  twin of `BranchFacts.recogView`'s CONSP/ENDP/ATOM duality — read off
  ACL2's own emitted definition, never inferred.
-/
import ACL2Lean.Replay.CountSim

namespace ACL2.Replay

open ACL2 Logic

/-! ## The ground-zero shapes (byte-checked by the registry before use) -/

def oRstSym : Symbol := { name := "O-RST" }
def oFirstExptSym : Symbol := { name := "O-FIRST-EXPT" }
def oFinpSym : Symbol := { name := "O-FINP" }

private def ordX : SExpr := .atom (.symbol oltXSym)
private def carOf (u : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "CAR" })) (.cons u .nil)

/-- `(CDR X)` — `O-RST`'s ground-zero body exactly as ACL2 emits it. -/
def oRstBodyShape : SExpr :=
  .cons (.atom (.symbol { name := "CDR" })) (.cons ordX .nil)

/-- `(IF (O-FINP X) '0 (CAR (CAR X)))` — `O-FIRST-EXPT`'s ground-zero
    body exactly as ACL2 emits it. -/
def oFirstExptBodyShape : SExpr :=
  .cons (.atom (.symbol { name := "IF" }))
    (.cons (.cons (.atom (.symbol oFinpSym)) (.cons ordX .nil))
      (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
          (.cons (.atom (.number (.int 0))) .nil))
        (.cons (carOf (carOf ordX)) .nil)))

private theorem bindArgs_get_ordX (xv : SExpr) :
    (bindArgs [oltXSym] [xv]).get? oltXSym = some xv := by
  simp [bindArgs]

/-! ## `O-FINP` on a CONS, and the recognizer duality -/

/-- `o-finp` of a CONS value is `nil` (the byte-checked body's then
    branch) — the mirror of `conv_ofinp_atom`'s atom case. -/
theorem conv_ofinp_cons {w : World} {env : Env} {arg av : SExpr}
    (hnoConsp : w.defs.get? { name := "CONSP" } = none)
    (hdefF : w.defs.get? oFinpSym = some ([oltXSym], oFinpBodyShape))
    (hcons : Logic.toBool (Logic.consp av) = true)
    (harg : ∃ N, ∀ f ≥ N, evalOpt f w env arg = some av) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol oFinpSym)) (.cons arg .nil))
        = some SExpr.nil := by
  have hX := conv_var w (bindArgs [oltXSym] [av]) oltXSym av
    (bindArgs_get_ordX av)
  have hconsp := conv_builtin1 w (bindArgs [oltXSym] [av]) { name := "CONSP" }
    ordX av (Logic.consp av) (by decide) hnoConsp hX (callBuiltin_consp av)
  have hbody : ∃ N, ∀ f ≥ N,
      evalOpt f w (bindArgs [oltXSym] [av]) oFinpBodyShape = some SExpr.nil :=
    conv_if_true w (bindArgs [oltXSym] [av]) _ _ _ (Logic.consp av) SExpr.nil
      hconsp hcons (conv_quote w (bindArgs [oltXSym] [av]) SExpr.nil)
  exact conv_defn_1 w env oFinpSym arg av oltXSym oFinpBodyShape SExpr.nil
    (by decide) hdefF harg hbody

/-- THE ORDINAL RECOGNIZER DUALITY: a REFUTED `(O-FINP b)` branch fact IS
    `(consp b)`. ACL2's ground-zero `O-FINP` is `(IF (CONSP X) 'NIL 'T)`,
    so an atom argument makes it `'T` (`conv_ofinp_atom`); a falsy verdict
    therefore forces the argument to be a cons. Both convergences are the
    ones the admission walk already has in hand (the opaque-test split
    carries the verdict's value and its convergence). -/
theorem consp_toBool_of_ofinp_false {w : World} {env : Env} {arg av vc : SExpr}
    (hnoConsp : w.defs.get? { name := "CONSP" } = none)
    (hdefF : w.defs.get? oFinpSym = some ([oltXSym], oFinpBodyShape))
    (harg : ∃ N, ∀ f ≥ N, evalOpt f w env arg = some av)
    (hfin : ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol oFinpSym)) (.cons arg .nil))
        = some vc)
    (hb : Logic.toBool vc = false) :
    Logic.toBool (Logic.consp av) = true := by
  by_cases hc : Logic.consp av = SExpr.nil
  · -- an ATOM argument makes `(O-FINP arg)` 'T, contradicting the
    -- refuted branch fact
    exfalso
    have ht := conv_ofinp_atom hnoConsp hdefF hc harg
    have hvt : vc = SExpr.t := conv_unique hfin ht
    rw [hvt] at hb
    simp [Logic.toBool] at hb
  · -- `Logic.consp` is two-valued, so "not nil" IS "toBool true"
    cases av <;> simp_all [Logic.toBool]

/-! ## `O-RST` -/

/-- CALL-level simulation: a pinned convergence of `(O-RST a)` yields
    `v = Logic.cdr xv` for the argument's pinned value `xv`. -/
theorem orst_sim (w : World) (e : Env)
    (hdef : w.defs.get? oRstSym = some ([oltXSym], oRstBodyShape))
    (hnCdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (a xv v : SExpr)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w e a = some xv)
    (hv : ∃ N, ∀ f ≥ N,
      evalOpt f w e (.cons (.atom (.symbol oRstSym)) (.cons a .nil))
        = some v) :
    v = Logic.cdr xv := by
  have hvar := conv_var w (bindArgs [oltXSym] [xv]) oltXSym xv
    (bindArgs_get_ordX xv)
  have hbody : ∃ N, ∀ f ≥ N,
      evalOpt f w (bindArgs [oltXSym] [xv]) oRstBodyShape
        = some (Logic.cdr xv) :=
    conv_builtin1 w (bindArgs [oltXSym] [xv]) { name := "CDR" }
      ordX xv (Logic.cdr xv) (by decide) hnCdr hvar (callBuiltin_cdr xv)
  exact conv_unique hv
    (conv_defn_1 w e oRstSym a xv oltXSym oRstBodyShape (Logic.cdr xv)
      (by decide) hdef ha hbody)

/-! ## `O-FIRST-EXPT` -/

/-- CALL-level simulation UNDER THE CONS BRANCH: `(O-FIRST-EXPT a)` with
    `a`'s value a cons is `(CAR (CAR a))`. The cons hypothesis is exactly
    the branch fact the emitted obligation's `(O-FINP X)` ruler supplies
    (via `consp_toBool_of_ofinp_false`) — the else branch is the only one
    ACL2's own decrease clause applies on. -/
theorem ofirstexpt_sim_cons (w : World) (e : Env)
    (hdefE : w.defs.get? oFirstExptSym = some ([oltXSym], oFirstExptBodyShape))
    (hdefF : w.defs.get? oFinpSym = some ([oltXSym], oFinpBodyShape))
    (hnConsp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (hnCar : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (a xv v : SExpr)
    (hcons : Logic.toBool (Logic.consp xv) = true)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w e a = some xv)
    (hv : ∃ N, ∀ f ≥ N,
      evalOpt f w e (.cons (.atom (.symbol oFirstExptSym)) (.cons a .nil))
        = some v) :
    v = Logic.car (Logic.car xv) := by
  have hvar := conv_var w (bindArgs [oltXSym] [xv]) oltXSym xv
    (bindArgs_get_ordX xv)
  have htest := conv_ofinp_cons hnConsp hdefF hcons hvar
  have hcar1 := conv_builtin1 w (bindArgs [oltXSym] [xv]) { name := "CAR" }
    ordX xv (Logic.car xv) (by decide) hnCar hvar (callBuiltin_car xv)
  have hcar2 := conv_builtin1 w (bindArgs [oltXSym] [xv]) { name := "CAR" }
    (carOf ordX) (Logic.car xv) (Logic.car (Logic.car xv)) (by decide) hnCar
    hcar1 (callBuiltin_car (Logic.car xv))
  have hbody : ∃ N, ∀ f ≥ N,
      evalOpt f w (bindArgs [oltXSym] [xv]) oFirstExptBodyShape
        = some (Logic.car (Logic.car xv)) :=
    conv_if_false w (bindArgs [oltXSym] [xv]) _ _ _
      (Logic.car (Logic.car xv)) htest hcar2
  exact conv_unique hv
    (conv_defn_1 w e oFirstExptSym a xv oltXSym oFirstExptBodyShape
      (Logic.car (Logic.car xv)) (by decide) hdefE ha hbody)

/-! ## The model-level count decreases -/

/-- `(CAR (CAR x))` is strictly smaller than a CONS `x` — the
    `O-FIRST-EXPT` row's count leg (one strict `car` step at the base,
    the outer `car` composed by `≤`). -/
theorem consCount_car_car_lt_of_consp {x : SExpr}
    (h : Logic.toBool (Logic.consp x) = true) :
    (Logic.car (Logic.car x)).consCount < x.consCount :=
  Nat.lt_of_le_of_lt (ACL2.consCount_car_le (Logic.car x))
    (ACL2.consCount_car_lt_of_consp h)

end ACL2.Replay
