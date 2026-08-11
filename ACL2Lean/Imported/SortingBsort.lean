import ACL2Lean.Imported.Sorting

/-! # Imported: the bsort book — the BNEXT FIXED-POINT row

The bsort cluster's decode layer, split out of `Imported/Sorting.lean`
(which is at its module-weight baseline). The BNEXT simulation itself
(`bnextExec` / `bnext_exec_corr` / the generated `bnextExec_enc`) and the
native pass `bnextL` live there; this module carries the row assemblies
that consume them.

ORDEREDP-WHEN-BNEXT-CONSTANT is the bubble-sort termination argument's
other half: a list the bubble pass leaves ALONE is already sorted. Its
native reading needs no new simulation — `bnextL` (the pass) and
`orderedpRec` (the chain2 reading of ORDEREDP) both exist, so the decode
is the standard implies-eliminator over the two sims. -/

open ACL2 ACL2.Replay ACL2.Lifting ACL2.Worlds.Perm ACL2.ExecGen

namespace ACL2.Worlds.Sorting

/-- The ORDEREDP-WHEN-BNEXT-CONSTANT replayed-statement formula — the root
    Goal clause, exactly as the log emits it:
    `(IMPLIES (EQUAL (BNEXT X) X) (ORDEREDP X))`. -/
def orderedp_when_bnext_constantFormula : SExpr :=
  impliesT (equalT (app1 "BNEXT" xT) xT) (orderedpT xT)

/-- ORDEREDP-WHEN-BNEXT-CONSTANT, natively: A FIXED POINT OF THE BUBBLE
    PASS IS SORTED — if one pass of `bnextL` leaves the list unchanged,
    every adjacent pair is lexorder-related.
    SCOPE: the native quantifies over `List SExpr` — the `enc` IMAGE —
    while the ACL2 theorem is over ALL objects, so this is strictly
    WEAKER than the replayed statement (the standing type-absorbed
    doctrine). -/
theorem orderedp_when_bnext_constant_native_of_replayed (w : World)
    (h_bnext : w.defs.get? bnext_sym = some ([xS], bnextBody))
    (h_ord : w.defs.get? { package := "ACL2", name := "ORDEREDP" }
      = some ([{ package := "ACL2", name := "X" }],
              chain2Body "LEXORDER" "ORDEREDP"))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env orderedp_when_bnext_constantFormula = some v
        ∧ v ≠ SExpr.nil)
    (xs : List SExpr) (h : bnextL xs = xs) :
    orderedpRec xs = true := by
  let e : Env := ({} : Env).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ({} : Env).insert xS (enc xs) from rfl,
          Env.get?_insert, if_pos (by decide)])
  -- the antecedent: (bnext x) computes the native pass, which the
  -- hypothesis says IS x — so (equal (bnext x) x) is truthy
  have hbn : ConvTo w e (app1 "BNEXT" xT) (bnextExec (enc xs)) :=
    bnext_exec_corr w h_bnext h_no_consp h_no_car h_no_cdr h_no_cons
      h_no_lexorder e xT (enc xs) hx
  rw [bnextExec_enc] at hbn
  have hEq := conv_equalT w e (app1 "BNEXT" xT) xT (enc (bnextL xs))
    (enc xs) h_no_equal hbn hx
  -- the consequent: (orderedp x) computes the chain2 reading
  have hOrd := corr_orderedp_enc w h_ord h_no_consp h_no_cdr h_no_car
    h_no_lexorder xs e xT hx
  have hImp := conv_builtin2 w e { name := "IMPLIES" } _ _ _ _ _ (by decide)
    h_no_implies hEq hOrd (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (replayed_pins_ne_nil (hreplayed e) hImp)
  have hp : Logic.toBool (Logic.equal (enc (bnextL xs)) (enc xs)) = true :=
    equal_truthy_of_eq (by rw [h])
  exact bool_true_of_cond_truthy (truthy_of_implies_t hIt hp)

end ACL2.Worlds.Sorting
