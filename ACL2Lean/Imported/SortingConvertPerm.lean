import ACL2Lean.Imported.Sorting

/-! # Imported: the convert-perm-to-how-many book — HOW-MANY-RM-GENERAL

The convert-perm book's decode layer beyond the three rows already in
`Imported/Sorting.lean` (which is at its module-weight baseline). The
`rm` / `memb` / `how-many` simulations all live there (and in
`Imported/Perm.lean`); this module carries the row assembly that
consumes them.

HOW-MANY-RM-GENERAL is HOW-MANY-RM's unconditional companion: it fixes
the count after erasing ANY element, including the erased element
itself (one fewer, when it was present). Its native reading is
therefore an equation with a case split, and the ACL2 side's `(+ -1
…)` is genuine INTEGER arithmetic — the decode lands the `Int`
equation and the `Nat` reading follows because a present element has a
positive count. -/

open ACL2 ACL2.Replay ACL2.Lifting ACL2.Worlds.Perm ACL2.ExecGen

namespace ACL2.Worlds.Sorting

/-- The HOW-MANY-RM-GENERAL replayed-statement formula — the root Goal
    clause, exactly as the log emits it (the `AND` already if-expanded):
    `(EQUAL (HOW-MANY A (RM B X))
            (IF (IF (EQUAL A B) (MEMB A X) 'NIL)
                (BINARY-+ '-1 (HOW-MANY A X))
                (HOW-MANY A X)))`. -/
def how_many_rm_generalFormula : SExpr :=
  equalT (howManyT aT (rmT bT xT))
    (appIf (appIf (equalT aT bT) (membT aT xT) qNilT)
      (plusT (qInt (-1)) (howManyT aT xT))
      (howManyT aT xT))

/-- HOW-MANY-RM-GENERAL, natively: erasing an element drops ITS count by
    one when it was present, and leaves every other count alone (the
    general count-of-erase law; HOW-MANY-RM is its off-diagonal case).
    SCOPE: the native quantifies over `List SExpr` — the `enc` IMAGE —
    while the ACL2 theorem is over ALL objects, so this is strictly
    WEAKER than the replayed statement (the standing type-absorbed
    doctrine: the non-list cases are `tlfix` plumbing with no
    user-facing content). -/
theorem how_many_rm_general_native_of_replayed (w : World)
    (h_rm : w.defs.get? { package := "ACL2", name := "RM" }
      = some ([{ package := "ACL2", name := "E" },
               { package := "ACL2", name := "X" }], rmBody))
    (h_memb : w.defs.get? { package := "ACL2", name := "MEMB" }
      = some ([{ package := "ACL2", name := "A" },
               { package := "ACL2", name := "X" }], membBody))
    (h_hm : w.defs.get? how_many_sym = some ([eS, xS], howManyBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env how_many_rm_generalFormula = some v ∧ v ≠ SExpr.nil)
    (av bv : SExpr) (xs : List SExpr) :
    (xs.erase bv).count av
      = bif (av == bv) && xs.contains av then xs.count av - 1
        else xs.count av := by
  let e : Env := ((({} : Env).insert xS (enc xs)).insert bS bv).insert aS av
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some av :=
    re_val_var_get w e { name := "A" } av (by
      show e.get? aS = some av
      rw [show e = ((({} : Env).insert xS (enc xs)).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hb : ∃ N, ∀ f ≥ N, evalOpt f w e bT = some bv :=
    re_val_var_get w e { name := "B" } bv (by
      show e.get? bS = some bv
      rw [show e = ((({} : Env).insert xS (enc xs)).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ((({} : Env).insert xS (enc xs)).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  -- the LHS count, over the erased list
  have hRm : ∃ N, ∀ f ≥ N,
      evalOpt f w e (rmT bT xT) = some (enc (xs.erase bv)) :=
    corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr h_no_cons
      xs e bT xT bv hb hx
  have hL : ∃ N, ∀ f ≥ N, evalOpt f w e (howManyT aT (rmT bT xT))
      = some (.atom (.number (.int ((xs.erase bv).count av)))) := by
    have hcorr := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
      h_no_cdr h_no_plus e aT (rmT bT xT) av (enc (xs.erase bv)) ha hRm
    rw [howManyExec_enc] at hcorr
    exact hcorr
  have hCount : ∃ N, ∀ f ≥ N, evalOpt f w e (howManyT aT xT)
      = some (.atom (.number (.int (xs.count av)))) := by
    have hcorr := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
      h_no_cdr h_no_plus e aT xT av (enc xs) ha hx
    rw [howManyExec_enc] at hcorr
    exact hcorr
  -- the RHS guard: (if (equal a b) (memb a x) 'nil)
  have hMemb := corr_memb_enc w h_memb h_no_consp h_no_equal h_no_car
    h_no_cdr xs e aT xT av ha hx
  have hEqAB := conv_equalT w e aT bT av bv h_no_equal ha hb
  have hInner := conv_if_lift w e (equalT aT bT) (membT aT xT) qNilT
    (Logic.equal av bv) (bif xs.contains av then SExpr.t else SExpr.nil)
    SExpr.nil hEqAB (fun _ => hMemb) (fun _ => re_val_quote w e SExpr.nil)
  -- the RHS branches: the decremented count, and the count
  have hNeg1 : ∃ N, ∀ f ≥ N, evalOpt f w e (qInt (-1))
      = some (.atom (.number (.int (-1)))) := re_val_quote w e _
  have hPlus := conv_plus_int w e (qInt (-1)) (howManyT aT xT) (-1)
    (xs.count av) h_no_plus hNeg1 hCount
  have hOuter := conv_if_lift w e
    (appIf (equalT aT bT) (membT aT xT) qNilT)
    (plusT (qInt (-1)) (howManyT aT xT)) (howManyT aT xT) _
    (.atom (.number (.int (-1 + (xs.count av : Int)))))
    (.atom (.number (.int (xs.count av)))) hInner
    (fun _ => hPlus) (fun _ => hCount)
  have hEq := conv_equalT w e _ _ _ _ h_no_equal hL hOuter
  have hval := Logic.eq_of_equal_ne_nil
    (replayed_pins_ne_nil (hreplayed e) hEq)
  -- the guard's value IS the native's Bool condition
  have hcond : Logic.toBool
      (if Logic.toBool (Logic.equal av bv) = true then
        (bif xs.contains av then SExpr.t else SExpr.nil) else SExpr.nil)
      = ((av == bv) && xs.contains av) := by
    rw [toBool_equal]
    cases h1 : (av == bv) <;> cases h2 : xs.contains av <;>
      simp [Logic.toBool]
  rw [hcond] at hval
  cases h3 : ((av == bv) && xs.contains av) with
  | true =>
    rw [h3, if_pos rfl] at hval
    have hint : ((xs.erase bv).count av : Int) = -1 + (xs.count av : Int) :=
      int_atom_inj hval
    show (xs.erase bv).count av = xs.count av - 1
    omega
  | false =>
    rw [h3, if_neg (by simp)] at hval
    have hint : ((xs.erase bv).count av : Int) = (xs.count av : Int) :=
      int_atom_inj hval
    show (xs.erase bv).count av = xs.count av
    omega

end ACL2.Worlds.Sorting
