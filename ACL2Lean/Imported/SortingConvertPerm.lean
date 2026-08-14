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
positive count.

PERM-COUNTER-EXAMPLE-IS-COUNTEREXAMPLE-FOR-TRUE-LISTS is the book's
witness row: `perm-counter-example` computes an element at which the
two lists' counts must agree if they are permutations at all. Its
reading is the RAW ELEMENT reading of the iso generator's table (ruled
2026-08-11) — the program's value is an element of the data, so the
native `pceL` returns a bare `SExpr` and the iso carries no encoder on
the right. -/

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
    howManyL av (xs.erase bv)
      = bif (av == bv) && xs.contains av then howManyL av xs - 1
        else howManyL av xs := by
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
      = some (.atom (.number (.int (howManyL av (xs.erase bv))))) := by
    have hcorr := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
      h_no_cdr h_no_plus e aT (rmT bT xT) av (enc (xs.erase bv)) ha hRm
    rw [howManyExec_enc] at hcorr
    exact hcorr
  have hCount : ∃ N, ∀ f ≥ N, evalOpt f w e (howManyT aT xT)
      = some (.atom (.number (.int (howManyL av xs)))) := by
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
    (howManyL av xs) h_no_plus hNeg1 hCount
  have hOuter := conv_if_lift w e
    (appIf (equalT aT bT) (membT aT xT) qNilT)
    (plusT (qInt (-1)) (howManyT aT xT)) (howManyT aT xT) _
    (.atom (.number (.int (-1 + (howManyL av xs : Int)))))
    (.atom (.number (.int (howManyL av xs)))) hInner
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
    have hint : (howManyL av (xs.erase bv) : Int)
        = -1 + (howManyL av xs : Int) :=
      int_atom_inj hval
    show howManyL av (xs.erase bv) = howManyL av xs - 1
    omega
  | false =>
    rw [h3, if_neg (by simp)] at hval
    have hint : (howManyL av (xs.erase bv) : Int) = (howManyL av xs : Int) :=
      int_atom_inj hval
    show howManyL av (xs.erase bv) = howManyL av xs
    omega

/-! ## PERM-COUNTER-EXAMPLE-IS-COUNTEREXAMPLE-FOR-TRUE-LISTS — the
counterexample WITNESS row -/

/-- The NATIVE counterexample witness: walk `xs`, erasing each element
    from `ys` as it is matched; the first element of `xs` that `ys`
    cannot match IS the witness, and when `xs` is exhausted the witness
    is `ys`'s head (`nil` when both are). Self-contained (waypoint
    criterion: `List` vocabulary only). -/
def pceL : List SExpr → List SExpr → SExpr
  | [], ys => ys.headD SExpr.nil
  | x :: xs, ys => bif ys.contains x then pceL xs (ys.erase x) else x

-- The hand `pceExec` (Sorting.lean) enters the kit registry here — the
-- iso below is its stage-2 reading.
register_exec_kit% "PERM-COUNTER-EXAMPLE" => pceExec arity 2

/-- Stage 2: `pceExec` on encoded lists computes the native witness —
    GENERATED. The result reading is the RAW ELEMENT reading (an
    `SExpr`-valued native, no encoder — the generator's table entry
    ruled 2026-08-11); the MEMB/RM callee isos resolve through the kit
    registry, `car_enc` bridges the exhausted-`xs` branch. -/
derive_sim% pceExec_enc for "PERM-COUNTER-EXAMPLE"
  vars (xs : list) (ys : list)
  exec [xs, ys]
  native (pceL xs ys)
  simp [pceL, car_enc]
  induct functional (pceL xs ys)

/-- The PERM-COUNTER-EXAMPLE-IS-COUNTEREXAMPLE-FOR-TRUE-LISTS
    replayed-statement formula — the root Goal clause, exactly as the log
    emits it (the `AND` already if-expanded):
    `(IMPLIES (IF (TRUE-LISTP X) (TRUE-LISTP Y) 'NIL)
              (EQUAL (PERM X Y)
                     (EQUAL (HOW-MANY (PERM-COUNTER-EXAMPLE X Y) X)
                            (HOW-MANY (PERM-COUNTER-EXAMPLE X Y) Y))))`. -/
def pce_is_counterexampleFormula : SExpr :=
  impliesT (appIf (app1 "TRUE-LISTP" xT) (app1 "TRUE-LISTP" yT) qNilT)
    (equalT (permT xT yT)
      (equalT (howManyT (pceT xT yT) xT) (howManyT (pceT xT yT) yT)))

/-- PERM-COUNTER-EXAMPLE-IS-COUNTEREXAMPLE-FOR-TRUE-LISTS, natively:
    `pceL` IS a complete counterexample witness for permutation —
    two lists are permutations of each other EXACTLY WHEN their counts
    agree at that ONE element. (One direction is trivial; the content is
    the other: a non-permutation is always caught at `pceL`.)
    SCOPE: the native quantifies over `List SExpr` — the `enc` IMAGE —
    which is exactly where the ACL2 theorem's `true-listp` hypotheses put
    it (the type-absorbed doctrine: the hypotheses ARE the enc image, so
    no strength is lost beyond the standing non-list plumbing). -/
theorem pce_is_counterexample_native_of_replayed (w : World)
    (h_pce : w.defs.get? pce_sym = some ([xS, yS], pceBody))
    (h_perm : w.defs.get? { package := "ACL2", name := "PERM" }
      = some ([{ package := "ACL2", name := "X" },
               { package := "ACL2", name := "Y" }], permBody))
    (h_memb : w.defs.get? { package := "ACL2", name := "MEMB" }
      = some ([{ package := "ACL2", name := "A" },
               { package := "ACL2", name := "X" }], membBody))
    (h_rm : w.defs.get? { package := "ACL2", name := "RM" }
      = some ([{ package := "ACL2", name := "E" },
               { package := "ACL2", name := "X" }], rmBody))
    (h_hm : w.defs.get? how_many_sym = some ([eS, xS], howManyBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (h_no_truelistp : w.defs.get? ({ name := "TRUE-LISTP" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env pce_is_counterexampleFormula = some v ∧ v ≠ SExpr.nil)
    (xs ys : List SExpr) :
    xs.isPerm ys
      = (howManyL (pceL xs ys) xs == howManyL (pceL xs ys) ys) := by
  let e : Env := (({} : Env).insert yS (enc ys)).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = (({} : Env).insert yS (enc ys)).insert xS (enc xs)
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f w e yT = some (enc ys) :=
    re_val_var_get w e { name := "Y" } (enc ys) (by
      show e.get? yS = some (enc ys)
      rw [show e = (({} : Env).insert yS (enc ys)).insert xS (enc xs)
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  -- the antecedent: both true-listp conjuncts hold on encoded lists
  have htlX : ∃ N, ∀ f ≥ N,
      evalOpt f w e (app1 "TRUE-LISTP" xT) = some SExpr.t := by
    have := conv_builtin1 w e { name := "TRUE-LISTP" } xT (enc xs)
      (Logic.trueListp (enc xs)) (by decide) h_no_truelistp hx rfl
    rwa [trueListp_enc] at this
  have htlY : ∃ N, ∀ f ≥ N,
      evalOpt f w e (app1 "TRUE-LISTP" yT) = some SExpr.t := by
    have := conv_builtin1 w e { name := "TRUE-LISTP" } yT (enc ys)
      (Logic.trueListp (enc ys)) (by decide) h_no_truelistp hy rfl
    rwa [trueListp_enc] at this
  have hAnt : ∃ N, ∀ f ≥ N,
      evalOpt f w e
        (appIf (app1 "TRUE-LISTP" xT) (app1 "TRUE-LISTP" yT) qNilT)
        = some SExpr.t :=
    conv_if_true w e (app1 "TRUE-LISTP" xT) (app1 "TRUE-LISTP" yT) qNilT
      SExpr.t SExpr.t htlX rfl htlY
  -- the witness, and the two counts at it
  have hpce := pce_exec_corr w h_pce h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons e xT yT (enc xs) (enc ys) hx hy
  rw [pceExec_enc] at hpce
  have hL := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e (pceT xT yT) xT (pceL xs ys) (enc xs) hpce hx
  rw [howManyExec_enc] at hL
  have hR := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e (pceT xT yT) yT (pceL xs ys) (enc ys) hpce hy
  rw [howManyExec_enc] at hR
  have hCounts := conv_equalT w e (howManyT (pceT xT yT) xT)
    (howManyT (pceT xT yT) yT) _ _ h_no_equal hL hR
  -- the left side of the conclusion: the perm simulation
  have hPerm := corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons xs ys e xT yT hx hy
  have hConcl := conv_equalT w e (permT xT yT)
    (equalT (howManyT (pceT xT yT) xT) (howManyT (pceT xT yT) yT))
    _ _ h_no_equal hPerm hCounts
  have hImp := conv_impliesT w e
    (appIf (app1 "TRUE-LISTP" xT) (app1 "TRUE-LISTP" yT) qNilT)
    (equalT (permT xT yT)
      (equalT (howManyT (pceT xT yT) xT) (howManyT (pceT xT yT) yT)))
    _ _ h_no_implies hAnt hConcl
  have hIt := implies_t_of_ne_nil (replayed_pins_ne_nil (hreplayed e) hImp)
  have hEq := eq_of_equal_truthy (truthy_of_implies_t hIt rfl)
  -- decode: `equal` on the two integer atoms IS the counts' `==`
  have hInt : Logic.equal
      (SExpr.atom (.number (.int (howManyL (pceL xs ys) xs))))
      (SExpr.atom (.number (.int (howManyL (pceL xs ys) ys))))
      = (bif (howManyL (pceL xs ys) xs == howManyL (pceL xs ys) ys) then SExpr.t
          else SExpr.nil) := by
    by_cases h : howManyL (pceL xs ys) xs = howManyL (pceL xs ys) ys
    · rw [h]; simp
    · have hi : ¬ ((howManyL (pceL xs ys) xs : Int)
          = (howManyL (pceL xs ys) ys : Int)) := by
        intro hc; exact h (by omega)
      have hne : (howManyL (pceL xs ys) xs
          == howManyL (pceL xs ys) ys) = false := by
        simpa using h
      rw [hne]
      simp [Logic.equal, hi]
  rw [hInt] at hEq
  exact bool_of_cond_eq hEq

end ACL2.Worlds.Sorting
