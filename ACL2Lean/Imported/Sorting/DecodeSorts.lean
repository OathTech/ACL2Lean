import ACL2Lean.Imported.Sorting.Decode

/-! # The sorting books — LAYER 3 (cont.): THE DECODE, sorts

`Decode.lean`'s continuation for the qsort, msort and bsort books —
the headline transports (`orderedp_qsort_native_of_replayed`,
`perm_qsort_native_of_replayed`, `how_many_msort_native_of_replayed`,
…), same discipline, same seam. A separate module only because of the
1500-line module norm.
-/

open ACL2 ACL2.Replay ACL2.Lifting ACL2.Worlds.Perm ACL2.ExecGen

namespace ACL2.Worlds.Sorting

private theorem logic_plus_int (m n : Int) :
    Logic.plus (.atom (.number (.int m))) (.atom (.number (.int n)))
      = .atom (.number (.int (m + n))) := by
  simp [Logic.plus, Logic.toRat, Logic.mkNumber]

/-- The HOW-MANY-APPEND replayed-statement formula:
    `(EQUAL (HOW-MANY E (BINARY-APPEND X Y))
            (BINARY-+ (HOW-MANY E X) (HOW-MANY E Y)))`. -/
def how_many_appendFormula : SExpr :=
  equalT (howManyT eT (appendT xT yT))
    (plusT (howManyT eT xT) (howManyT eT yT))

/-- HOW-MANY-APPEND, natively: `List.count` distributes over `++`. -/
theorem how_many_append_native_of_replayed (w : World)
    (h_hm : w.defs.get? how_many_sym = some ([eS, xS], howManyBody))
    (h_app : w.defs.get? { package := "ACL2", name := "BINARY-APPEND" }
      = some ([{ package := "ACL2", name := "X" },
               { package := "ACL2", name := "Y" }],
              appendBody "BINARY-APPEND"))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env how_many_appendFormula = some v ∧ v ≠ SExpr.nil)
    (ev : SExpr) (xs ys : List SExpr) :
    (xs ++ ys).count ev = xs.count ev + ys.count ev := by
  let e : Env := ((({} : Env).insert yS (enc ys)).insert xS (enc xs)).insert
    eS ev
  have he : ∃ N, ∀ f ≥ N, evalOpt f w e eT = some ev :=
    re_val_var_get w e { name := "E" } ev (by
      show e.get? eS = some ev
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS
            (enc xs)).insert eS ev from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS
            (enc xs)).insert eS ev from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f w e yT = some (enc ys) :=
    re_val_var_get w e { name := "Y" } (enc ys) (by
      show e.get? yS = some (enc ys)
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS
            (enc xs)).insert eS ev from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  have happ := corr_append_enc w "BINARY-APPEND" (by decide) h_app
    h_no_consp h_no_cdr h_no_car h_no_cons xs e xT yT ys hx hy
  have hL := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e eT (appendT xT yT) ev (enc (xs ++ ys)) he happ
  rw [howManyExec_enc] at hL
  have hcx := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e eT xT ev (enc xs) he hx
  rw [howManyExec_enc] at hcx
  have hcy := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e eT yT ev (enc ys) he hy
  rw [howManyExec_enc] at hcy
  have hR := conv_plusT w e (howManyT eT xT) (howManyT eT yT) _ _ h_no_plus
    hcx hcy
  rw [logic_plus_int] at hR
  have hnat := native_of_replayed_equal w e intRep _ _
    ((xs ++ ys).count ev : Int) ((xs.count ev : Int) + (ys.count ev : Int))
    h_no_equal hL hR (hreplayed e)
  omega

/-- The CAR-APPEND replayed-statement formula:
    `(EQUAL (CAR (BINARY-APPEND A B)) (IF (CONSP A) (CAR A) (CAR B)))`. -/
def car_appendFormula : SExpr :=
  equalT (carT (appendT aT bT))
    (ifT (conspT aT) (carT aT) (carT bT))

/-- CAR-APPEND's native right-hand side. -/
def carAppendSpec (xs ys : List SExpr) : SExpr :=
  match xs with
  | [] => ys.headD SExpr.nil
  | a :: _ => a

/-- CAR-APPEND, natively: the head of an append — the left head when the
    left is a cons, else the right head. -/
theorem car_append_native_of_replayed (w : World)
    (h_app : w.defs.get? { package := "ACL2", name := "BINARY-APPEND" }
      = some ([{ package := "ACL2", name := "X" },
               { package := "ACL2", name := "Y" }],
              appendBody "BINARY-APPEND"))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env car_appendFormula = some v ∧ v ≠ SExpr.nil)
    (xs ys : List SExpr) :
    (xs ++ ys).headD SExpr.nil = carAppendSpec xs ys := by
  let e : Env := (({} : Env).insert bS (enc ys)).insert aS (enc xs)
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some (enc xs) :=
    re_val_var_get w e { name := "A" } (enc xs) (by
      show e.get? aS = some (enc xs)
      rw [show e = (({} : Env).insert bS (enc ys)).insert aS (enc xs)
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hb : ∃ N, ∀ f ≥ N, evalOpt f w e bT = some (enc ys) :=
    re_val_var_get w e { name := "B" } (enc ys) (by
      show e.get? bS = some (enc ys)
      rw [show e = (({} : Env).insert bS (enc ys)).insert aS (enc xs)
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have happ := corr_append_enc w "BINARY-APPEND" (by decide) h_app
    h_no_consp h_no_cdr h_no_car h_no_cons xs e aT bT ys ha hb
  have hL := conv_builtin1 w e { name := "CAR" } (appendT aT bT)
    (enc (xs ++ ys)) (Logic.car (enc (xs ++ ys))) (by decide) h_no_car
    happ (callBuiltin_car _)
  have hconsp := conv_builtin1 w e { name := "CONSP" } aT (enc xs)
    (Logic.consp (enc xs)) (by decide) h_no_consp ha (callBuiltin_consp _)
  have hcarB : ∃ N, ∀ f ≥ N, evalOpt f w e (carT bT)
      = some (Logic.car (enc ys)) :=
    conv_builtin1 w e { name := "CAR" } bT (enc ys) (Logic.car (enc ys))
      (by decide) h_no_car hb (callBuiltin_car _)
  have hR : ∃ N, ∀ f ≥ N, evalOpt f w e
      (ifT (conspT aT) (carT aT) (carT bT))
      = some (carAppendSpec xs ys) := by
    match xs with
    | [] =>
      have := conv_if_false' w e (conspT aT) (carT aT) (carT bT)
        (Logic.car (enc ys)) hconsp hcarB
      rw [car_enc] at this
      exact this
    | a :: t =>
      have hcarA : ∃ N, ∀ f ≥ N, evalOpt f w e (carT aT) = some a := by
        have h0 := conv_builtin1 w e { name := "CAR" } aT (enc (a :: t))
          (Logic.car (enc (a :: t))) (by decide) h_no_car ha
          (callBuiltin_car _)
        simpa [enc, Logic.car] using h0
      exact conv_if_true w e (conspT aT) (carT aT) (carT bT)
        (Logic.consp (enc (a :: t))) a hconsp rfl hcarA
  have hnat := native_of_replayed_equal w e idRep _ _
    (Logic.car (enc (xs ++ ys))) (carAppendSpec xs ys) h_no_equal hL hR
    (hreplayed e)
  rw [← car_enc]
  exact hnat

/-! ## PERM-IMPLIES-EQUAL-ALL-REL-2 -/

/-- The replayed-statement formula:
    `(IMPLIES (PERM X X-EQUIV)
              (EQUAL (ALL-REL FN X E) (ALL-REL FN X-EQUIV E)))`. -/
def perm_implies_equal_all_rel_2Formula : SExpr :=
  impliesT (permT xT xEquivT)
    (equalT (allRelT fnT xT eT) (allRelT fnT xEquivT eT))

/-- PERM-IMPLIES-EQUAL-ALL-REL-2, natively: `allRelL` is invariant under
    permutation (ACL2's defcong, over `isPerm`). -/
theorem perm_implies_equal_all_rel_2_native_of_replayed (w : World)
    (h_perm : w.defs.get? { package := "ACL2", name := "PERM" }
      = some ([{ package := "ACL2", name := "X" },
               { package := "ACL2", name := "Y" }], permBody))
    (h_memb : w.defs.get? { package := "ACL2", name := "MEMB" }
      = some ([{ package := "ACL2", name := "A" },
               { package := "ACL2", name := "X" }], membBody))
    (h_rm : w.defs.get? { package := "ACL2", name := "RM" }
      = some ([{ package := "ACL2", name := "E" },
               { package := "ACL2", name := "X" }], rmBody))
    (h_rel : w.defs.get? rel_sym = some ([fnS, iS, jS], relBody))
    (h_ar : w.defs.get? all_rel_sym = some ([fnS, xS, eS], allRelBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env perm_implies_equal_all_rel_2Formula = some v ∧
      v ≠ SExpr.nil)
    (fv ev : SExpr) (xs ys : List SExpr)
    (hp : xs.isPerm ys = true) :
    allRelL fv ev xs = allRelL fv ev ys := by
  let e : Env := (((({} : Env).insert eS ev).insert fnS fv).insert
    xEquivS (enc ys)).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = (((({} : Env).insert eS ev).insert fnS fv).insert
            xEquivS (enc ys)).insert xS (enc xs) from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hxe : ∃ N, ∀ f ≥ N, evalOpt f w e xEquivT = some (enc ys) :=
    re_val_var_get w e { name := "X-EQUIV" } (enc ys) (by
      show e.get? xEquivS = some (enc ys)
      rw [show e = (((({} : Env).insert eS ev).insert fnS fv).insert
            xEquivS (enc ys)).insert xS (enc xs) from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hfn : ∃ N, ∀ f ≥ N, evalOpt f w e fnT = some fv :=
    re_val_var_get w e { name := "FN" } fv (by
      show e.get? fnS = some fv
      rw [show e = (((({} : Env).insert eS ev).insert fnS fv).insert
            xEquivS (enc ys)).insert xS (enc xs) from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  have hev : ∃ N, ∀ f ≥ N, evalOpt f w e eT = some ev :=
    re_val_var_get w e { name := "E" } ev (by
      show e.get? eS = some ev
      rw [show e = (((({} : Env).insert eS ev).insert fnS fv).insert
            xEquivS (enc ys)).insert xS (enc xs) from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_neg (by decide),
          Env.get?_insert, if_pos (by decide)])
  -- antecedent: (perm x x-equiv) computes isPerm = t
  have hP : ∃ N, ∀ f ≥ N, evalOpt f w e (permT xT xEquivT)
      = some SExpr.t := by
    have h := corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal
      h_no_car h_no_cdr h_no_cons xs ys e xT xEquivT hx hxe
    simpa only [hp, cond_true] using h
  -- consequent: equal of the two all-rel values
  have hL := all_rel_exec_corr w h_rel h_ar h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_lexorder e fnT xT eT fv (enc xs) ev hfn hx hev
  rw [allRelExec_enc] at hL
  have hR := all_rel_exec_corr w h_rel h_ar h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_lexorder e fnT xEquivT eT fv (enc ys) ev hfn hxe hev
  rw [allRelExec_enc] at hR
  have hEq := conv_builtin2 w e { name := "EQUAL" } _ _ _ _ _ (by decide)
    h_no_equal hL hR (callBuiltin_equal _ _)
  have hImp := conv_builtin2 w e { name := "IMPLIES" } _ _ _ _ _ (by decide)
    h_no_implies hP hEq (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (replayed_pins_ne_nil (hreplayed e) hImp)
  have hconc := truthy_of_implies_t hIt rfl
  exact bool_of_cond_eq (eq_of_equal_truthy hconc)

/-! ## ALL-REL-RM-1 / ALL-REL-RM-2 -/

/-- `(IMPLIES (ALL-REL FN X E) (ALL-REL FN (RM D X) E))`. -/
def all_rel_rm_1Formula : SExpr :=
  impliesT (allRelT fnT xT eT) (allRelT fnT (rmT dT xT) eT)

/-- `(IMPLIES (IF (ALL-REL FN (RM D X) E) (REL FN D E) 'NIL)
              (ALL-REL FN X E))` — the AND if-expanded. -/
def all_rel_rm_2Formula : SExpr :=
  impliesT
    (ifT (allRelT fnT (rmT dT xT) eT) (relT fnT dT eT) qNil)
    (allRelT fnT xT eT)

/-- The shared env for the two RM rows: FN/X/E/D. -/
private def rmRowEnv (fv ev dv : SExpr) (xs : List SExpr) : Env :=
  (((({} : Env).insert dS dv).insert eS ev).insert fnS fv).insert
    xS (enc xs)

private theorem rmRow_hx (w : World) (fv ev dv : SExpr) (xs : List SExpr) :
    ∃ N, ∀ f ≥ N, evalOpt f w (rmRowEnv fv ev dv xs) xT
      = some (enc xs) :=
  re_val_var_get w _ { name := "X" } (enc xs) (by
    show (rmRowEnv fv ev dv xs).get? xS = some (enc xs)
    rw [rmRowEnv, Env.get?_insert, if_pos (by decide)])

private theorem rmRow_hfn (w : World) (fv ev dv : SExpr) (xs : List SExpr) :
    ∃ N, ∀ f ≥ N, evalOpt f w (rmRowEnv fv ev dv xs) fnT = some fv :=
  re_val_var_get w _ { name := "FN" } fv (by
    show (rmRowEnv fv ev dv xs).get? fnS = some fv
    rw [rmRowEnv, Env.get?_insert, if_neg (by decide), Env.get?_insert,
        if_pos (by decide)])

private theorem rmRow_he (w : World) (fv ev dv : SExpr) (xs : List SExpr) :
    ∃ N, ∀ f ≥ N, evalOpt f w (rmRowEnv fv ev dv xs) eT = some ev :=
  re_val_var_get w _ { name := "E" } ev (by
    show (rmRowEnv fv ev dv xs).get? eS = some ev
    rw [rmRowEnv, Env.get?_insert, if_neg (by decide), Env.get?_insert,
        if_neg (by decide), Env.get?_insert, if_pos (by decide)])

private theorem rmRow_hd (w : World) (fv ev dv : SExpr) (xs : List SExpr) :
    ∃ N, ∀ f ≥ N, evalOpt f w (rmRowEnv fv ev dv xs) dT = some dv :=
  re_val_var_get w _ { name := "D" } dv (by
    show (rmRowEnv fv ev dv xs).get? dS = some dv
    rw [rmRowEnv, Env.get?_insert, if_neg (by decide), Env.get?_insert,
        if_neg (by decide), Env.get?_insert, if_neg (by decide),
        Env.get?_insert, if_pos (by decide)])

/-- ALL-REL-RM-1, natively: a universally `relL`-related list stays so
    after erasing an element. -/
theorem all_rel_rm_1_native_of_replayed (w : World)
    (h_rel : w.defs.get? rel_sym = some ([fnS, iS, jS], relBody))
    (h_ar : w.defs.get? all_rel_sym = some ([fnS, xS, eS], allRelBody))
    (h_rm : w.defs.get? { package := "ACL2", name := "RM" }
      = some ([{ package := "ACL2", name := "E" },
               { package := "ACL2", name := "X" }], rmBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env all_rel_rm_1Formula = some v ∧ v ≠ SExpr.nil)
    (fv ev dv : SExpr) (xs : List SExpr)
    (h : allRelL fv ev xs = true) :
    allRelL fv ev (xs.erase dv) = true := by
  let e := rmRowEnv fv ev dv xs
  have hP := all_rel_exec_corr w h_rel h_ar h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_lexorder e fnT xT eT fv (enc xs) ev
    (rmRow_hfn w fv ev dv xs) (rmRow_hx w fv ev dv xs)
    (rmRow_he w fv ev dv xs)
  rw [allRelExec_enc] at hP
  have hrm := corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr
    h_no_cons xs e dT xT dv (rmRow_hd w fv ev dv xs)
    (rmRow_hx w fv ev dv xs)
  have hC := all_rel_exec_corr w h_rel h_ar h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_lexorder e fnT (rmT dT xT) eT fv (enc (xs.erase dv)) ev
    (rmRow_hfn w fv ev dv xs) hrm (rmRow_he w fv ev dv xs)
  rw [allRelExec_enc] at hC
  have hImp := conv_builtin2 w e { name := "IMPLIES" } _ _ _ _ _ (by decide)
    h_no_implies hP hC (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (replayed_pins_ne_nil (hreplayed e) hImp)
  have hp : Logic.toBool (boolEnc (allRelL fv ev xs)) = true := by
    rw [h]; rfl
  exact bool_true_of_cond_truthy (truthy_of_implies_t hIt hp)

/-- ALL-REL-RM-2, natively: restoring an erased `relL`-related element
    keeps the list universally related. -/
theorem all_rel_rm_2_native_of_replayed (w : World)
    (h_rel : w.defs.get? rel_sym = some ([fnS, iS, jS], relBody))
    (h_ar : w.defs.get? all_rel_sym = some ([fnS, xS, eS], allRelBody))
    (h_rm : w.defs.get? { package := "ACL2", name := "RM" }
      = some ([{ package := "ACL2", name := "E" },
               { package := "ACL2", name := "X" }], rmBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env all_rel_rm_2Formula = some v ∧ v ≠ SExpr.nil)
    (fv ev dv : SExpr) (xs : List SExpr)
    (h1 : allRelL fv ev (xs.erase dv) = true)
    (h2 : relL fv dv ev = true) :
    allRelL fv ev xs = true := by
  let e := rmRowEnv fv ev dv xs
  have hrm := corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr
    h_no_cons xs e dT xT dv (rmRow_hd w fv ev dv xs)
    (rmRow_hx w fv ev dv xs)
  have hAr := all_rel_exec_corr w h_rel h_ar h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_lexorder e fnT (rmT dT xT) eT fv (enc (xs.erase dv)) ev
    (rmRow_hfn w fv ev dv xs) hrm (rmRow_he w fv ev dv xs)
  rw [allRelExec_enc] at hAr
  have hRel := rel_exec_corr w h_rel h_no_equal h_no_lexorder e
    fnT dT eT fv dv ev (rmRow_hfn w fv ev dv xs) (rmRow_hd w fv ev dv xs)
    (rmRow_he w fv ev dv xs)
  have hAnte : ∃ N, ∀ f ≥ N, evalOpt f w e
      (ifT (allRelT fnT (rmT dT xT) eT) (relT fnT dT eT) qNil)
      = some (relExec fv dv ev) := by
    refine conv_if_true w e _ _ qNil (boolEnc (allRelL fv ev (xs.erase dv)))
      (relExec fv dv ev) hAr ?_ hRel
    rw [h1]; rfl
  have hC := all_rel_exec_corr w h_rel h_ar h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_lexorder e fnT xT eT fv (enc xs) ev
    (rmRow_hfn w fv ev dv xs) (rmRow_hx w fv ev dv xs)
    (rmRow_he w fv ev dv xs)
  rw [allRelExec_enc] at hC
  have hImp := conv_builtin2 w e { name := "IMPLIES" } _ _ _ _ _ (by decide)
    h_no_implies hAnte hC (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (replayed_pins_ne_nil (hreplayed e) hImp)
  have hp : Logic.toBool (relExec fv dv ev) = true := by
    rw [toBool_relExec, h2]
  exact bool_true_of_cond_truthy (truthy_of_implies_t hIt hp)

/-! ## ALL-REL-FILTER-1 / ALL-REL-FILTER-2 / HOW-MANY-FILTER-1 -/

/-- `(ALL-REL 'LTE (FILTER 'LT X E) E)`. -/
def all_rel_filter_1Formula : SExpr :=
  allRelT (qSym "LTE") (filterT (qSym "LT") xT eT) eT

/-- `(ALL-REL 'GTE (FILTER 'GTE X E) E)`. -/
def all_rel_filter_2Formula : SExpr :=
  allRelT (qSym "GTE") (filterT (qSym "GTE") xT eT) eT

private def xeEnv (ev : SExpr) (xs : List SExpr) : Env :=
  (({} : Env).insert eS ev).insert xS (enc xs)

private theorem xeEnv_hx (w : World) (ev : SExpr) (xs : List SExpr) :
    ∃ N, ∀ f ≥ N, evalOpt f w (xeEnv ev xs) xT = some (enc xs) :=
  re_val_var_get w _ { name := "X" } (enc xs) (by
    show (xeEnv ev xs).get? xS = some (enc xs)
    rw [xeEnv, Env.get?_insert, if_pos (by decide)])

private theorem xeEnv_he (w : World) (ev : SExpr) (xs : List SExpr) :
    ∃ N, ∀ f ≥ N, evalOpt f w (xeEnv ev xs) eT = some ev :=
  re_val_var_get w _ { name := "E" } ev (by
    show (xeEnv ev xs).get? eS = some ev
    rw [xeEnv, Env.get?_insert, if_neg (by decide), Env.get?_insert,
        if_pos (by decide)])

/-- ALL-REL-FILTER-1, natively: everything the strict-lexorder filter
    keeps is lexorder-below the pivot. -/
theorem all_rel_filter_1_native_of_replayed (w : World)
    (h_rel : w.defs.get? rel_sym = some ([fnS, iS, jS], relBody))
    (h_ar : w.defs.get? all_rel_sym = some ([fnS, xS, eS], allRelBody))
    (h_filter : w.defs.get? filter_sym = some ([fnS, xS, eS], filterBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env all_rel_filter_1Formula = some v ∧ v ≠ SExpr.nil)
    (ev : SExpr) (xs : List SExpr) :
    (xs.filter (fun a => lexLtB a ev)).all (fun a => lexorderB a ev)
      = true := by
  let e := xeEnv ev xs
  have hfil := filter_exec_corr w h_rel h_filter h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons h_no_lexorder e (qSym "LT") xT eT
    (symV "LT") (enc xs) ev (re_val_quote w e (symV "LT"))
    (xeEnv_hx w ev xs) (xeEnv_he w ev xs)
  rw [filterExec_enc] at hfil
  have hAr := all_rel_exec_corr w h_rel h_ar h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_lexorder e (qSym "LTE")
    (filterT (qSym "LT") xT eT) eT (symV "LTE")
    (enc (filterL (symV "LT") ev xs)) ev (re_val_quote w e (symV "LTE"))
    hfil (xeEnv_he w ev xs)
  rw [allRelExec_enc] at hAr
  have h := bool_true_of_cond_truthy (toBool_true_of_ne_nil
    (replayed_pins_ne_nil (hreplayed e) hAr))
  simpa only [allRelL, filterL, relL_LTE, relL_LT] using h

/-- ALL-REL-FILTER-2, natively: everything the reverse-lexorder filter
    keeps is lexorder-above the pivot. -/
theorem all_rel_filter_2_native_of_replayed (w : World)
    (h_rel : w.defs.get? rel_sym = some ([fnS, iS, jS], relBody))
    (h_ar : w.defs.get? all_rel_sym = some ([fnS, xS, eS], allRelBody))
    (h_filter : w.defs.get? filter_sym = some ([fnS, xS, eS], filterBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env all_rel_filter_2Formula = some v ∧ v ≠ SExpr.nil)
    (ev : SExpr) (xs : List SExpr) :
    (xs.filter (fun a => lexorderB ev a)).all (fun a => lexorderB ev a)
      = true := by
  let e := xeEnv ev xs
  have hfil := filter_exec_corr w h_rel h_filter h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons h_no_lexorder e (qSym "GTE") xT eT
    (symV "GTE") (enc xs) ev (re_val_quote w e (symV "GTE"))
    (xeEnv_hx w ev xs) (xeEnv_he w ev xs)
  rw [filterExec_enc] at hfil
  have hAr := all_rel_exec_corr w h_rel h_ar h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_lexorder e (qSym "GTE")
    (filterT (qSym "GTE") xT eT) eT (symV "GTE")
    (enc (filterL (symV "GTE") ev xs)) ev (re_val_quote w e (symV "GTE"))
    hfil (xeEnv_he w ev xs)
  rw [allRelExec_enc] at hAr
  have h := bool_true_of_cond_truthy (toBool_true_of_ne_nil
    (replayed_pins_ne_nil (hreplayed e) hAr))
  simpa only [allRelL, filterL, relL_GTE] using h

/-- `(EQUAL (BINARY-+ (HOW-MANY E (FILTER 'LT X D))
                      (HOW-MANY E (FILTER 'GTE X D)))
            (HOW-MANY E X))`. -/
def how_many_filter_1Formula : SExpr :=
  equalT
    (plusT (howManyT eT (filterT (qSym "LT") xT dT))
           (howManyT eT (filterT (qSym "GTE") xT dT)))
    (howManyT eT xT)

/-- HOW-MANY-FILTER-1, natively: the LT/GTE filters PARTITION every
    element's multiplicity — the count below the pivot plus the count
    at-or-above it is the whole count. -/
theorem how_many_filter_1_native_of_replayed (w : World)
    (h_hm : w.defs.get? how_many_sym = some ([eS, xS], howManyBody))
    (h_rel : w.defs.get? rel_sym = some ([fnS, iS, jS], relBody))
    (h_filter : w.defs.get? filter_sym = some ([fnS, xS, eS], filterBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env how_many_filter_1Formula = some v ∧ v ≠ SExpr.nil)
    (ev dv : SExpr) (xs : List SExpr) :
    (xs.filter (fun a => lexLtB a dv)).count ev
      + (xs.filter (fun a => lexorderB dv a)).count ev
      = xs.count ev := by
  let e' : Env := ((({} : Env).insert dS dv).insert eS ev).insert
    xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e' xT = some (enc xs) :=
    re_val_var_get w e' { name := "X" } (enc xs) (by
      show e'.get? xS = some (enc xs)
      rw [show e' = ((({} : Env).insert dS dv).insert eS ev).insert
            xS (enc xs) from rfl,
          Env.get?_insert, if_pos (by decide)])
  have he : ∃ N, ∀ f ≥ N, evalOpt f w e' eT = some ev :=
    re_val_var_get w e' { name := "E" } ev (by
      show e'.get? eS = some ev
      rw [show e' = ((({} : Env).insert dS dv).insert eS ev).insert
            xS (enc xs) from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hd : ∃ N, ∀ f ≥ N, evalOpt f w e' dT = some dv :=
    re_val_var_get w e' { name := "D" } dv (by
      show e'.get? dS = some dv
      rw [show e' = ((({} : Env).insert dS dv).insert eS ev).insert
            xS (enc xs) from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  have hfilLT := filter_exec_corr w h_rel h_filter h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons h_no_lexorder e' (qSym "LT") xT dT
    (symV "LT") (enc xs) dv (re_val_quote w e' (symV "LT")) hx hd
  rw [filterExec_enc] at hfilLT
  have hfilGTE := filter_exec_corr w h_rel h_filter h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons h_no_lexorder e' (qSym "GTE") xT dT
    (symV "GTE") (enc xs) dv (re_val_quote w e' (symV "GTE")) hx hd
  rw [filterExec_enc] at hfilGTE
  have hcLT := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e' eT (filterT (qSym "LT") xT dT) ev
    (enc (filterL (symV "LT") dv xs)) he hfilLT
  rw [howManyExec_enc] at hcLT
  have hcGTE := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e' eT (filterT (qSym "GTE") xT dT) ev
    (enc (filterL (symV "GTE") dv xs)) he hfilGTE
  rw [howManyExec_enc] at hcGTE
  have hL := conv_plusT w e' _ _ _ _ h_no_plus hcLT hcGTE
  rw [logic_plus_int] at hL
  have hR := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e' eT xT ev (enc xs) he hx
  rw [howManyExec_enc] at hR
  have hnat := native_of_replayed_equal w e' intRep _ _
    (((filterL (symV "LT") dv xs).count ev : Int)
      + ((filterL (symV "GTE") dv xs).count ev : Int))
    ((xs.count ev : Int)) h_no_equal hL hR (hreplayed e')
  have hLT : filterL (symV "LT") dv xs
      = xs.filter (fun a => lexLtB a dv) := by
    simp only [filterL, relL_LT]
  have hGTE : filterL (symV "GTE") dv xs
      = xs.filter (fun a => lexorderB dv a) := by
    simp only [filterL, relL_GTE]
  rw [hLT, hGTE] at hnat
  omega

/-- The ORDEREDP-APPEND replayed-statement formula — the root Goal
    clause (the AND if-expanded, APPEND macroexpanded):
    `(IMPLIES (ORDEREDP A)
       (IFF (ORDEREDP (BINARY-APPEND A (CONS E B)))
            (IF (ORDEREDP B)
                (IF (ALL-REL 'LTE A E) (ALL-REL 'GTE B E) 'NIL)
                'NIL)))`. -/
def orderedp_appendFormula : SExpr :=
  impliesT (orderedpT aT)
    (iffT (orderedpT (appendT aT (consT eT bT)))
      (ifT (orderedpT bT)
        (ifT (allRelT (qSym "LTE") aT eT) (allRelT (qSym "GTE") bT eT)
          qNil)
        qNil))

/-- ORDEREDP-APPEND, natively: for sorted `as`, the append
    `as ++ ev :: bs` is sorted EXACTLY when `bs` is sorted, everything
    in `as` is lexorder-below `ev`, and everything in `bs` is
    lexorder-above it — quicksort's assembly step. -/
theorem orderedp_append_native_of_replayed (w : World)
    (h_orderedp : w.defs.get? { package := "ACL2", name := "ORDEREDP" }
      = some ([{ package := "ACL2", name := "X" }],
              chain2Body "LEXORDER" "ORDEREDP"))
    (h_rel : w.defs.get? rel_sym = some ([fnS, iS, jS], relBody))
    (h_ar : w.defs.get? all_rel_sym = some ([fnS, xS, eS], allRelBody))
    (h_app : w.defs.get? append_sym
      = some ([{ package := "ACL2", name := "X" },
               { package := "ACL2", name := "Y" }],
              appendBody "BINARY-APPEND"))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (h_no_iff : w.defs.get? ({ name := "IFF" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env orderedp_appendFormula = some v ∧ v ≠ SExpr.nil)
    (ev : SExpr) (as bs : List SExpr)
    (hord : orderedpRec as = true) :
    orderedpRec (as ++ ev :: bs)
      = (orderedpRec bs
          && ((as.all fun a => lexorderB a ev)
              && (bs.all fun b => lexorderB ev b))) := by
  let e : Env := ((({} : Env).insert bS (enc bs)).insert eS ev).insert
    aS (enc as)
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some (enc as) :=
    re_val_var_get w e { name := "A" } (enc as) (by
      show e.get? aS = some (enc as)
      rw [show e = ((({} : Env).insert bS (enc bs)).insert eS ev).insert
            aS (enc as) from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hev : ∃ N, ∀ f ≥ N, evalOpt f w e eT = some ev :=
    re_val_var_get w e { name := "E" } ev (by
      show e.get? eS = some ev
      rw [show e = ((({} : Env).insert bS (enc bs)).insert eS ev).insert
            aS (enc as) from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hb : ∃ N, ∀ f ≥ N, evalOpt f w e bT = some (enc bs) :=
    re_val_var_get w e { name := "B" } (enc bs) (by
      show e.get? bS = some (enc bs)
      rw [show e = ((({} : Env).insert bS (enc bs)).insert eS ev).insert
            aS (enc as) from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  -- the antecedent
  have hAnte := corr_orderedp_enc w h_orderedp h_no_consp h_no_cdr h_no_car
    h_no_lexorder as e aT ha
  -- iff LHS: orderedp of the append
  have hcons : ∃ N, ∀ f ≥ N, evalOpt f w e (consT eT bT)
      = some (enc (ev :: bs)) :=
    conv_builtin2 w e { name := "CONS" } eT bT ev (enc bs)
      (enc (ev :: bs)) (by decide) h_no_cons hev hb rfl
  have happ := corr_append_enc w "BINARY-APPEND" (by decide) h_app
    h_no_consp h_no_cdr h_no_car h_no_cons as e aT (consT eT bT)
    (ev :: bs) ha hcons
  have hL := corr_orderedp_enc w h_orderedp h_no_consp h_no_cdr h_no_car
    h_no_lexorder (as ++ ev :: bs) e (appendT aT (consT eT bT)) happ
  -- iff RHS: the three-guard nest
  have h1 := corr_orderedp_enc w h_orderedp h_no_consp h_no_cdr h_no_car
    h_no_lexorder bs e bT hb
  have h2 := all_rel_exec_corr w h_rel h_ar h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_lexorder e (qSym "LTE") aT eT (symV "LTE") (enc as) ev
    (re_val_quote w e (symV "LTE")) ha hev
  rw [allRelExec_enc] at h2
  have h3 := all_rel_exec_corr w h_rel h_ar h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_lexorder e (qSym "GTE") bT eT (symV "GTE") (enc bs) ev
    (re_val_quote w e (symV "GTE")) hb hev
  rw [allRelExec_enc] at h3
  have hR := conv_if3 w e _ _ _ (orderedpRec bs)
    (allRelL (symV "LTE") ev as) (allRelL (symV "GTE") ev bs) h1 h2 h3
  -- compose, pin, project
  have hIff := conv_builtin2 w e { name := "IFF" } _ _ _ _ _ (by decide)
    h_no_iff hL hR (callBuiltin_iff _ _)
  have hImp := conv_builtin2 w e { name := "IMPLIES" } _ _ _ _ _ (by decide)
    h_no_implies hAnte hIff (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (replayed_pins_ne_nil (hreplayed e) hImp)
  have hp : Logic.toBool (boolEnc (orderedpRec as)) = true := by
    rw [hord]; rfl
  have hiff := bool_of_iff_truthy (truthy_of_implies_t hIt hp)
  simpa only [allRelL, relL_LTE, relL_GTE] using hiff

/-! ## The msort row assemblies -/

/-- `(EQUAL (HOW-MANY E (MERGE2 X Y))
            (BINARY-+ (HOW-MANY E X) (HOW-MANY E Y)))`. -/
def how_many_merge2Formula : SExpr :=
  equalT (howManyT eT (merge2T xT yT))
    (plusT (howManyT eT xT) (howManyT eT yT))

/-- HOW-MANY-MERGE2, natively: merging adds multiplicities. -/
theorem how_many_merge2_native_of_replayed (w : World)
    (h_hm : w.defs.get? how_many_sym = some ([eS, xS], howManyBody))
    (h_m2 : w.defs.get? merge2_sym = some ([xS, yS], merge2Body))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env how_many_merge2Formula = some v ∧ v ≠ SExpr.nil)
    (ev : SExpr) (xs ys : List SExpr) :
    (merge2L xs ys).count ev = xs.count ev + ys.count ev := by
  let e : Env := ((({} : Env).insert yS (enc ys)).insert xS
    (enc xs)).insert eS ev
  have he : ∃ N, ∀ f ≥ N, evalOpt f w e eT = some ev :=
    re_val_var_get w e { name := "E" } ev (by
      show e.get? eS = some ev
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS
            (enc xs)).insert eS ev from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS
            (enc xs)).insert eS ev from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f w e yT = some (enc ys) :=
    re_val_var_get w e { name := "Y" } (enc ys) (by
      show e.get? yS = some (enc ys)
      rw [show e = ((({} : Env).insert yS (enc ys)).insert xS
            (enc xs)).insert eS ev from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  have hm2 := merge2_exec_corr w h_m2 h_no_consp h_no_car h_no_cdr
    h_no_cons h_no_lexorder e xT yT (enc xs) (enc ys) hx hy
  rw [merge2Exec_enc] at hm2
  have hL := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e eT (merge2T xT yT) ev (enc (merge2L xs ys)) he hm2
  rw [howManyExec_enc] at hL
  have hcx := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e eT xT ev (enc xs) he hx
  rw [howManyExec_enc] at hcx
  have hcy := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e eT yT ev (enc ys) he hy
  rw [howManyExec_enc] at hcy
  have hR := conv_plusT w e _ _ _ _ h_no_plus hcx hcy
  rw [logic_plus_int] at hR
  have hnat := native_of_replayed_equal w e intRep _ _
    ((merge2L xs ys).count ev : Int)
    ((xs.count ev : Int) + (ys.count ev : Int)) h_no_equal hL hR
    (hreplayed e)
  omega

/-- `(IMPLIES (CONSP X)
       (EQUAL (BINARY-+ (HOW-MANY E (EVENS X)) (HOW-MANY E (EVENS (CDR X))))
              (HOW-MANY E X)))`. -/
def how_many_evens_and_oddsFormula : SExpr :=
  impliesT (conspT xT)
    (equalT
      (plusT (howManyT eT (evensT xT)) (howManyT eT (evensT (cdrT xT))))
      (howManyT eT xT))

/-- HOW-MANY-EVENS-AND-ODDS, natively (at the cons instance, where the
    hypothesis has content): the evens/odds split partitions every
    element's multiplicity. -/
theorem how_many_evens_and_odds_native_of_replayed (w : World)
    (h_hm : w.defs.get? how_many_sym = some ([eS, xS], howManyBody))
    (h_evens : w.defs.get? evens_sym = some ([lS], evensBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env how_many_evens_and_oddsFormula = some v ∧
      v ≠ SExpr.nil)
    (ev a : SExpr) (t : List SExpr) :
    (evensL (a :: t)).count ev + (evensL t).count ev
      = (a :: t).count ev := by
  let e : Env := (({} : Env).insert eS ev).insert xS (enc (a :: t))
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc (a :: t)) :=
    re_val_var_get w e { name := "X" } (enc (a :: t)) (by
      show e.get? xS = some (enc (a :: t))
      rw [show e = (({} : Env).insert eS ev).insert xS (enc (a :: t))
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have he : ∃ N, ∀ f ≥ N, evalOpt f w e eT = some ev :=
    re_val_var_get w e { name := "E" } ev (by
      show e.get? eS = some ev
      rw [show e = (({} : Env).insert eS ev).insert xS (enc (a :: t))
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hconsp : ∃ N, ∀ f ≥ N, evalOpt f w e (conspT xT) = some SExpr.t := by
    have h0 := conv_builtin1 w e { name := "CONSP" } xT (enc (a :: t))
      (Logic.consp (enc (a :: t))) (by decide) h_no_consp hx
      (callBuiltin_consp _)
    simpa [enc, Logic.consp] using h0
  have hcdr : ∃ N, ∀ f ≥ N, evalOpt f w e (cdrT xT) = some (enc t) := by
    have h0 := conv_builtin1 w e { name := "CDR" } xT (enc (a :: t))
      (Logic.cdr (enc (a :: t))) (by decide) h_no_cdr hx (callBuiltin_cdr _)
    simpa [enc, Logic.cdr] using h0
  have hev1 := evens_exec_corr w h_evens h_no_consp h_no_car h_no_cdr
    h_no_cons e xT (enc (a :: t)) hx
  rw [evensExec_enc] at hev1
  have hev2 := evens_exec_corr w h_evens h_no_consp h_no_car h_no_cdr
    h_no_cons e (cdrT xT) (enc t) hcdr
  rw [evensExec_enc] at hev2
  have hc1 := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e eT (evensT xT) ev (enc (evensL (a :: t))) he hev1
  rw [howManyExec_enc] at hc1
  have hc2 := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e eT (evensT (cdrT xT)) ev (enc (evensL t)) he hev2
  rw [howManyExec_enc] at hc2
  have hplus := conv_plusT w e _ _ _ _ h_no_plus hc1 hc2
  rw [logic_plus_int] at hplus
  have hcx := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e eT xT ev (enc (a :: t)) he hx
  rw [howManyExec_enc] at hcx
  have hEq := conv_builtin2 w e { name := "EQUAL" } _ _ _ _ _ (by decide)
    h_no_equal hplus hcx (callBuiltin_equal _ _)
  have hImp := conv_builtin2 w e { name := "IMPLIES" } _ _ _ _ _ (by decide)
    h_no_implies hconsp hEq (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (replayed_pins_ne_nil (hreplayed e) hImp)
  have hconc := eq_of_equal_truthy (truthy_of_implies_t hIt rfl)
  have := int_atom_inj hconc
  omega

/-- `(ORDEREDP (MSORT X))`. -/
def orderedp_msortFormula : SExpr := orderedpT (msortT xT)

/-- ORDEREDP-MSORT, natively: MERGE SORT ALWAYS SORTS. -/
theorem orderedp_msort_native_of_replayed (w : World)
    (h_orderedp : w.defs.get? { package := "ACL2", name := "ORDEREDP" }
      = some ([{ package := "ACL2", name := "X" }],
              chain2Body "LEXORDER" "ORDEREDP"))
    (h_m2 : w.defs.get? merge2_sym = some ([xS, yS], merge2Body))
    (h_evens : w.defs.get? evens_sym = some ([lS], evensBody))
    (h_odds : w.defs.get? odds_sym = some ([lS], oddsBody))
    (h_msort : w.defs.get? msort_sym = some ([xS], msortBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env orderedp_msortFormula = some v ∧ v ≠ SExpr.nil)
    (xs : List SExpr) :
    orderedpRec (msortL xs) = true := by
  let e : Env := ({} : Env).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ({} : Env).insert xS (enc xs) from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hms := msort_exec_corr w h_m2 h_evens h_odds h_msort h_no_consp
    h_no_car h_no_cdr h_no_cons h_no_lexorder e xT (enc xs) hx
  rw [msortExec_enc] at hms
  have hord := corr_orderedp_enc w h_orderedp h_no_consp h_no_cdr h_no_car
    h_no_lexorder (msortL xs) e (msortT xT) hms
  exact bool_true_of_cond_truthy (toBool_true_of_ne_nil
    (replayed_pins_ne_nil (hreplayed e) hord))

/-- `(EQUAL (HOW-MANY E (MSORT X)) (HOW-MANY E X))`. -/
def how_many_msortFormula : SExpr :=
  equalT (howManyT eT (msortT xT)) (howManyT eT xT)

/-- HOW-MANY-MSORT, natively: MERGE SORT PRESERVES MULTIPLICITY. -/
theorem how_many_msort_native_of_replayed (w : World)
    (h_hm : w.defs.get? how_many_sym = some ([eS, xS], howManyBody))
    (h_m2 : w.defs.get? merge2_sym = some ([xS, yS], merge2Body))
    (h_evens : w.defs.get? evens_sym = some ([lS], evensBody))
    (h_odds : w.defs.get? odds_sym = some ([lS], oddsBody))
    (h_msort : w.defs.get? msort_sym = some ([xS], msortBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env how_many_msortFormula = some v ∧ v ≠ SExpr.nil)
    (ev : SExpr) (xs : List SExpr) :
    (msortL xs).count ev = xs.count ev := by
  let e : Env := (({} : Env).insert xS (enc xs)).insert eS ev
  have he : ∃ N, ∀ f ≥ N, evalOpt f w e eT = some ev :=
    re_val_var_get w e { name := "E" } ev (by
      show e.get? eS = some ev
      rw [show e = (({} : Env).insert xS (enc xs)).insert eS ev from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = (({} : Env).insert xS (enc xs)).insert eS ev from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hms := msort_exec_corr w h_m2 h_evens h_odds h_msort h_no_consp
    h_no_car h_no_cdr h_no_cons h_no_lexorder e xT (enc xs) hx
  rw [msortExec_enc] at hms
  have hL := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e eT (msortT xT) ev (enc (msortL xs)) he hms
  rw [howManyExec_enc] at hL
  have hR := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e eT xT ev (enc xs) he hx
  rw [howManyExec_enc] at hR
  have hnat := native_of_replayed_equal w e intRep _ _
    ((msortL xs).count ev : Int) ((xs.count ev : Int)) h_no_equal hL hR
    (hreplayed e)
  omega

/-! ## HOW-MANY-QSORT -/

/-- `(EQUAL (HOW-MANY E (QSORT X)) (HOW-MANY E X))`. -/
def how_many_qsortFormula : SExpr :=
  equalT (howManyT eT (qsortT xT)) (howManyT eT xT)

/-- HOW-MANY-QSORT, natively: QUICKSORT PRESERVES MULTIPLICITY. -/
theorem how_many_qsort_native_of_replayed (w : World)
    (h_hm : w.defs.get? how_many_sym = some ([eS, xS], howManyBody))
    (h_qs : w.defs.get? qsort_sym = some ([xS], qsortBody))
    (h_rel : w.defs.get? rel_sym = some ([fnS, iS, jS], relBody))
    (h_filter : w.defs.get? filter_sym = some ([fnS, xS, eS], filterBody))
    (h_app : w.defs.get? append_sym
      = some ([{ package := "ACL2", name := "X" },
               { package := "ACL2", name := "Y" }],
              appendBody "BINARY-APPEND"))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env how_many_qsortFormula = some v ∧ v ≠ SExpr.nil)
    (ev : SExpr) (xs : List SExpr) :
    (qsortL xs).count ev = xs.count ev := by
  let e : Env := (({} : Env).insert xS (enc xs)).insert eS ev
  have he : ∃ N, ∀ f ≥ N, evalOpt f w e eT = some ev :=
    re_val_var_get w e { name := "E" } ev (by
      show e.get? eS = some ev
      rw [show e = (({} : Env).insert xS (enc xs)).insert eS ev from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = (({} : Env).insert xS (enc xs)).insert eS ev from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hqs := qsort_exec_corr w h_qs h_rel h_filter h_app h_no_consp
    h_no_equal h_no_car h_no_cdr h_no_cons h_no_lexorder e xT (enc xs) hx
  rw [qsortExec_enc] at hqs
  have hL := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e eT (qsortT xT) ev (enc (qsortL xs)) he hqs
  rw [howManyExec_enc] at hL
  have hR := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e eT xT ev (enc xs) he hx
  rw [howManyExec_enc] at hR
  have hnat := native_of_replayed_equal w e intRep _ _
    ((qsortL xs).count ev : Int) ((xs.count ev : Int)) h_no_equal hL hR
    (hreplayed e)
  omega

/-! ## PERM-QSORT -/

/-- `(PERM (QSORT X) X)`. -/
def perm_qsortFormula : SExpr := permT (qsortT xT) xT

/-- PERM-QSORT, natively: QUICKSORT PERMUTES — `qsortL xs` is a
    permutation of `xs`. -/
theorem perm_qsort_native_of_replayed (w : World)
    (h_perm : w.defs.get? { package := "ACL2", name := "PERM" }
      = some ([{ package := "ACL2", name := "X" },
               { package := "ACL2", name := "Y" }], permBody))
    (h_memb : w.defs.get? { package := "ACL2", name := "MEMB" }
      = some ([{ package := "ACL2", name := "A" },
               { package := "ACL2", name := "X" }], membBody))
    (h_rm : w.defs.get? { package := "ACL2", name := "RM" }
      = some ([{ package := "ACL2", name := "E" },
               { package := "ACL2", name := "X" }], rmBody))
    (h_qs : w.defs.get? qsort_sym = some ([xS], qsortBody))
    (h_rel : w.defs.get? rel_sym = some ([fnS, iS, jS], relBody))
    (h_filter : w.defs.get? filter_sym = some ([fnS, xS, eS], filterBody))
    (h_app : w.defs.get? append_sym
      = some ([{ package := "ACL2", name := "X" },
               { package := "ACL2", name := "Y" }],
              appendBody "BINARY-APPEND"))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env perm_qsortFormula = some v ∧ v ≠ SExpr.nil)
    (xs : List SExpr) :
    (qsortL xs).isPerm xs = true := by
  let e : Env := ({} : Env).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ({} : Env).insert xS (enc xs) from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hqs := qsort_exec_corr w h_qs h_rel h_filter h_app h_no_consp
    h_no_equal h_no_car h_no_cdr h_no_cons h_no_lexorder e xT (enc xs) hx
  rw [qsortExec_enc] at hqs
  have hP := corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons (qsortL xs) xs e (qsortT xT) xT hqs hx
  exact bool_true_of_cond_truthy (toBool_true_of_ne_nil
    (replayed_pins_ne_nil (hreplayed e) hP))

/-- `rule:ORDEREDP-APPEND` — the in-book rule, discharged FROM the
    theorem's own replayed statement (both sides two-valued, so the
    replayed IFF pins the values EQUAL). -/
theorem dis_rule_orderedp_append (w : World)
    (h_ord : w.defs.get? orderedp_sym
      = some ([{ package := "ACL2", name := "X" }],
              chain2Body "LEXORDER" "ORDEREDP"))
    (h_rel : w.defs.get? rel_sym = some ([fnS, iS, jS], relBody))
    (h_ar : w.defs.get? all_rel_sym = some ([fnS, xS, eS], allRelBody))
    (h_app : w.defs.get? append_sym
      = some ([{ package := "ACL2", name := "X" },
               { package := "ACL2", name := "Y" }],
              appendBody "BINARY-APPEND"))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (h_no_iff : w.defs.get? ({ name := "IFF" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env orderedp_appendFormula = some v ∧ v ≠ SExpr.nil) :
    ∀ env' : Env, EvTrue w env' (orderedpT aT) →
    ∃ N, ∀ f ≥ N,
      evalOpt f w env' (orderedpT (appendT aT (consT eT bT)))
        = evalOpt f w env'
            (ifT (orderedpT bT)
              (ifT (allRelT (qSym "LTE") aT eT)
                (allRelT (qSym "GTE") bT eT) qNil)
              qNil) := by
  intro env' hyp
  obtain ⟨va, ha⟩ := conv_var w env' aS (by decide)
  obtain ⟨vb, hb⟩ := conv_var w env' bS (by decide)
  obtain ⟨ve, he⟩ := conv_var w env' eS (by decide)
  have hAnte := orderedp_exec_corr w h_ord h_no_consp h_no_car h_no_cdr
    h_no_lexorder env' aT va ha
  -- LHS: orderedp of the append
  have hcons := conv_builtin2 w env' { name := "CONS" } eT bT ve vb
    (Logic.cons ve vb) (by decide) h_no_cons he hb rfl
  have happ := append_exec_corr w h_app h_no_consp h_no_car h_no_cdr
    h_no_cons env' aT (consT eT bT) va (Logic.cons ve vb) ha hcons
  have hL := orderedp_exec_corr w h_ord h_no_consp h_no_car h_no_cdr
    h_no_lexorder env' (appendT aT (consT eT bT))
    (appendExec va (Logic.cons ve vb)) happ
  -- RHS: the if-nest
  have hOrdB := orderedp_exec_corr w h_ord h_no_consp h_no_car h_no_cdr
    h_no_lexorder env' bT vb hb
  have hAr1 := all_rel_exec_corr w h_rel h_ar h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_lexorder env' (qSym "LTE") aT eT (symV "LTE")
    va ve (re_val_quote w env' (symV "LTE")) ha he
  have hAr2 := all_rel_exec_corr w h_rel h_ar h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_lexorder env' (qSym "GTE") bT eT (symV "GTE")
    vb ve (re_val_quote w env' (symV "GTE")) hb he
  have hInner := conv_if_lift w env' (allRelT (qSym "LTE") aT eT)
    (allRelT (qSym "GTE") bT eT) qNil (allRelExec (symV "LTE") va ve)
    (allRelExec (symV "GTE") vb ve) SExpr.nil hAr1
    (fun _ => hAr2) (fun _ => re_val_quote w env' SExpr.nil)
  have hR := conv_if_lift w env' (orderedpT bT) _ qNil (orderedpExec vb)
    (if Logic.toBool (allRelExec (symV "LTE") va ve) = true then
      allRelExec (symV "GTE") vb ve
     else SExpr.nil)
    SExpr.nil hOrdB (fun _ => hInner)
    (fun _ => re_val_quote w env' SExpr.nil)
  -- the replayed IFF pins the two-valued sides equal
  have hIff := conv_builtin2 w env' { name := "IFF" } _ _ _ _ _
    (by decide) h_no_iff hL hR (callBuiltin_iff _ _)
  have hImp := conv_builtin2 w env' { name := "IMPLIES" } _ _ _ _ _
    (by decide) h_no_implies hAnte hIff (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil
    (replayed_pins_ne_nil (hreplayed env') hImp)
  have hp : Logic.toBool (orderedpExec va) = true :=
    toBool_true_of_ne_nil (ne_nil_of_evtrue_conv hyp hAnte)
  have hiff := truthy_of_implies_t hIt hp
  have hRtv : (if Logic.toBool (orderedpExec vb) = true then
      (if Logic.toBool (allRelExec (symV "LTE") va ve) = true then
        allRelExec (symV "GTE") vb ve
       else SExpr.nil)
     else SExpr.nil) = SExpr.t ∨
      (if Logic.toBool (orderedpExec vb) = true then
        (if Logic.toBool (allRelExec (symV "LTE") va ve) = true then
          allRelExec (symV "GTE") vb ve
         else SExpr.nil)
       else SExpr.nil) = SExpr.nil := by
    split
    · split
      · exact allRelExec_t_or_nil _ _ _
      · exact Or.inr rfl
    · exact Or.inr rfl
  exact fuel_eq_of_conv hL hR
    (eq_of_iff_truthy_two_valued (orderedpExec_t_or_nil _) hRtv hiff)

/-! ## ORDEREDP-QSORT -/

/-- `(ORDEREDP (QSORT X))`. -/
def orderedp_qsortFormula : SExpr := orderedpT (qsortT xT)

/-- ORDEREDP-QSORT, natively: QUICKSORT SORTS. -/
theorem orderedp_qsort_native_of_replayed (w : World)
    (h_ord : w.defs.get? orderedp_sym
      = some ([{ package := "ACL2", name := "X" }],
              chain2Body "LEXORDER" "ORDEREDP"))
    (h_qs : w.defs.get? qsort_sym = some ([xS], qsortBody))
    (h_rel : w.defs.get? rel_sym = some ([fnS, iS, jS], relBody))
    (h_filter : w.defs.get? filter_sym = some ([fnS, xS, eS], filterBody))
    (h_app : w.defs.get? append_sym
      = some ([{ package := "ACL2", name := "X" },
               { package := "ACL2", name := "Y" }],
              appendBody "BINARY-APPEND"))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env orderedp_qsortFormula = some v ∧ v ≠ SExpr.nil)
    (xs : List SExpr) :
    orderedpRec (qsortL xs) = true := by
  let e : Env := ({} : Env).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ({} : Env).insert xS (enc xs) from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hqs := qsort_exec_corr w h_qs h_rel h_filter h_app h_no_consp
    h_no_equal h_no_car h_no_cdr h_no_cons h_no_lexorder e xT (enc xs) hx
  rw [qsortExec_enc] at hqs
  have hord := corr_orderedp_enc w h_ord h_no_consp h_no_cdr h_no_car
    h_no_lexorder (qsortL xs) e (qsortT xT) hqs
  exact bool_true_of_cond_truthy (toBool_true_of_ne_nil
    (replayed_pins_ne_nil (hreplayed e) hord))

/-- The HOW-MANY-BNEXT replayed-statement formula:
    `(EQUAL (HOW-MANY E (BNEXT X)) (HOW-MANY E X))`. -/
def how_many_bnextFormula : SExpr :=
  equalT (howManyT eT (app1 "BNEXT" xT)) (howManyT eT xT)

/-- HOW-MANY-BNEXT, natively: the bubble pass preserves `List.count`. -/
theorem how_many_bnext_native_of_replayed (w : World)
    (h_bnext : w.defs.get? bnext_sym = some ([xS], bnextBody))
    (h_hm : w.defs.get? how_many_sym = some ([eS, xS], howManyBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env how_many_bnextFormula = some v ∧ v ≠ SExpr.nil)
    (ev : SExpr) (xs : List SExpr) :
    (bnextL xs).count ev = xs.count ev := by
  let e : Env := (({} : Env).insert xS (enc xs)).insert eS ev
  have he : ∃ N, ∀ f ≥ N, evalOpt f w e eT = some ev :=
    re_val_var_get w e { name := "E" } ev (by
      show e.get? eS = some ev
      rw [show e = (({} : Env).insert xS (enc xs)).insert eS ev from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = (({} : Env).insert xS (enc xs)).insert eS ev from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hbn : ConvTo w e (app1 "BNEXT" xT) (bnextExec (enc xs)) :=
    bnext_exec_corr w h_bnext h_no_consp h_no_car h_no_cdr h_no_cons
      h_no_lexorder e xT (enc xs) hx
  rw [bnextExec_enc] at hbn
  have hL := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e eT (app1 "BNEXT" xT) ev (enc (bnextL xs)) he hbn
  rw [howManyExec_enc] at hL
  have hR := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e eT xT ev (enc xs) he hx
  rw [howManyExec_enc] at hR
  have hnat := native_of_replayed_equal w e intRep _ _
    ((bnextL xs).count ev) (xs.count ev) h_no_equal hL hR (hreplayed e)
  omega

end ACL2.Worlds.Sorting
