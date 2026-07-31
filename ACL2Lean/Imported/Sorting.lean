import ACL2Lean.Imported.Perm

/-! # Imported: the sorting books — world-parametric support beyond perm

World-parametric (invariant L3) support for the SORTING MIRROR PROGRAM
(the sorting-completion-2 amended criteria): the LEXORDER Bool kit, the
ORDEREDP simulation (an instance of the `corr_chain2_enc` schematic —
ORDEREDP is EXACTLY `chain2Body "LEXORDER" "ORDEREDP"` in every sorting
book), and the assembly lemmas for the ordered-perms book's native
entries. The `memb`/`rm`/`perm` simulations are REUSED from
`Imported/Perm.lean` — the sorting books carry those defuns verbatim
(same formals, same bodies; the `by decide` world facts at each
log-derived world enforce this at build time). -/

open ACL2 ACL2.Replay ACL2.Lifting ACL2.Worlds.Perm

namespace ACL2.Worlds.Sorting

/-! ## The LEXORDER Bool kit

`lexorder` (the trusted-core primitive, Lexorder.lean) is two-valued;
`lexorderB` is its Bool reading, and the bridge lets the chain2
schematic consume LEXORDER as its comparison. -/

theorem lexorder_t_or_nil (x y : SExpr) :
    lexorder x y = SExpr.t ∨ lexorder x y = SExpr.nil := by
  fun_induction lexorder x y <;> first | assumption | simp

/-- The Bool reading of the two-valued `lexorder`. -/
def lexorderB (x y : SExpr) : Bool := lexorder x y == SExpr.t

theorem lexorder_eq_boolEnc (x y : SExpr) :
    lexorder x y = boolEnc (lexorderB x y) := by
  unfold lexorderB
  rcases lexorder_t_or_nil x y with h | h <;> rw [h] <;> decide

/-- LEXORDER as a `corr_chain2_enc`-shaped comparison: the builtin call
    computes `boolEnc (lexorderB a b)`. -/
theorem callBuiltin_lexorder_boolEnc (a b : SExpr) :
    callBuiltin "LEXORDER" [a, b] = some (boolEnc (lexorderB a b)) := by
  show some (lexorder a b) = some (boolEnc (lexorderB a b))
  rw [lexorder_eq_boolEnc]

/-! ## ORDEREDP: the chain2 instance -/

/-- `(orderedp x)`. -/
abbrev orderedpT (x : SExpr) : SExpr := app1 "ORDEREDP" x

/-- The native reading of ORDEREDP: every adjacent pair is
    lexorder-related. -/
abbrev orderedpRec (xs : List SExpr) : Bool := chain2Rec lexorderB xs

/-- `orderedp` over an encoded argument computes `orderedpRec` — the
    chain2 schematic at `cmp = LEXORDER`. The h_fn body IS the sorting
    books' ORDEREDP verbatim (`chain2Body "LEXORDER" "ORDEREDP"`). -/
theorem corr_orderedp_enc (w : World)
    (h_fn : w.defs.get? { package := "ACL2", name := "ORDEREDP" }
      = some ([{ package := "ACL2", name := "X" }],
              chain2Body "LEXORDER" "ORDEREDP"))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none) :
    ∀ (xs : List SExpr) (e' : Env) (a : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' a = some (enc xs)) →
    ∃ N, ∀ f ≥ N, evalOpt f w e' (orderedpT a)
      = some (boolEnc (orderedpRec xs)) :=
  corr_chain2_enc w "LEXORDER" "ORDEREDP" lexorderB (by decide) (by decide)
    h_fn h_no_consp h_no_cdr h_no_car h_no_lexorder
    callBuiltin_lexorder_boolEnc

/-! ## The ordered-perms assemblies -/

private def aS : Symbol := { package := "ACL2", name := "A" }
private def eS : Symbol := { package := "ACL2", name := "E" }
private def aT : SExpr := .atom (.symbol { name := "A" })
private def eT : SExpr := .atom (.symbol { name := "E" })

/-- The ORDEREDP-RM replayed-statement formula — the root Goal clause,
    exactly as the log emits it:
    `(IMPLIES (ORDEREDP A) (ORDEREDP (RM E A)))`. -/
def orderedp_rmFormula : SExpr :=
  impliesT (orderedpT aT) (orderedpT (rmT eT aT))

/-- ORDEREDP-RM, natively: erasing an element preserves adjacent-pair
    lexorder-sortedness. -/
theorem orderedp_rm_native_of_replayed (w : World)
    (h_orderedp : w.defs.get? { package := "ACL2", name := "ORDEREDP" }
      = some ([{ package := "ACL2", name := "X" }],
              chain2Body "LEXORDER" "ORDEREDP"))
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
      evalOpt f w env orderedp_rmFormula = some v ∧ v ≠ SExpr.nil)
    (ev : SExpr) (xs : List SExpr)
    (h : orderedpRec xs = true) :
    orderedpRec (xs.erase ev) = true := by
  let e : Env := (({} : Env).insert aS (enc xs)).insert eS ev
  have he : ∃ N, ∀ f ≥ N, evalOpt f w e eT = some ev :=
    re_val_var_get w e { name := "E" } ev (by
      show e.get? eS = some ev
      rw [show e = (({} : Env).insert aS (enc xs)).insert eS ev from rfl,
          Env.get?_insert, if_pos (by decide)])
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some (enc xs) :=
    re_val_var_get w e { name := "A" } (enc xs) (by
      show e.get? aS = some (enc xs)
      rw [show e = (({} : Env).insert aS (enc xs)).insert eS ev from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hP := corr_orderedp_enc w h_orderedp h_no_consp h_no_cdr h_no_car
    h_no_lexorder xs e aT ha
  have hrm := corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr
    h_no_cons xs e eT aT ev he ha
  have hC := corr_orderedp_enc w h_orderedp h_no_consp h_no_cdr h_no_car
    h_no_lexorder (xs.erase ev) e (rmT eT aT) hrm
  have hImp := conv_builtin2 w e { name := "IMPLIES" } _ _ _ _ _ (by decide)
    h_no_implies hP hC (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (replayed_pins_ne_nil (hreplayed e) hImp)
  have hp : Logic.toBool (boolEnc (orderedpRec xs)) = true := by
    rw [h]; rfl
  exact bool_true_of_cond_truthy (truthy_of_implies_t hIt hp)

/-! ## CAR-RM -/

private abbrev ifT (c t e : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil)))
private def qNil : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.nil .nil)

/-- `car` of an encoded list is `headD nil` — the native reading of CAR on
    the list fragment. -/
theorem car_enc (l : List SExpr) : Logic.car (enc l) = l.headD SExpr.nil := by
  cases l <;> rfl

/-- Value-level if-false composition (the `re_if_false` + else-value glue
    used throughout the mirrors). -/
private theorem conv_if_false' (w : World) (e : Env) (c t el ev : SExpr)
    (hc : ∃ N, ∀ f ≥ N, evalOpt f w e c = some SExpr.nil)
    (he : ∃ N, ∀ f ≥ N, evalOpt f w e el = some ev) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (ifT c t el) = some ev := by
  obtain ⟨Ni, hi⟩ := re_if_false w e c t el ev hc he
  obtain ⟨Ne, he'⟩ := he
  exact ⟨max Ni Ne, fun f hf => (hi f (by omega)).trans (he' f (by omega))⟩

/-- The CAR-RM replayed-statement formula — the root Goal clause, exactly
    as the log emits it (the AND already if-expanded by clausification):
    `(EQUAL (CAR (RM E A))
            (IF (CONSP A) (IF (EQUAL E (CAR A)) (CAR (CDR A)) (CAR A))
                'NIL))`. -/
def car_rmFormula : SExpr :=
  equalT (carT (rmT eT aT))
    (ifT (conspT aT)
      (ifT (equalT eT (carT aT)) (carT (cdrT aT)) (carT aT))
      qNil)

/-- CAR-RM's native right-hand side: the head of the erased list, by
    cases on whether the erased element was the head. -/
def carRmSpec (ev : SExpr) (xs : List SExpr) : SExpr :=
  match xs with
  | [] => SExpr.nil
  | a :: t => bif ev == a then t.headD SExpr.nil else a

/-- CAR-RM, natively: the head of `xs.erase ev` — nil on the empty list,
    else the tail's head if the head was erased, else the head. -/
theorem car_rm_native_of_replayed (w : World)
    (h_rm : w.defs.get? { package := "ACL2", name := "RM" }
      = some ([{ package := "ACL2", name := "E" },
               { package := "ACL2", name := "X" }], rmBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env car_rmFormula = some v ∧ v ≠ SExpr.nil)
    (ev : SExpr) (xs : List SExpr) :
    (xs.erase ev).headD SExpr.nil = carRmSpec ev xs := by
  let e : Env := (({} : Env).insert aS (enc xs)).insert eS ev
  have he : ∃ N, ∀ f ≥ N, evalOpt f w e eT = some ev :=
    re_val_var_get w e { name := "E" } ev (by
      show e.get? eS = some ev
      rw [show e = (({} : Env).insert aS (enc xs)).insert eS ev from rfl,
          Env.get?_insert, if_pos (by decide)])
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some (enc xs) :=
    re_val_var_get w e { name := "A" } (enc xs) (by
      show e.get? aS = some (enc xs)
      rw [show e = (({} : Env).insert aS (enc xs)).insert eS ev from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  -- LHS: (car (rm e a)) computes the erased list's car
  have hrm := corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr
    h_no_cons xs e eT aT ev he ha
  have hL : ∃ N, ∀ f ≥ N, evalOpt f w e (carT (rmT eT aT))
      = some (Logic.car (enc (xs.erase ev))) :=
    conv_builtin1 w e { name := "CAR" } _ _ _ (by decide) h_no_car hrm
      (callBuiltin_car _)
  -- RHS: the if-tree, by cases on xs
  have hconsp : ∃ N, ∀ f ≥ N, evalOpt f w e (conspT aT)
      = some (Logic.consp (enc xs)) :=
    conv_builtin1 w e { name := "CONSP" } _ _ _ (by decide) h_no_consp ha
      (callBuiltin_consp _)
  have hR : ∃ N, ∀ f ≥ N, evalOpt f w e
      (ifT (conspT aT)
        (ifT (equalT eT (carT aT)) (carT (cdrT aT)) (carT aT)) qNil)
      = some (carRmSpec ev xs) := by
    match xs with
    | [] =>
      exact conv_if_false' w e _ _ _ _ hconsp (re_val_quote w e SExpr.nil)
    | a :: t =>
      have hcarA : ∃ N, ∀ f ≥ N, evalOpt f w e (carT aT) = some a := by
        have h0 := conv_builtin1 w e { name := "CAR" } aT _ _ (by decide)
          h_no_car ha (callBuiltin_car _)
        simpa [enc, Logic.car] using h0
      have hcdrA : ∃ N, ∀ f ≥ N, evalOpt f w e (cdrT aT) = some (enc t) := by
        have h0 := conv_builtin1 w e { name := "CDR" } aT _ _ (by decide)
          h_no_cdr ha (callBuiltin_cdr _)
        simpa [enc, Logic.cdr] using h0
      have heq : ∃ N, ∀ f ≥ N, evalOpt f w e (equalT eT (carT aT))
          = some (Logic.equal ev a) :=
        conv_equalT w e eT (carT aT) ev a h_no_equal he hcarA
      have hinner : ∃ N, ∀ f ≥ N, evalOpt f w e
          (ifT (equalT eT (carT aT)) (carT (cdrT aT)) (carT aT))
          = some (carRmSpec ev (a :: t)) := by
        cases hcase : ev == a with
        | true =>
          have hcarcdr : ∃ N, ∀ f ≥ N, evalOpt f w e (carT (cdrT aT))
              = some (Logic.car (enc t)) :=
            conv_builtin1 w e { name := "CAR" } _ _ _ (by decide) h_no_car
              hcdrA (callBuiltin_car _)
          have := conv_if_true w e (equalT eT (carT aT)) (carT (cdrT aT))
            (carT aT) (Logic.equal ev a) (Logic.car (enc t)) heq
            (by simp [Logic.equal, hcase, SExpr.t]) hcarcdr
          rw [car_enc] at this
          simpa only [carRmSpec, hcase, cond_true] using this
        | false =>
          have heqn : ∃ N, ∀ f ≥ N, evalOpt f w e (equalT eT (carT aT))
              = some SExpr.nil := by
            simpa [Logic.equal, hcase] using heq
          have := conv_if_false' w e (equalT eT (carT aT)) (carT (cdrT aT))
            (carT aT) a heqn hcarA
          simpa only [carRmSpec, hcase, cond_false] using this
      have := conv_if_true w e (conspT aT) _ qNil (Logic.consp (enc (a :: t)))
        (carRmSpec ev (a :: t)) hconsp (by simp [enc, Logic.consp]) hinner
      exact this
  -- the equational ender, then read both values natively
  have hnat := native_of_replayed_equal w e idRep (carT (rmT eT aT)) _
    (Logic.car (enc (xs.erase ev))) (carRmSpec ev xs) h_no_equal hL hR
    (hreplayed e)
  rw [← car_enc]
  exact hnat

/-! ## The isort book: `insert` / `isort` exec kit

The two-stage lift (docs/plans/2026-07-06_two-stage-lift.md) for the
isort book's defuns, plus the `tp:INSERT` discharger (`(CONSP (INSERT E
X))` — every branch of the body is a `cons`). -/

private def xS : Symbol := { package := "ACL2", name := "X" }
private def xT : SExpr := .atom (.symbol { name := "X" })

abbrev insertT (e x : SExpr) : SExpr := app2 "INSERT" e x
abbrev isortT (x : SExpr) : SExpr := app1 "ISORT" x
private abbrev lexT (a b : SExpr) : SExpr := app2 "LEXORDER" a b

/-- `(defun insert (e x) …)`, macroexpanded — exactly as the sorting
    books' logs carry it. -/
def insertBody : SExpr :=
  ifT (conspT xT)
    (ifT (lexT eT (carT xT))
      (consT eT xT)
      (consT (carT xT) (insertT eT (cdrT xT))))
    (consT eT xT)

/-- `(defun isort (x) …)`, macroexpanded. -/
def isortBody : SExpr :=
  ifT (conspT xT) (insertT (carT xT) (isortT (cdrT xT))) qNil

private def insert_sym : Symbol := { package := "ACL2", name := "INSERT" }
private def isort_sym : Symbol := { package := "ACL2", name := "ISORT" }

private theorem insert_ns :
    (insert_sym.isNamed "QUOTE" = false ∧ insert_sym.isNamed "IF" = false ∧
     insert_sym.isNamed "LET" = false ∧ insert_sym.isNamed "LET*" = false) := by
  decide
private theorem isort_ns :
    (isort_sym.isNamed "QUOTE" = false ∧ isort_sym.isNamed "IF" = false ∧
     isort_sym.isNamed "LET" = false ∧ isort_sym.isNamed "LET*" = false) := by
  decide

private theorem callBuiltin_lexorder (a b : SExpr) :
    callBuiltin "LEXORDER" [a, b] = some (lexorder a b) := rfl

private theorem bindArgs_ex_e (ve vx : SExpr) :
    (bindArgs [eS, xS] [ve, vx]).get? eS = some ve := by
  show ((({} : Env).insert xS vx).insert eS ve).get? eS = some ve
  rw [Env.get?_insert, if_pos (by decide)]

private theorem bindArgs_ex_x (ve vx : SExpr) :
    (bindArgs [eS, xS] [ve, vx]).get? xS = some vx := by
  show ((({} : Env).insert xS vx).insert eS ve).get? xS = some vx
  rw [Env.get?_insert, if_neg (by decide), Env.get?_insert,
      if_pos (by decide)]

/-- `insert`'s body as a total Lean function (shape-exact, D2). -/
def insertExec (e x : SExpr) : SExpr :=
  if Logic.toBool (Logic.consp x) = true then
    if Logic.toBool (lexorder e (Logic.car x)) = true then Logic.cons e x
    else Logic.cons (Logic.car x) (insertExec e (Logic.cdr x))
  else Logic.cons e x
termination_by x.consCount
decreasing_by exact consCount_cdr_lt_of_consp (by assumption)

/-- Stage 1: an `insert` call converges to `insertExec` of its argument
    values. -/
theorem insert_exec_corr (w : World)
    (h_insert : w.defs.get? insert_sym = some ([eS, xS], insertBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none) :
    ∀ (env : Env) (a x av xv : SExpr),
      ConvTo w env a av → ConvTo w env x xv →
      ConvTo w env (insertT a x) (insertExec av xv) := by
  have hbody : ∀ xv av : SExpr,
      ConvTo w (bindArgs [eS, xS] [av, xv]) insertBody (insertExec av xv) := by
    refine consCount_strong_induction
      (fun xv => ∀ av, ConvTo w (bindArgs [eS, xS] [av, xv]) insertBody
        (insertExec av xv)) ?_
    intro xv ih av
    have hav := re_val_var_get w (bindArgs [eS, xS] [av, xv])
      { name := "E" } av (bindArgs_ex_e av xv)
    have hxv := re_val_var_get w (bindArgs [eS, xS] [av, xv])
      { name := "X" } xv (bindArgs_ex_x av xv)
    have hconsp := conv_builtin1 w _ { name := "CONSP" } xT xv
      (Logic.consp xv) (by decide) h_no_consp hxv (callBuiltin_consp _)
    have hcar := conv_builtin1 w _ { name := "CAR" } xT xv
      (Logic.car xv) (by decide) h_no_car hxv (callBuiltin_car _)
    have hcdr := conv_builtin1 w _ { name := "CDR" } xT xv
      (Logic.cdr xv) (by decide) h_no_cdr hxv (callBuiltin_cdr _)
    have hlex := conv_builtin2 w _ { name := "LEXORDER" } eT (carT xT) av
      (Logic.car xv) (lexorder av (Logic.car xv)) (by decide) h_no_lexorder
      hav hcar (callBuiltin_lexorder _ _)
    have hconsEX : ConvTo w (bindArgs [eS, xS] [av, xv]) (consT eT xT)
        (Logic.cons av xv) :=
      conv_builtin2 w _ { name := "CONS" } eT xT av xv
        (Logic.cons av xv) (by decide) h_no_cons hav hxv rfl
    have houter := conv_if_lift w (bindArgs [eS, xS] [av, xv]) (conspT xT)
      (ifT (lexT eT (carT xT)) (consT eT xT)
        (consT (carT xT) (insertT eT (cdrT xT))))
      (consT eT xT) (Logic.consp xv)
      (if Logic.toBool (lexorder av (Logic.car xv)) = true then
        Logic.cons av xv
       else Logic.cons (Logic.car xv) (insertExec av (Logic.cdr xv)))
      (Logic.cons av xv) hconsp
      (fun hb =>
        conv_if_lift w _ (lexT eT (carT xT)) (consT eT xT)
          (consT (carT xT) (insertT eT (cdrT xT)))
          (lexorder av (Logic.car xv)) (Logic.cons av xv)
          (Logic.cons (Logic.car xv) (insertExec av (Logic.cdr xv))) hlex
          (fun _ => hconsEX)
          (fun _ =>
            conv_builtin2 w _ { name := "CONS" } (carT xT)
              (insertT eT (cdrT xT)) (Logic.car xv)
              (insertExec av (Logic.cdr xv))
              (Logic.cons (Logic.car xv) (insertExec av (Logic.cdr xv)))
              (by decide) h_no_cons hcar
              (conv_defn_2 w _ insert_sym eT (cdrT xT) av (Logic.cdr xv)
                eS xS insertBody _ insert_ns h_insert hav hcdr
                (ih (Logic.cdr xv) (consCount_cdr_lt_of_consp hb) av))
              rfl))
      (fun _ => hconsEX)
    rw [insertExec.eq_def]
    exact houter
  intro env a x av xv ha hx
  exact conv_defn_2 w env insert_sym a x av xv eS xS insertBody _
    insert_ns h_insert ha hx (hbody xv av)

/-- `insert`'s native reading: ordered insertion by `lexorderB`. -/
def insertL (e : SExpr) : List SExpr → List SExpr
  | [] => [e]
  | a :: t => bif lexorderB e a then e :: a :: t else a :: insertL e t

private theorem toBool_lexorder (e a : SExpr) :
    Logic.toBool (lexorder e a) = lexorderB e a := by
  rw [lexorder_eq_boolEnc]; cases lexorderB e a <;> rfl

/-- Stage 2: `insertExec` on an encoded list computes `insertL`. -/
theorem insertExec_enc (e : SExpr) (xs : List SExpr) :
    insertExec e (enc xs) = enc (insertL e xs) := by
  induction xs with
  | nil => rw [insertExec.eq_def]; rfl
  | cons hd tl ih =>
    rw [insertExec.eq_def, show enc (hd :: tl) = .cons hd (enc tl) from rfl,
        if_pos (show Logic.toBool (Logic.consp (.cons hd (enc tl))) = true
          from rfl),
        show Logic.car (SExpr.cons hd (enc tl)) = hd from rfl,
        show Logic.cdr (SExpr.cons hd (enc tl)) = enc tl from rfl,
        toBool_lexorder]
    cases hb : lexorderB e hd with
    | true => simp [hb, insertL, enc]
    | false =>
      simp only [hb, Bool.false_eq_true, if_false, insertL, cond_false]
      rw [ih]
      rfl

/-- `isort`'s body as a total Lean function. -/
def isortExec (x : SExpr) : SExpr :=
  if Logic.toBool (Logic.consp x) = true then
    insertExec (Logic.car x) (isortExec (Logic.cdr x))
  else SExpr.nil
termination_by x.consCount
decreasing_by exact consCount_cdr_lt_of_consp (by assumption)

/-- Stage 1: an `isort` call converges to `isortExec` of its argument
    value. -/
theorem isort_exec_corr (w : World)
    (h_insert : w.defs.get? insert_sym = some ([eS, xS], insertBody))
    (h_isort : w.defs.get? isort_sym = some ([xS], isortBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none) :
    ∀ (env : Env) (x xv : SExpr),
      ConvTo w env x xv → ConvTo w env (isortT x) (isortExec xv) := by
  have hbody : ∀ xv : SExpr,
      ConvTo w (bindArgs [xS] [xv]) isortBody (isortExec xv) := by
    refine consCount_strong_induction
      (fun xv => ConvTo w (bindArgs [xS] [xv]) isortBody (isortExec xv)) ?_
    intro xv ih
    have hxv := re_val_var_get w (bindArgs [xS] [xv])
      { name := "X" } xv (bindArgs_single_get_self xS xv)
    have hconsp := conv_builtin1 w _ { name := "CONSP" } xT xv
      (Logic.consp xv) (by decide) h_no_consp hxv (callBuiltin_consp _)
    have hcar := conv_builtin1 w _ { name := "CAR" } xT xv
      (Logic.car xv) (by decide) h_no_car hxv (callBuiltin_car _)
    have hcdr := conv_builtin1 w _ { name := "CDR" } xT xv
      (Logic.cdr xv) (by decide) h_no_cdr hxv (callBuiltin_cdr _)
    have houter := conv_if_lift w (bindArgs [xS] [xv]) (conspT xT)
      (insertT (carT xT) (isortT (cdrT xT))) qNil (Logic.consp xv)
      (insertExec (Logic.car xv) (isortExec (Logic.cdr xv))) SExpr.nil
      hconsp
      (fun hb =>
        insert_exec_corr w h_insert h_no_consp h_no_car h_no_cdr h_no_cons
          h_no_lexorder _ (carT xT) (isortT (cdrT xT)) (Logic.car xv)
          (isortExec (Logic.cdr xv)) hcar
          (conv_defn_1 w _ isort_sym (cdrT xT) (Logic.cdr xv) xS isortBody _
            isort_ns h_isort hcdr
            (ih (Logic.cdr xv) (consCount_cdr_lt_of_consp hb))))
      (fun _ => re_val_quote w _ SExpr.nil)
    rw [isortExec.eq_def]
    exact houter
  intro env x xv hx
  exact conv_defn_1 w env isort_sym x xv xS isortBody _
    isort_ns h_isort hx (hbody xv)

/-- `isort`'s native reading: insertion sort by `lexorderB`. -/
def isortL : List SExpr → List SExpr
  | [] => []
  | a :: t => insertL a (isortL t)

/-- Stage 2: `isortExec` on an encoded list computes `isortL`. -/
theorem isortExec_enc (xs : List SExpr) :
    isortExec (enc xs) = enc (isortL xs) := by
  induction xs with
  | nil => rw [isortExec.eq_def]; rfl
  | cons hd tl ih =>
    rw [isortExec.eq_def, show enc (hd :: tl) = .cons hd (enc tl) from rfl]
    simp [Logic.consp, Logic.car, Logic.cdr, ih, insertExec_enc, isortL]

/-- `isort` over an encoded argument computes `isortL` under `enc`. -/
theorem corr_isort_enc (w : World)
    (h_insert : w.defs.get? insert_sym = some ([eS, xS], insertBody))
    (h_isort : w.defs.get? isort_sym = some ([xS], isortBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none) :
    ∀ (xs : List SExpr) (e' : Env) (x : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w e' x = some (enc xs)) →
    ∃ N, ∀ f ≥ N, evalOpt f w e' (isortT x) = some (enc (isortL xs)) := by
  intro xs e' x hx
  have h := isort_exec_corr w h_insert h_isort h_no_consp h_no_car h_no_cdr
    h_no_cons h_no_lexorder e' x (enc xs) hx
  rwa [isortExec_enc] at h

/-! ## The `tp:INSERT` discharger — `(CONSP (INSERT E X))` -/

/-- Every branch of `insertExec` is a `cons`. -/
theorem insertExec_consp (e x : SExpr) :
    Logic.consp (insertExec e x) = SExpr.t := by
  rw [insertExec.eq_def]
  split
  · split <;> rfl
  · rfl

/-- `tp:INSERT`, world-parametric — the driver-shape TP hypothesis:
    any value `(insert a0 a1)` converges to satisfies insert's emitted
    `consp` TP corollary. -/
theorem dis_insert_tp (w : World)
    (h_insert : w.defs.get? insert_sym = some ([eS, xS], insertBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (e' : Env) (a0 a1 v : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e' (insertT a0 a1) = some v) :
    Logic.consp v = SExpr.t := by
  obtain ⟨⟨N0, u0, h0⟩, ⟨N1, u1, h1⟩⟩ :=
    conv_args2_of_conv_app w e' { name := "INSERT" } a0 a1 v (by decide) h
  have happ := insert_exec_corr w h_insert h_no_consp h_no_car h_no_cdr
    h_no_cons h_no_lexorder e' a0 a1 u0 u1 ⟨N0, h0⟩ ⟨N1, h1⟩
  rw [val_unique h happ]
  exact insertExec_consp u0 u1

/-! ## The ORDEREDP-ISORT assembly -/

/-- The ORDEREDP-ISORT replayed-statement formula: `(ORDEREDP (ISORT X))`. -/
def orderedp_isortFormula : SExpr := orderedpT (isortT xT)

/-- ORDEREDP-ISORT, natively: INSERTION SORT ALWAYS SORTS — the output of
    `isortL` is adjacent-pair lexorder-sorted, for every input list. -/
theorem orderedp_isort_native_of_replayed (w : World)
    (h_insert : w.defs.get? insert_sym = some ([eS, xS], insertBody))
    (h_isort : w.defs.get? isort_sym = some ([xS], isortBody))
    (h_orderedp : w.defs.get? { package := "ACL2", name := "ORDEREDP" }
      = some ([{ package := "ACL2", name := "X" }],
              chain2Body "LEXORDER" "ORDEREDP"))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env orderedp_isortFormula = some v ∧ v ≠ SExpr.nil)
    (xs : List SExpr) :
    orderedpRec (isortL xs) = true := by
  let e : Env := ({} : Env).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ({} : Env).insert xS (enc xs) from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hisort := corr_isort_enc w h_insert h_isort h_no_consp h_no_car
    h_no_cdr h_no_cons h_no_lexorder xs e xT hx
  have hord := corr_orderedp_enc w h_orderedp h_no_consp h_no_cdr h_no_car
    h_no_lexorder (isortL xs) e (isortT xT) hisort
  exact bool_true_of_cond_truthy (toBool_true_of_ne_nil
    (replayed_pins_ne_nil (hreplayed e) hord))

end ACL2.Worlds.Sorting
