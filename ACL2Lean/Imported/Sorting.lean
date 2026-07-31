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

/-- The chain2 fold IS Mathlib's `List.IsChain` — the fully idiomatic
    reading of the ORDEREDP-shaped recognizers. -/
theorem chain2Rec_iff_isChain (p : SExpr → SExpr → Bool) :
    ∀ xs : List SExpr,
      chain2Rec p xs = true ↔ xs.IsChain (fun a b => p a b = true)
  | [] => by simp [chain2Rec]
  | [_] => by simp [chain2Rec]
  | a :: b :: t => by
    rw [show chain2Rec p (a :: b :: t)
          = (p a b && chain2Rec p (b :: t)) from rfl,
        Bool.and_eq_true, chain2Rec_iff_isChain p (b :: t),
        List.isChain_cons_cons]

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

/-! ## Ground-zero rule dischargers

The stored ground-zero rewrite rules (`(:GROUND-ZERO-RULES …)`) cited as
`rule:` conditions by the sorting rows, as world-parametric value-level
facts. Each type matches `mkRuleHypType` of the emitted spec exactly:
`∀ env', EvTrue hyp → … → ∃N ∀f≥N, eval lhs = eval rhs`. -/

private abbrev notT (a : SExpr) : SExpr := app1 "NOT" a

/-- The value of the variable `X` in an arbitrary env (total — unbound
    reads `nil`). -/
private theorem conv_varX (w : World) (env' : Env) :
    ∃ N, ∀ f ≥ N, evalOpt f w env' xT
      = some ((env'.get? xS).getD .nil) :=
  re_val_var w env' { name := "X" } (by decide)

/-- `rule:DEFAULT-CAR` — `((NOT (CONSP X))) ⊢ (CAR X) ≡ 'NIL`. -/
theorem dis_default_car (w : World)
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_not : w.defs.get? ({ name := "NOT" } : Symbol) = none) :
    ∀ env' : Env, EvTrue w env' (notT (conspT xT)) →
    ∃ N, ∀ f ≥ N, evalOpt f w env' (carT xT) = evalOpt f w env' qNil := by
  intro env' hyp
  obtain ⟨vx, hx⟩ : ∃ vx, ∃ N, ∀ f ≥ N, evalOpt f w env' xT = some vx :=
    ⟨_, conv_varX w env'⟩
  have hconsp := conv_builtin1 w env' { name := "CONSP" } xT vx
    (Logic.consp vx) (by decide) h_no_consp hx (callBuiltin_consp _)
  have hnot := conv_builtin1 w env' { name := "NOT" } (conspT xT)
    (Logic.consp vx) (Logic.not (Logic.consp vx)) (by decide) h_no_not
    hconsp (callBuiltin_not _)
  have hne := ne_nil_of_evtrue_conv hyp hnot
  have hcar0 : Logic.car vx = SExpr.nil := by
    cases vx <;> simp_all [Logic.consp, Logic.not, Logic.car, Logic.toBool]
  have hL := conv_builtin1 w env' { name := "CAR" } xT vx
    (Logic.car vx) (by decide) h_no_car hx (callBuiltin_car _)
  rw [hcar0] at hL
  exact fuel_eq_of_conv hL (re_val_quote w env' SExpr.nil) rfl

/-- `rule:DEFAULT-CDR` — `((NOT (CONSP X))) ⊢ (CDR X) ≡ 'NIL`. -/
theorem dis_default_cdr (w : World)
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_not : w.defs.get? ({ name := "NOT" } : Symbol) = none) :
    ∀ env' : Env, EvTrue w env' (notT (conspT xT)) →
    ∃ N, ∀ f ≥ N, evalOpt f w env' (cdrT xT) = evalOpt f w env' qNil := by
  intro env' hyp
  obtain ⟨vx, hx⟩ : ∃ vx, ∃ N, ∀ f ≥ N, evalOpt f w env' xT = some vx :=
    ⟨_, conv_varX w env'⟩
  have hconsp := conv_builtin1 w env' { name := "CONSP" } xT vx
    (Logic.consp vx) (by decide) h_no_consp hx (callBuiltin_consp _)
  have hnot := conv_builtin1 w env' { name := "NOT" } (conspT xT)
    (Logic.consp vx) (Logic.not (Logic.consp vx)) (by decide) h_no_not
    hconsp (callBuiltin_not _)
  have hne := ne_nil_of_evtrue_conv hyp hnot
  have hcdr0 : Logic.cdr vx = SExpr.nil := by
    cases vx <;> simp_all [Logic.consp, Logic.not, Logic.cdr, Logic.toBool]
  have hL := conv_builtin1 w env' { name := "CDR" } xT vx
    (Logic.cdr vx) (by decide) h_no_cdr hx (callBuiltin_cdr _)
  rw [hcdr0] at hL
  exact fuel_eq_of_conv hL (re_val_quote w env' SExpr.nil) rfl

/-- `'(NIL)` — the CONS-CAR-CDR rule's else-value, `(cons nil nil)`
    quoted. -/
private def qNilList : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" }))
    (.cons (.cons SExpr.nil SExpr.nil) .nil)

/-- `rule:CONS-CAR-CDR` — unconditional, the stored ground-zero form:
    `(CONS (CAR X) (CDR X)) ≡ (IF (CONSP X) X '(NIL))`. -/
theorem dis_cons_car_cdr (w : World)
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none) :
    ∀ env' : Env,
    ∃ N, ∀ f ≥ N, evalOpt f w env' (consT (carT xT) (cdrT xT))
      = evalOpt f w env' (ifT (conspT xT) xT qNilList) := by
  intro env'
  obtain ⟨vx, hx⟩ : ∃ vx, ∃ N, ∀ f ≥ N, evalOpt f w env' xT = some vx :=
    ⟨_, conv_varX w env'⟩
  have hconsp := conv_builtin1 w env' { name := "CONSP" } xT vx
    (Logic.consp vx) (by decide) h_no_consp hx (callBuiltin_consp _)
  have hcar := conv_builtin1 w env' { name := "CAR" } xT vx
    (Logic.car vx) (by decide) h_no_car hx (callBuiltin_car _)
  have hcdr := conv_builtin1 w env' { name := "CDR" } xT vx
    (Logic.cdr vx) (by decide) h_no_cdr hx (callBuiltin_cdr _)
  have hL := conv_builtin2 w env' { name := "CONS" } (carT xT) (cdrT xT)
    (Logic.car vx) (Logic.cdr vx) (Logic.cons (Logic.car vx) (Logic.cdr vx))
    (by decide) h_no_cons hcar hcdr rfl
  match vx with
  | .cons a d =>
    have hR := conv_if_true w env' (conspT xT) xT qNilList
      (Logic.consp (.cons a d)) (.cons a d) hconsp rfl hx
    exact fuel_eq_of_conv hL hR (by simp [Logic.cons, Logic.car, Logic.cdr])
  | .nil =>
    have hR := conv_if_false' w env' (conspT xT) xT qNilList
      (.cons SExpr.nil SExpr.nil) hconsp
      (re_val_quote w env' (.cons SExpr.nil SExpr.nil))
    exact fuel_eq_of_conv hL hR (by simp [Logic.cons, Logic.car, Logic.cdr])
  | .atom a =>
    have hR := conv_if_false' w env' (conspT xT) xT qNilList
      (.cons SExpr.nil SExpr.nil) hconsp
      (re_val_quote w env' (.cons SExpr.nil SExpr.nil))
    exact fuel_eq_of_conv hL hR (by simp [Logic.cons, Logic.car, Logic.cdr])

/-! ## EQUAL-CONS -/

private def bS : Symbol := { package := "ACL2", name := "B" }
private def bT : SExpr := .atom (.symbol { name := "B" })

/-- The EQUAL-CONS replayed-statement formula — the root Goal clause:
    `(EQUAL (EQUAL (CONS A B) X)
            (IF (CONSP X) (IF (EQUAL A (CAR X)) (EQUAL B (CDR X)) 'NIL)
                'NIL))`. -/
def equal_consFormula : SExpr :=
  equalT (equalT (consT aT bT) xT)
    (ifT (conspT xT)
      (ifT (equalT aT (carT xT)) (equalT bT (cdrT xT)) qNil)
      qNil)

/-- EQUAL-CONS's native right-hand side: componentwise equality against a
    cons, false against a non-cons. -/
def equalConsSpec (av bv xv : SExpr) : Bool :=
  match xv with
  | .cons c d => av == c && bv == d
  | _ => false

/-- EQUAL-CONS, natively: equality with a cons decomposes componentwise
    (ACL2's cons-equation decode, as a Bool fact over `==`). -/
theorem equal_cons_native_of_replayed (w : World)
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env equal_consFormula = some v ∧ v ≠ SExpr.nil)
    (av bv xv : SExpr) :
    (SExpr.cons av bv == xv) = equalConsSpec av bv xv := by
  let e : Env := ((({} : Env).insert xS xv).insert bS bv).insert aS av
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some av :=
    re_val_var_get w e { name := "A" } av (by
      show e.get? aS = some av
      rw [show e = ((({} : Env).insert xS xv).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hb : ∃ N, ∀ f ≥ N, evalOpt f w e bT = some bv :=
    re_val_var_get w e { name := "B" } bv (by
      show e.get? bS = some bv
      rw [show e = ((({} : Env).insert xS xv).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some xv :=
    re_val_var_get w e { name := "X" } xv (by
      show e.get? xS = some xv
      rw [show e = ((({} : Env).insert xS xv).insert bS bv).insert aS av
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  -- LHS: (equal (cons a b) x) computes Logic.equal (cons av bv) xv
  have hcons := conv_builtin2 w e { name := "CONS" } aT bT av bv
    (Logic.cons av bv) (by decide) h_no_cons ha hb rfl
  have hL := conv_builtin2 w e { name := "EQUAL" } (consT aT bT) xT
    (Logic.cons av bv) xv (Logic.equal (Logic.cons av bv) xv) (by decide)
    h_no_equal hcons hx (callBuiltin_equal _ _)
  -- RHS: the if-tree, by cases on xv
  have hconsp := conv_builtin1 w e { name := "CONSP" } xT xv
    (Logic.consp xv) (by decide) h_no_consp hx (callBuiltin_consp _)
  have hR : ∃ N, ∀ f ≥ N, evalOpt f w e
      (ifT (conspT xT)
        (ifT (equalT aT (carT xT)) (equalT bT (cdrT xT)) qNil)
        qNil)
      = some (boolEnc (equalConsSpec av bv xv)) := by
    match xv with
    | .cons c d =>
      have hcar : ∃ N, ∀ f ≥ N, evalOpt f w e (carT xT) = some c := by
        have h0 := conv_builtin1 w e { name := "CAR" } xT (.cons c d)
          (Logic.car (.cons c d)) (by decide) h_no_car hx (callBuiltin_car _)
        simpa [Logic.car] using h0
      have hcdr : ∃ N, ∀ f ≥ N, evalOpt f w e (cdrT xT) = some d := by
        have h0 := conv_builtin1 w e { name := "CDR" } xT (.cons c d)
          (Logic.cdr (.cons c d)) (by decide) h_no_cdr hx (callBuiltin_cdr _)
        simpa [Logic.cdr] using h0
      have heqA := conv_builtin2 w e { name := "EQUAL" } aT (carT xT) av c
        (Logic.equal av c) (by decide) h_no_equal ha hcar
        (callBuiltin_equal _ _)
      have heqB := conv_builtin2 w e { name := "EQUAL" } bT (cdrT xT) bv d
        (Logic.equal bv d) (by decide) h_no_equal hb hcdr
        (callBuiltin_equal _ _)
      have hinner : ∃ N, ∀ f ≥ N, evalOpt f w e
          (ifT (equalT aT (carT xT)) (equalT bT (cdrT xT)) qNil)
          = some (boolEnc (equalConsSpec av bv (.cons c d))) := by
        cases hac : av == c with
        | true =>
          have := conv_if_true w e (equalT aT (carT xT))
            (equalT bT (cdrT xT)) qNil (Logic.equal av c) (Logic.equal bv d)
            heqA (by simp [Logic.equal, hac, SExpr.t]) heqB
          have hval : Logic.equal bv d
              = boolEnc (equalConsSpec av bv (.cons c d)) := by
            simp only [equalConsSpec, hac, Bool.true_and, Logic.equal,
              boolEnc]
            cases hbd : bv == d <;> simp
          rwa [hval] at this
        | false =>
          have heqAn : ∃ N, ∀ f ≥ N,
              evalOpt f w e (equalT aT (carT xT)) = some SExpr.nil := by
            simpa [Logic.equal, hac] using heqA
          have := conv_if_false' w e (equalT aT (carT xT))
            (equalT bT (cdrT xT)) qNil SExpr.nil heqAn
            (re_val_quote w e SExpr.nil)
          have hval : SExpr.nil
              = boolEnc (equalConsSpec av bv (.cons c d)) := by
            simp [equalConsSpec, hac, boolEnc]
          rwa [hval] at this
      have := conv_if_true w e (conspT xT) _ qNil
        (Logic.consp (.cons c d))
        (boolEnc (equalConsSpec av bv (.cons c d))) hconsp rfl hinner
      exact this
    | .nil =>
      have := conv_if_false' w e (conspT xT)
        (ifT (equalT aT (carT xT)) (equalT bT (cdrT xT)) qNil) qNil
        SExpr.nil hconsp (re_val_quote w e SExpr.nil)
      simpa [equalConsSpec, boolEnc] using this
    | .atom a =>
      have := conv_if_false' w e (conspT xT)
        (ifT (equalT aT (carT xT)) (equalT bT (cdrT xT)) qNil) qNil
        SExpr.nil hconsp (re_val_quote w e SExpr.nil)
      simpa [equalConsSpec, boolEnc] using this
  -- the equational ender, then read the Logic.equal as ==
  have hnat := native_of_replayed_equal w e idRep _ _
    (Logic.equal (Logic.cons av bv) xv) (boolEnc (equalConsSpec av bv xv))
    h_no_equal hL hR (hreplayed e)
  have hcond : ∀ b : Bool,
      (if b = true then SExpr.t else SExpr.nil) = boolEnc b :=
    fun b => by cases b <;> rfl
  have : Logic.equal (Logic.cons av bv) xv
      = boolEnc (SExpr.cons av bv == xv) := by
    simp only [Logic.cons, Logic.equal]
    exact hcond _
  rw [this] at hnat
  exact bool_of_cond_eq hnat

/-! ## ORDEREDP-MEMB -/

/-- The ORDEREDP-MEMB replayed-statement formula — the root Goal clause
    (the AND if-expanded):
    `(IMPLIES (IF (ORDEREDP A)
                  (IF (NOT (EQUAL E (CAR A))) (LEXORDER E (CAR A)) 'NIL)
                  'NIL)
              (NOT (MEMB E A)))`. -/
def orderedp_membFormula : SExpr :=
  impliesT
    (ifT (orderedpT aT)
      (ifT (notT (equalT eT (carT aT))) (lexT eT (carT aT)) qNil)
      qNil)
    (notT (membT eT aT))

/-- ORDEREDP-MEMB, natively: an element strictly below the head of a
    lexorder-sorted list is not in the list. (Stated at the cons
    instance, where the ACL2 hypotheses have their content.) -/
theorem orderedp_memb_native_of_replayed (w : World)
    (h_orderedp : w.defs.get? { package := "ACL2", name := "ORDEREDP" }
      = some ([{ package := "ACL2", name := "X" }],
              chain2Body "LEXORDER" "ORDEREDP"))
    (h_memb : w.defs.get? { package := "ACL2", name := "MEMB" }
      = some ([{ package := "ACL2", name := "A" },
               { package := "ACL2", name := "X" }], membBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_not : w.defs.get? ({ name := "NOT" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env orderedp_membFormula = some v ∧ v ≠ SExpr.nil)
    (ev a : SExpr) (t : List SExpr)
    (hord : orderedpRec (a :: t) = true)
    (hne : (ev == a) = false)
    (hlex : lexorderB ev a = true) :
    (a :: t).contains ev = false := by
  let e : Env := (({} : Env).insert aS (enc (a :: t))).insert eS ev
  have he : ∃ N, ∀ f ≥ N, evalOpt f w e eT = some ev :=
    re_val_var_get w e { name := "E" } ev (by
      show e.get? eS = some ev
      rw [show e = (({} : Env).insert aS (enc (a :: t))).insert eS ev
            from rfl,
          Env.get?_insert, if_pos (by decide)])
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some (enc (a :: t)) :=
    re_val_var_get w e { name := "A" } (enc (a :: t)) (by
      show e.get? aS = some (enc (a :: t))
      rw [show e = (({} : Env).insert aS (enc (a :: t))).insert eS ev
            from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  -- the antecedent's pieces
  have hOrd := corr_orderedp_enc w h_orderedp h_no_consp h_no_cdr h_no_car
    h_no_lexorder (a :: t) e aT ha
  have hcarA : ∃ N, ∀ f ≥ N, evalOpt f w e (carT aT) = some a := by
    have h0 := conv_builtin1 w e { name := "CAR" } aT (enc (a :: t))
      (Logic.car (enc (a :: t))) (by decide) h_no_car ha (callBuiltin_car _)
    simpa [enc, Logic.car] using h0
  have hEq : ∃ N, ∀ f ≥ N, evalOpt f w e (equalT eT (carT aT))
      = some SExpr.nil := by
    have h0 := conv_builtin2 w e { name := "EQUAL" } eT (carT aT) ev a
      (Logic.equal ev a) (by decide) h_no_equal he hcarA
      (callBuiltin_equal _ _)
    simpa [Logic.equal, hne] using h0
  have hNot : ∃ N, ∀ f ≥ N,
      evalOpt f w e (notT (equalT eT (carT aT))) = some SExpr.t := by
    have h0 := conv_builtin1 w e { name := "NOT" } (equalT eT (carT aT))
      SExpr.nil (Logic.not SExpr.nil) (by decide) h_no_not hEq
      (callBuiltin_not _)
    simpa [Logic.not] using h0
  have hLex : ∃ N, ∀ f ≥ N, evalOpt f w e (lexT eT (carT aT))
      = some SExpr.t := by
    have h0 := conv_builtin2 w e { name := "LEXORDER" } eT (carT aT) ev a
      (lexorder ev a) (by decide) h_no_lexorder he hcarA
      (callBuiltin_lexorder _ _)
    rw [lexorder_eq_boolEnc, hlex] at h0
    exact h0
  have hInner : ∃ N, ∀ f ≥ N, evalOpt f w e
      (ifT (notT (equalT eT (carT aT))) (lexT eT (carT aT)) qNil)
      = some SExpr.t :=
    conv_if_true w e _ _ qNil SExpr.t SExpr.t hNot rfl hLex
  have hAnte : ∃ N, ∀ f ≥ N, evalOpt f w e
      (ifT (orderedpT aT)
        (ifT (notT (equalT eT (carT aT))) (lexT eT (carT aT)) qNil)
        qNil)
      = some SExpr.t := by
    refine conv_if_true w e _ _ qNil (boolEnc (orderedpRec (a :: t)))
      SExpr.t hOrd ?_ hInner
    rw [hord]; rfl
  -- the consequent
  have hMemb := corr_memb_enc w h_memb h_no_consp h_no_equal h_no_car
    h_no_cdr (a :: t) e eT aT ev he ha
  have hC := conv_builtin1 w e { name := "NOT" } (membT eT aT)
    (bif (a :: t).contains ev then SExpr.t else SExpr.nil)
    (Logic.not (bif (a :: t).contains ev then SExpr.t else SExpr.nil))
    (by decide) h_no_not hMemb (callBuiltin_not _)
  -- pin + project
  have hImp := conv_builtin2 w e { name := "IMPLIES" } _ _ _ _ _ (by decide)
    h_no_implies hAnte hC (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (replayed_pins_ne_nil (hreplayed e) hImp)
  have hconc := truthy_of_implies_t hIt rfl
  cases hcont : (a :: t).contains ev with
  | true => rw [hcont] at hconc; exact absurd hconc (by decide)
  | false => rfl

/-! ## Arithmetic rule dischargers

The arithmetic-3 commutativity/associativity family and the two
if-lifting rules the HOW-MANY rows cite — all unconditional value-level
facts over `Logic.plus` (the SYNP `syntaxp` hypotheses of
FOLD-CONSTS-IN-+ are premises we never need). Variables per the stored
specs: X/Y/Z, and A/B/C in the if-lifting rules. -/

private def yS : Symbol := { package := "ACL2", name := "Y" }
private def yT : SExpr := .atom (.symbol { name := "Y" })
private def zS : Symbol := { package := "ACL2", name := "Z" }
private def zT : SExpr := .atom (.symbol { name := "Z" })
private def cS : Symbol := { package := "ACL2", name := "C" }
private def cT : SExpr := .atom (.symbol { name := "C" })

/-- Any variable converges in any env (unbound reads nil; none of the
    rule variables is `T`). -/
private theorem conv_var (w : World) (env' : Env) (s : Symbol)
    (h : s.isNamed "T" = false) :
    ∃ v, ∃ N, ∀ f ≥ N, evalOpt f w env' (.atom (.symbol s)) = some v :=
  ⟨_, re_val_var w env' s h⟩

private theorem conv_plusT (w : World) (env' : Env) (a b av bv : SExpr)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (ha : ∃ N, ∀ f ≥ N, evalOpt f w env' a = some av)
    (hb : ∃ N, ∀ f ≥ N, evalOpt f w env' b = some bv) :
    ∃ N, ∀ f ≥ N, evalOpt f w env' (plusT a b)
      = some (Logic.plus av bv) :=
  conv_builtin2 w env' { name := "BINARY-+" } a b av bv _ (by decide)
    h_no_plus ha hb (callBuiltin_plus _ _)

/-- `rule:(+ y x) ≡ (+ x y)` (commutativity-of-+). -/
theorem dis_plus_comm (w : World)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none) :
    ∀ env' : Env, ∃ N, ∀ f ≥ N,
      evalOpt f w env' (plusT yT xT) = evalOpt f w env' (plusT xT yT) := by
  intro env'
  obtain ⟨vx, hx⟩ := conv_var w env' xS (by decide)
  obtain ⟨vy, hy⟩ := conv_var w env' yS (by decide)
  exact fuel_eq_of_conv (conv_plusT w env' yT xT vy vx h_no_plus hy hx)
    (conv_plusT w env' xT yT vx vy h_no_plus hx hy) (logic_plus_comm vy vx)

/-- `rule:(+ y (+ x z)) ≡ (+ x (+ y z))` (commutativity-2-of-+). -/
theorem dis_plus_comm2 (w : World)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none) :
    ∀ env' : Env, ∃ N, ∀ f ≥ N,
      evalOpt f w env' (plusT yT (plusT xT zT))
        = evalOpt f w env' (plusT xT (plusT yT zT)) := by
  intro env'
  obtain ⟨vx, hx⟩ := conv_var w env' xS (by decide)
  obtain ⟨vy, hy⟩ := conv_var w env' yS (by decide)
  obtain ⟨vz, hz⟩ := conv_var w env' zS (by decide)
  exact fuel_eq_of_conv
    (conv_plusT w env' yT (plusT xT zT) vy (Logic.plus vx vz) h_no_plus hy
      (conv_plusT w env' xT zT vx vz h_no_plus hx hz))
    (conv_plusT w env' xT (plusT yT zT) vx (Logic.plus vy vz) h_no_plus hx
      (conv_plusT w env' yT zT vy vz h_no_plus hy hz))
    (logic_plus_comm2 vy vx vz)

/-- `rule:(+ (+ x y) z) ≡ (+ x (+ y z))` (associativity-of-+). -/
theorem dis_plus_assoc (w : World)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none) :
    ∀ env' : Env, ∃ N, ∀ f ≥ N,
      evalOpt f w env' (plusT (plusT xT yT) zT)
        = evalOpt f w env' (plusT xT (plusT yT zT)) := by
  intro env'
  obtain ⟨vx, hx⟩ := conv_var w env' xS (by decide)
  obtain ⟨vy, hy⟩ := conv_var w env' yS (by decide)
  obtain ⟨vz, hz⟩ := conv_var w env' zS (by decide)
  exact fuel_eq_of_conv
    (conv_plusT w env' (plusT xT yT) zT (Logic.plus vx vy) vz h_no_plus
      (conv_plusT w env' xT yT vx vy h_no_plus hx hy) hz)
    (conv_plusT w env' xT (plusT yT zT) vx (Logic.plus vy vz) h_no_plus hx
      (conv_plusT w env' yT zT vy vz h_no_plus hy hz))
    (logic_plus_assoc vx vy vz)

/-- `rule:FOLD-CONSTS-IN-+` — `(+ x (+ y z)) ≡ (+ (+ x y) z)` under two
    `syntaxp` SYNP hypotheses (premises the value-level fact never
    needs). -/
theorem dis_fold_consts (w : World)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (synpX synpY : SExpr) :
    ∀ env' : Env, EvTrue w env' synpX → EvTrue w env' synpY →
    ∃ N, ∀ f ≥ N,
      evalOpt f w env' (plusT xT (plusT yT zT))
        = evalOpt f w env' (plusT (plusT xT yT) zT) := by
  intro env' _ _
  obtain ⟨vx, hx⟩ := conv_var w env' xS (by decide)
  obtain ⟨vy, hy⟩ := conv_var w env' yS (by decide)
  obtain ⟨vz, hz⟩ := conv_var w env' zS (by decide)
  exact fuel_eq_of_conv
    (conv_plusT w env' xT (plusT yT zT) vx (Logic.plus vy vz) h_no_plus hx
      (conv_plusT w env' yT zT vy vz h_no_plus hy hz))
    (conv_plusT w env' (plusT xT yT) zT (Logic.plus vx vy) vz h_no_plus
      (conv_plusT w env' xT yT vx vy h_no_plus hx hy) hz)
    (logic_plus_assoc vx vy vz).symm

/-- `rule:(+ x (if a b c)) ≡ (if a (+ x b) (+ x c))` (if-lifting). -/
theorem dis_plus_if_lift (w : World)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none) :
    ∀ env' : Env, ∃ N, ∀ f ≥ N,
      evalOpt f w env' (plusT xT (ifT aT bT cT))
        = evalOpt f w env' (ifT aT (plusT xT bT) (plusT xT cT)) := by
  intro env'
  obtain ⟨vx, hx⟩ := conv_var w env' xS (by decide)
  obtain ⟨va, ha⟩ := conv_var w env' aS (by decide)
  obtain ⟨vb, hb⟩ := conv_var w env' bS (by decide)
  obtain ⟨vc, hc⟩ := conv_var w env' cS (by decide)
  cases hta : Logic.toBool va with
  | true =>
    exact fuel_eq_of_conv
      (conv_plusT w env' xT (ifT aT bT cT) vx vb h_no_plus hx
        (conv_if_true w env' aT bT cT va vb ha hta hb))
      (conv_if_true w env' aT (plusT xT bT) (plusT xT cT) va
        (Logic.plus vx vb) ha hta
        (conv_plusT w env' xT bT vx vb h_no_plus hx hb)) rfl
  | false =>
    have han : ∃ N, ∀ f ≥ N, evalOpt f w env' aT = some SExpr.nil :=
      nil_of_toBool_false hta ▸ ha
    exact fuel_eq_of_conv
      (conv_plusT w env' xT (ifT aT bT cT) vx vc h_no_plus hx
        (conv_if_false' w env' aT bT cT vc han hc))
      (conv_if_false' w env' aT (plusT xT bT) (plusT xT cT)
        (Logic.plus vx vc) han
        (conv_plusT w env' xT cT vx vc h_no_plus hx hc)) rfl

/-- `rule:(equal (if a b c) x) ≡ (if a (equal b x) (equal c x))`
    (if-lifting through EQUAL). -/
theorem dis_equal_if_lift (w : World)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none) :
    ∀ env' : Env, ∃ N, ∀ f ≥ N,
      evalOpt f w env' (equalT (ifT aT bT cT) xT)
        = evalOpt f w env' (ifT aT (equalT bT xT) (equalT cT xT)) := by
  intro env'
  obtain ⟨vx, hx⟩ := conv_var w env' xS (by decide)
  obtain ⟨va, ha⟩ := conv_var w env' aS (by decide)
  obtain ⟨vb, hb⟩ := conv_var w env' bS (by decide)
  obtain ⟨vc, hc⟩ := conv_var w env' cS (by decide)
  cases hta : Logic.toBool va with
  | true =>
    exact fuel_eq_of_conv
      (conv_equalT w env' (ifT aT bT cT) xT vb vx h_no_equal
        (conv_if_true w env' aT bT cT va vb ha hta hb) hx)
      (conv_if_true w env' aT (equalT bT xT) (equalT cT xT) va
        (Logic.equal vb vx) ha hta
        (conv_equalT w env' bT xT vb vx h_no_equal hb hx)) rfl
  | false =>
    have han : ∃ N, ∀ f ≥ N, evalOpt f w env' aT = some SExpr.nil :=
      nil_of_toBool_false hta ▸ ha
    exact fuel_eq_of_conv
      (conv_equalT w env' (ifT aT bT cT) xT vc vx h_no_equal
        (conv_if_false' w env' aT bT cT vc han hc) hx)
      (conv_if_false' w env' aT (equalT bT xT) (equalT cT xT)
        (Logic.equal vc vx) han
        (conv_equalT w env' cT xT vc vx h_no_equal hc hx)) rfl

/-! ## The `how-many` exec kit -/

abbrev howManyT (e x : SExpr) : SExpr := app2 "HOW-MANY" e x

private def q1 : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" }))
    (.cons (.atom (.number (.int 1))) .nil)
private def q0 : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" }))
    (.cons (.atom (.number (.int 0))) .nil)
private def int1 : SExpr := .atom (.number (.int 1))

/-- `(defun how-many (e x) …)`, macroexpanded. -/
def howManyBody : SExpr :=
  ifT (conspT xT)
    (ifT (equalT eT (carT xT))
      (plusT q1 (howManyT eT (cdrT xT)))
      (howManyT eT (cdrT xT)))
    q0

private def how_many_sym : Symbol := { package := "ACL2", name := "HOW-MANY" }

private theorem how_many_ns :
    (how_many_sym.isNamed "QUOTE" = false ∧
     how_many_sym.isNamed "IF" = false ∧
     how_many_sym.isNamed "LET" = false ∧
     how_many_sym.isNamed "LET*" = false) := by decide

/-- `how-many`'s body as a total Lean function. -/
def howManyExec (e x : SExpr) : SExpr :=
  if Logic.toBool (Logic.consp x) = true then
    if Logic.toBool (Logic.equal e (Logic.car x)) = true then
      Logic.plus int1 (howManyExec e (Logic.cdr x))
    else howManyExec e (Logic.cdr x)
  else .atom (.number (.int 0))
termination_by x.consCount
decreasing_by all_goals exact consCount_cdr_lt_of_consp (by assumption)

/-- Stage 1: a `how-many` call converges to `howManyExec` of its argument
    values. -/
theorem how_many_exec_corr (w : World)
    (h_hm : w.defs.get? how_many_sym = some ([eS, xS], howManyBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none) :
    ∀ (env : Env) (a x av xv : SExpr),
      ConvTo w env a av → ConvTo w env x xv →
      ConvTo w env (howManyT a x) (howManyExec av xv) := by
  have hbody : ∀ xv av : SExpr,
      ConvTo w (bindArgs [eS, xS] [av, xv]) howManyBody
        (howManyExec av xv) := by
    refine consCount_strong_induction
      (fun xv => ∀ av, ConvTo w (bindArgs [eS, xS] [av, xv]) howManyBody
        (howManyExec av xv)) ?_
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
    have heq := conv_builtin2 w _ { name := "EQUAL" } eT (carT xT) av
      (Logic.car xv) (Logic.equal av (Logic.car xv)) (by decide) h_no_equal
      hav hcar (callBuiltin_equal _ _)
    have hrec : ConvTo w (bindArgs [eS, xS] [av, xv])
        (howManyT eT (cdrT xT)) (howManyExec av (Logic.cdr xv)) →
        True := fun _ => trivial
    have houter := conv_if_lift w (bindArgs [eS, xS] [av, xv]) (conspT xT)
      (ifT (equalT eT (carT xT))
        (plusT q1 (howManyT eT (cdrT xT)))
        (howManyT eT (cdrT xT)))
      q0 (Logic.consp xv)
      (if Logic.toBool (Logic.equal av (Logic.car xv)) = true then
        Logic.plus int1 (howManyExec av (Logic.cdr xv))
       else howManyExec av (Logic.cdr xv))
      (.atom (.number (.int 0))) hconsp
      (fun hb =>
        have hrecc : ConvTo w (bindArgs [eS, xS] [av, xv])
            (howManyT eT (cdrT xT)) (howManyExec av (Logic.cdr xv)) :=
          conv_defn_2 w _ how_many_sym eT (cdrT xT) av (Logic.cdr xv)
            eS xS howManyBody _ how_many_ns h_hm hav hcdr
            (ih (Logic.cdr xv) (consCount_cdr_lt_of_consp hb) av)
        conv_if_lift w _ (equalT eT (carT xT))
          (plusT q1 (howManyT eT (cdrT xT)))
          (howManyT eT (cdrT xT))
          (Logic.equal av (Logic.car xv))
          (Logic.plus int1 (howManyExec av (Logic.cdr xv)))
          (howManyExec av (Logic.cdr xv)) heq
          (fun _ =>
            conv_builtin2 w _ { name := "BINARY-+" } q1
              (howManyT eT (cdrT xT)) int1
              (howManyExec av (Logic.cdr xv)) _ (by decide) h_no_plus
              (re_val_quote w _ int1) hrecc (callBuiltin_plus _ _))
          (fun _ => hrecc))
      (fun _ => re_val_quote w _ (.atom (.number (.int 0))))
    rw [howManyExec.eq_def]
    exact houter
  intro env a x av xv ha hx
  exact conv_defn_2 w env how_many_sym a x av xv eS xS howManyBody _
    how_many_ns h_hm ha hx (hbody xv av)

/-- Stage 2: `howManyExec` on an encoded list computes `List.count`
    (as an SExpr integer). -/
theorem howManyExec_enc (e : SExpr) (xs : List SExpr) :
    howManyExec e (enc xs) = .atom (.number (.int (xs.count e))) := by
  induction xs with
  | nil => rw [howManyExec.eq_def]; rfl
  | cons hd tl ih =>
    rw [howManyExec.eq_def, show enc (hd :: tl) = .cons hd (enc tl) from rfl,
        if_pos (show Logic.toBool (Logic.consp (.cons hd (enc tl))) = true
          from rfl),
        show Logic.car (SExpr.cons hd (enc tl)) = hd from rfl,
        show Logic.cdr (SExpr.cons hd (enc tl)) = enc tl from rfl]
    cases hbeq : e == hd with
    | true =>
      rw [if_pos (by simp [Logic.equal, hbeq, Logic.toBool, SExpr.t]), ih]
      have : (hd :: tl).count e = tl.count e + 1 := by
        simp [eq_of_beq hbeq]
      rw [this]
      simp [Logic.plus, int1, Logic.toRat, Logic.mkNumber]
      omega
    | false =>
      rw [if_neg (by simp [Logic.equal, hbeq, Logic.toBool]), ih]
      have : (hd :: tl).count e = tl.count e := by
        simp [Ne.symm (beq_eq_false_iff_ne.mp hbeq)]
      rw [this]

/-- `howManyExec` always yields a non-negative integer. -/
theorem howManyExec_nat (e x : SExpr) :
    ∃ n : Nat, howManyExec e x = .atom (.number (.int n)) := by
  fun_induction howManyExec e x with
  | case1 x _ _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by rw [hn]; simp [Logic.plus, int1, Logic.toRat,
      Logic.mkNumber]; omega⟩
  | case2 x _ _ ih => exact ih
  | case3 x _ => exact ⟨0, rfl⟩

/-- `tp:HOW-MANY`, world-parametric — the emitted non-negative-integer TP
    corollary. -/
theorem dis_how_many_tp (w : World)
    (h_hm : w.defs.get? how_many_sym = some ([eS, xS], howManyBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (e' : Env) (a0 a1 v : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e' (howManyT a0 a1) = some v) :
    (bif Logic.toBool (Logic.integerp v) then
      Logic.not (Logic.lt v (.atom (.number (.int 0))))
    else SExpr.nil) = SExpr.t := by
  obtain ⟨⟨N0, u0, h0⟩, ⟨N1, u1, h1⟩⟩ :=
    conv_args2_of_conv_app w e' { name := "HOW-MANY" } a0 a1 v (by decide) h
  have happ := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e' a0 a1 u0 u1 ⟨N0, h0⟩ ⟨N1, h1⟩
  rw [val_unique h happ]
  obtain ⟨n, hn⟩ := howManyExec_nat u0 u1
  rw [hn]
  simp [Logic.integerp, Logic.lt, Logic.not, Logic.toRat, Logic.toBool,
    show ¬((n : Int) < 0) from by omega]

/-- `membExec = nil` forces `howManyExec = 0` — the value-level content
    of NOT-MEMB-IMPLIES-HOW-MANY-IS-0, over ALL SExpr values. -/
private theorem howManyExec_zero_of_membExec_nil (a x : SExpr) :
    membExec a x = SExpr.nil →
    howManyExec a x = .atom (.number (.int 0)) := by
  fun_induction membExec a x with
  | case1 x hc heq =>
    intro h
    exact absurd h (by simp [SExpr.t])
  | case2 x hc heq ih =>
    intro h
    rw [howManyExec.eq_def, if_pos hc, if_neg heq]
    exact ih h
  | case3 x hc =>
    intro _
    rw [howManyExec.eq_def, if_neg hc]

/-- `rule:NOT-MEMB-IMPLIES-HOW-MANY-IS-0` — the ONE-hypothesis
    conditional rewrite, world-parametric. -/
theorem dis_not_memb_how_many_0 (w : World)
    (h_hm : w.defs.get? how_many_sym = some ([eS, xS], howManyBody))
    (h_memb : w.defs.get? { package := "ACL2", name := "MEMB" }
      = some ([{ package := "ACL2", name := "A" },
               { package := "ACL2", name := "X" }], membBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (h_no_not : w.defs.get? ({ name := "NOT" } : Symbol) = none) :
    ∀ env' : Env, EvTrue w env' (notT (membT aT xT)) →
    ∃ N, ∀ f ≥ N,
      evalOpt f w env' (howManyT aT xT) = evalOpt f w env' q0 := by
  intro env' hyp
  obtain ⟨va, ha⟩ := conv_var w env' aS (by decide)
  obtain ⟨vx, hx⟩ := conv_var w env' xS (by decide)
  have hmemb := memb_exec_corr w h_memb h_no_consp h_no_equal h_no_car
    h_no_cdr env' aT xT va vx ha hx
  have hnot := conv_builtin1 w env' { name := "NOT" } (membT aT xT)
    (membExec va vx) (Logic.not (membExec va vx)) (by decide) h_no_not
    hmemb (callBuiltin_not _)
  have hnil : membExec va vx = SExpr.nil := by
    have hne := ne_nil_of_evtrue_conv hyp hnot
    cases hm : membExec va vx <;> simp_all [Logic.not, Logic.toBool]
  have hhm := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus env' aT xT va vx ha hx
  rw [howManyExec_zero_of_membExec_nil va vx hnil] at hhm
  exact fuel_eq_of_conv hhm
    (re_val_quote w env' (.atom (.number (.int 0)))) rfl

/-! ## HOW-MANY-ISORT -/

/-- The HOW-MANY-ISORT replayed-statement formula:
    `(EQUAL (HOW-MANY E (ISORT X)) (HOW-MANY E X))`. -/
def how_many_isortFormula : SExpr :=
  equalT (howManyT eT (isortT xT)) (howManyT eT xT)

/-- HOW-MANY-ISORT, natively: INSERTION SORT PRESERVES MULTIPLICITY —
    `List.count` of every element is unchanged by `isortL`. -/
theorem how_many_isort_native_of_replayed (w : World)
    (h_hm : w.defs.get? how_many_sym = some ([eS, xS], howManyBody))
    (h_insert : w.defs.get? insert_sym = some ([eS, xS], insertBody))
    (h_isort : w.defs.get? isort_sym = some ([xS], isortBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env how_many_isortFormula = some v ∧ v ≠ SExpr.nil)
    (ev : SExpr) (xs : List SExpr) :
    (isortL xs).count ev = xs.count ev := by
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
  have hisort := corr_isort_enc w h_insert h_isort h_no_consp h_no_car
    h_no_cdr h_no_cons h_no_lexorder xs e xT hx
  have hL := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e eT (isortT xT) ev (enc (isortL xs)) he hisort
  rw [howManyExec_enc] at hL
  have hR := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus e eT xT ev (enc xs) he hx
  rw [howManyExec_enc] at hR
  have hnat := native_of_replayed_equal w e intRep _ _
    ((isortL xs).count ev) (xs.count ev) h_no_equal hL hR (hreplayed e)
  omega

/-! ## The qsort book: HOW-MANY-APPEND / CAR-APPEND -/

abbrev appendT (a b : SExpr) : SExpr := app2 "BINARY-APPEND" a b

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

/-! ## The REL / ALL-REL kit (qsort's comparison dispatch) -/

private def fnS : Symbol := { package := "ACL2", name := "FN" }
private def fnT : SExpr := .atom (.symbol { name := "FN" })
private def iS : Symbol := { package := "ACL2", name := "I" }
private def iT : SExpr := .atom (.symbol { name := "I" })
private def jS : Symbol := { package := "ACL2", name := "J" }
private def jT : SExpr := .atom (.symbol { name := "J" })
private def dS : Symbol := { package := "ACL2", name := "D" }
private def dT : SExpr := .atom (.symbol { name := "D" })
private def xEquivS : Symbol := { package := "ACL2", name := "X-EQUIV" }
private def xEquivT : SExpr := .atom (.symbol { name := "X-EQUIV" })

private def symV (s : String) : SExpr := .atom (.symbol { name := s })
private def qSym (s : String) : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" })) (.cons (symV s) .nil)
private def qT' : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" })) (.cons SExpr.t .nil)

abbrev relT (f i j : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "REL" }))
    (.cons f (.cons i (.cons j .nil)))
abbrev allRelT (f x e : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "ALL-REL" }))
    (.cons f (.cons x (.cons e .nil)))

/-- `(defun rel (fn i j) …)` — the 4-way comparison dispatch,
    macroexpanded. -/
def relBody : SExpr :=
  ifT (equalT fnT (qSym "LT"))
    (ifT (lexT iT jT) (ifT (equalT iT jT) qNil qT') qNil)
    (ifT (equalT fnT (qSym "LTE"))
      (lexT iT jT)
      (ifT (equalT fnT (qSym "GT"))
        (ifT (lexT jT iT) (ifT (equalT iT jT) qNil qT') qNil)
        (lexT jT iT)))

/-- `(defun all-rel (fn x e) …)`, macroexpanded. -/
def allRelBody : SExpr :=
  ifT (conspT xT)
    (ifT (relT fnT (carT xT) eT) (allRelT fnT (cdrT xT) eT) qNil)
    qT'

private def rel_sym : Symbol := { package := "ACL2", name := "REL" }
private def all_rel_sym : Symbol := { package := "ACL2", name := "ALL-REL" }

private theorem rel_ns :
    (rel_sym.isNamed "QUOTE" = false ∧ rel_sym.isNamed "IF" = false ∧
     rel_sym.isNamed "LET" = false ∧ rel_sym.isNamed "LET*" = false) := by
  decide
private theorem all_rel_ns :
    (all_rel_sym.isNamed "QUOTE" = false ∧
     all_rel_sym.isNamed "IF" = false ∧
     all_rel_sym.isNamed "LET" = false ∧
     all_rel_sym.isNamed "LET*" = false) := by decide

private theorem bindArgs_fij_fn (vf vi vj : SExpr) :
    (bindArgs [fnS, iS, jS] [vf, vi, vj]).get? fnS = some vf := by
  show (((({} : Env).insert jS vj).insert iS vi).insert fnS vf).get? fnS
    = some vf
  rw [Env.get?_insert, if_pos (by decide)]
private theorem bindArgs_fij_i (vf vi vj : SExpr) :
    (bindArgs [fnS, iS, jS] [vf, vi, vj]).get? iS = some vi := by
  show (((({} : Env).insert jS vj).insert iS vi).insert fnS vf).get? iS
    = some vi
  rw [Env.get?_insert, if_neg (by decide), Env.get?_insert,
      if_pos (by decide)]
private theorem bindArgs_fij_j (vf vi vj : SExpr) :
    (bindArgs [fnS, iS, jS] [vf, vi, vj]).get? jS = some vj := by
  show (((({} : Env).insert jS vj).insert iS vi).insert fnS vf).get? jS
    = some vj
  rw [Env.get?_insert, if_neg (by decide), Env.get?_insert,
      if_neg (by decide), Env.get?_insert, if_pos (by decide)]

private theorem bindArgs_fxe_fn (vf vx ve : SExpr) :
    (bindArgs [fnS, xS, eS] [vf, vx, ve]).get? fnS = some vf := by
  show (((({} : Env).insert eS ve).insert xS vx).insert fnS vf).get? fnS
    = some vf
  rw [Env.get?_insert, if_pos (by decide)]
private theorem bindArgs_fxe_x (vf vx ve : SExpr) :
    (bindArgs [fnS, xS, eS] [vf, vx, ve]).get? xS = some vx := by
  show (((({} : Env).insert eS ve).insert xS vx).insert fnS vf).get? xS
    = some vx
  rw [Env.get?_insert, if_neg (by decide), Env.get?_insert,
      if_pos (by decide)]
private theorem bindArgs_fxe_e (vf vx ve : SExpr) :
    (bindArgs [fnS, xS, eS] [vf, vx, ve]).get? eS = some ve := by
  show (((({} : Env).insert eS ve).insert xS vx).insert fnS vf).get? eS
    = some ve
  rw [Env.get?_insert, if_neg (by decide), Env.get?_insert,
      if_neg (by decide), Env.get?_insert, if_pos (by decide)]

/-- `rel`'s body as a total Lean function (non-recursive dispatch). -/
def relExec (fv i j : SExpr) : SExpr :=
  if Logic.toBool (Logic.equal fv (symV "LT")) = true then
    if Logic.toBool (lexorder i j) = true then
      if Logic.toBool (Logic.equal i j) = true then SExpr.nil else SExpr.t
    else SExpr.nil
  else if Logic.toBool (Logic.equal fv (symV "LTE")) = true then
    lexorder i j
  else if Logic.toBool (Logic.equal fv (symV "GT")) = true then
    if Logic.toBool (lexorder j i) = true then
      if Logic.toBool (Logic.equal i j) = true then SExpr.nil else SExpr.t
    else SExpr.nil
  else lexorder j i

theorem relExec_t_or_nil (f i j : SExpr) :
    relExec f i j = SExpr.t ∨ relExec f i j = SExpr.nil := by
  unfold relExec
  repeat' split
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exact lexorder_t_or_nil _ _

/-- Stage 1: a `rel` call converges to `relExec` of its argument
    values. -/
theorem rel_exec_corr (w : World)
    (h_rel : w.defs.get? rel_sym = some ([fnS, iS, jS], relBody))
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none) :
    ∀ (env : Env) (a b c av bv cv : SExpr),
      ConvTo w env a av → ConvTo w env b bv → ConvTo w env c cv →
      ConvTo w env (relT a b c) (relExec av bv cv) := by
  have hbody : ∀ vf vi vj : SExpr,
      ConvTo w (bindArgs [fnS, iS, jS] [vf, vi, vj]) relBody
        (relExec vf vi vj) := by
    intro vf vi vj
    set be := bindArgs [fnS, iS, jS] [vf, vi, vj] with hbe
    have hf := re_val_var_get w be { name := "FN" } vf
      (bindArgs_fij_fn vf vi vj)
    have hi := re_val_var_get w be { name := "I" } vi
      (bindArgs_fij_i vf vi vj)
    have hj := re_val_var_get w be { name := "J" } vj
      (bindArgs_fij_j vf vi vj)
    have hqLT : ConvTo w be (qSym "LT") (symV "LT") :=
      re_val_quote w be (symV "LT")
    have hqLTE : ConvTo w be (qSym "LTE") (symV "LTE") :=
      re_val_quote w be (symV "LTE")
    have hqGT : ConvTo w be (qSym "GT") (symV "GT") :=
      re_val_quote w be (symV "GT")
    have heqLT := conv_builtin2 w be { name := "EQUAL" } fnT (qSym "LT")
      vf (symV "LT") _ (by decide) h_no_equal hf hqLT (callBuiltin_equal _ _)
    have heqLTE := conv_builtin2 w be { name := "EQUAL" } fnT (qSym "LTE")
      vf (symV "LTE") _ (by decide) h_no_equal hf hqLTE
      (callBuiltin_equal _ _)
    have heqGT := conv_builtin2 w be { name := "EQUAL" } fnT (qSym "GT")
      vf (symV "GT") _ (by decide) h_no_equal hf hqGT
      (callBuiltin_equal _ _)
    have hlexIJ := conv_builtin2 w be { name := "LEXORDER" } iT jT vi vj
      (lexorder vi vj) (by decide) h_no_lexorder hi hj
      (callBuiltin_lexorder _ _)
    have hlexJI := conv_builtin2 w be { name := "LEXORDER" } jT iT vj vi
      (lexorder vj vi) (by decide) h_no_lexorder hj hi
      (callBuiltin_lexorder _ _)
    have heqIJ := conv_builtin2 w be { name := "EQUAL" } iT jT vi vj
      (Logic.equal vi vj) (by decide) h_no_equal hi hj
      (callBuiltin_equal _ _)
    -- the two strict-comparison sub-nests
    have hStrictIJ : ConvTo w be
        (ifT (lexT iT jT) (ifT (equalT iT jT) qNil qT') qNil)
        (if Logic.toBool (lexorder vi vj) = true then
          (if Logic.toBool (Logic.equal vi vj) = true then SExpr.nil
           else SExpr.t)
         else SExpr.nil) :=
      conv_if_lift w be _ _ _ _ _ _ hlexIJ
        (fun _ => conv_if_lift w be _ _ _ _ _ _ heqIJ
          (fun _ => re_val_quote w be SExpr.nil)
          (fun _ => re_val_quote w be SExpr.t))
        (fun _ => re_val_quote w be SExpr.nil)
    have hStrictJI : ConvTo w be
        (ifT (lexT jT iT) (ifT (equalT iT jT) qNil qT') qNil)
        (if Logic.toBool (lexorder vj vi) = true then
          (if Logic.toBool (Logic.equal vi vj) = true then SExpr.nil
           else SExpr.t)
         else SExpr.nil) :=
      conv_if_lift w be _ _ _ _ _ _ hlexJI
        (fun _ => conv_if_lift w be _ _ _ _ _ _ heqIJ
          (fun _ => re_val_quote w be SExpr.nil)
          (fun _ => re_val_quote w be SExpr.t))
        (fun _ => re_val_quote w be SExpr.nil)
    have houter := conv_if_lift w be _ _ _ _ _ _ heqLT
      (fun _ => hStrictIJ)
      (fun _ => conv_if_lift w be _ _ _ _ _ _ heqLTE
        (fun _ => hlexIJ)
        (fun _ => conv_if_lift w be _ _ _ _ _ _ heqGT
          (fun _ => hStrictJI)
          (fun _ => hlexJI)))
    unfold relExec
    exact houter
  intro env a b c av bv cv ha hb hc
  exact conv_defn_3 w env rel_sym a b c av bv cv fnS iS jS relBody _
    rel_ns h_rel ha hb hc (hbody av bv cv)

/-- `all-rel`'s body as a total Lean function. -/
def allRelExec (fv x ev : SExpr) : SExpr :=
  if Logic.toBool (Logic.consp x) = true then
    if Logic.toBool (relExec fv (Logic.car x) ev) = true then
      allRelExec fv (Logic.cdr x) ev
    else SExpr.nil
  else SExpr.t
termination_by x.consCount
decreasing_by exact consCount_cdr_lt_of_consp (by assumption)

/-- Stage 1: an `all-rel` call converges to `allRelExec` of its argument
    values. -/
theorem all_rel_exec_corr (w : World)
    (h_rel : w.defs.get? rel_sym = some ([fnS, iS, jS], relBody))
    (h_ar : w.defs.get? all_rel_sym = some ([fnS, xS, eS], allRelBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none) :
    ∀ (env : Env) (a x b av xv bv : SExpr),
      ConvTo w env a av → ConvTo w env x xv → ConvTo w env b bv →
      ConvTo w env (allRelT a x b) (allRelExec av xv bv) := by
  have hbody : ∀ (xv : SExpr) (vf ve : SExpr),
      ConvTo w (bindArgs [fnS, xS, eS] [vf, xv, ve]) allRelBody
        (allRelExec vf xv ve) := by
    refine consCount_strong_induction
      (fun xv => ∀ vf ve, ConvTo w (bindArgs [fnS, xS, eS] [vf, xv, ve])
        allRelBody (allRelExec vf xv ve)) ?_
    intro xv ih vf ve
    have hf := re_val_var_get w (bindArgs [fnS, xS, eS] [vf, xv, ve])
      { name := "FN" } vf (bindArgs_fxe_fn vf xv ve)
    have hx := re_val_var_get w (bindArgs [fnS, xS, eS] [vf, xv, ve])
      { name := "X" } xv (bindArgs_fxe_x vf xv ve)
    have he := re_val_var_get w (bindArgs [fnS, xS, eS] [vf, xv, ve])
      { name := "E" } ve (bindArgs_fxe_e vf xv ve)
    have hconsp := conv_builtin1 w _ { name := "CONSP" } xT xv
      (Logic.consp xv) (by decide) h_no_consp hx (callBuiltin_consp _)
    have hcar := conv_builtin1 w _ { name := "CAR" } xT xv
      (Logic.car xv) (by decide) h_no_car hx (callBuiltin_car _)
    have hcdr := conv_builtin1 w _ { name := "CDR" } xT xv
      (Logic.cdr xv) (by decide) h_no_cdr hx (callBuiltin_cdr _)
    have hrel := rel_exec_corr w h_rel h_no_equal h_no_lexorder _
      fnT (carT xT) eT vf (Logic.car xv) ve hf hcar he
    have houter := conv_if_lift w (bindArgs [fnS, xS, eS] [vf, xv, ve])
      (conspT xT)
      (ifT (relT fnT (carT xT) eT) (allRelT fnT (cdrT xT) eT) qNil)
      qT' (Logic.consp xv)
      (if Logic.toBool (relExec vf (Logic.car xv) ve) = true then
        allRelExec vf (Logic.cdr xv) ve
       else SExpr.nil)
      SExpr.t hconsp
      (fun hb =>
        conv_if_lift w _ (relT fnT (carT xT) eT)
          (allRelT fnT (cdrT xT) eT) qNil
          (relExec vf (Logic.car xv) ve)
          (allRelExec vf (Logic.cdr xv) ve) SExpr.nil hrel
          (fun _ =>
            conv_defn_3 w _ all_rel_sym fnT (cdrT xT) eT vf (Logic.cdr xv)
              ve fnS xS eS allRelBody _ all_rel_ns h_ar hf hcdr he
              (ih (Logic.cdr xv) (consCount_cdr_lt_of_consp hb) vf ve))
          (fun _ => re_val_quote w _ SExpr.nil))
      (fun _ => re_val_quote w _ SExpr.t)
    rw [allRelExec.eq_def]
    exact houter
  intro env a x b av xv bv ha hx hb
  exact conv_defn_3 w env all_rel_sym a x b av xv bv fnS xS eS allRelBody _
    all_rel_ns h_ar ha hx hb (hbody xv av bv)

/-- The NATIVE reading of one REL verdict — an ordinary Lean match on the
    four comparison modes, in `lexorderB`/`==` vocabulary only (the mirror
    criterion: no exec function in a mirror statement). -/
def relL (fv a e : SExpr) : Bool :=
  if fv == symV "LT" then lexorderB a e && !(a == e)
  else if fv == symV "LTE" then lexorderB a e
  else if fv == symV "GT" then lexorderB e a && !(a == e)
  else lexorderB e a

private theorem toBool_equal (a b : SExpr) :
    Logic.toBool (Logic.equal a b) = (a == b) := by
  cases h : a == b <;> simp [Logic.equal, h]

private theorem toBool_strict (x y a e : SExpr) :
    Logic.toBool
      (if Logic.toBool (lexorder x y) = true then
        (if Logic.toBool (Logic.equal a e) = true then SExpr.nil
         else SExpr.t)
       else SExpr.nil)
      = (lexorderB x y && !(a == e)) := by
  rw [toBool_lexorder, toBool_equal]
  cases hl : lexorderB x y <;> cases he : a == e <;>
    simp [Logic.toBool, SExpr.t]

/-- The exec dispatch computes exactly the native `relL` verdict. -/
theorem toBool_relExec (fv a e : SExpr) :
    Logic.toBool (relExec fv a e) = relL fv a e := by
  unfold relExec relL
  by_cases hLT : (fv == symV "LT") = true
  · rw [if_pos (by rw [toBool_equal]; exact hLT), if_pos hLT]
    exact toBool_strict a e a e
  · rw [if_neg (by rw [toBool_equal]; exact hLT), if_neg hLT]
    by_cases hLTE : (fv == symV "LTE") = true
    · rw [if_pos (by rw [toBool_equal]; exact hLTE), if_pos hLTE]
      exact toBool_lexorder a e
    · rw [if_neg (by rw [toBool_equal]; exact hLTE), if_neg hLTE]
      by_cases hGT : (fv == symV "GT") = true
      · rw [if_pos (by rw [toBool_equal]; exact hGT), if_pos hGT]
        exact toBool_strict e a a e
      · rw [if_neg (by rw [toBool_equal]; exact hGT), if_neg hGT]
        exact toBool_lexorder e a

/-- The native reading of ALL-REL: every element is `relL`-related to
    `ev`. -/
def allRelL (fv ev : SExpr) (xs : List SExpr) : Bool :=
  xs.all (fun a => relL fv a ev)

/-- Stage 2: `allRelExec` on an encoded list computes `allRelL`. -/
theorem allRelExec_enc (fv ev : SExpr) (xs : List SExpr) :
    allRelExec fv (enc xs) ev = boolEnc (allRelL fv ev xs) := by
  induction xs with
  | nil => rw [allRelExec.eq_def]; rfl
  | cons hd tl ih =>
    rw [allRelExec.eq_def, show enc (hd :: tl) = .cons hd (enc tl) from rfl,
        if_pos (show Logic.toBool (Logic.consp (.cons hd (enc tl))) = true
          from rfl),
        show Logic.car (SExpr.cons hd (enc tl)) = hd from rfl,
        show Logic.cdr (SExpr.cons hd (enc tl)) = enc tl from rfl]
    cases hb : relL fv hd ev with
    | true =>
      rw [if_pos (show Logic.toBool (relExec fv hd ev) = true from by
        rw [toBool_relExec, hb]), ih]
      simp only [allRelL, List.all_cons, hb, Bool.true_and]
    | false =>
      rw [if_neg (show ¬(Logic.toBool (relExec fv hd ev) = true) from by
        rw [toBool_relExec, hb]; simp)]
      simp only [allRelL, List.all_cons, hb, Bool.false_and, boolEnc,
        cond_false]

/-- 3-ary argument STRICTNESS (the 2-ary `evalOpt_app2_args`, one more
    argument): a converging 3-ary (non-special) application has
    converging arguments. -/
private theorem evalOpt_app3_args (f : Nat) (w : World) (env : Env)
    (s : Symbol) (a1 a2 a3 v : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h : evalOpt (f + 1) w env
      (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 (.cons a3 .nil))))
      = some v) :
    (∃ u, evalOpt f w env a1 = some u) ∧
    (∃ u, evalOpt f w env a2 = some u) ∧
    (∃ u, evalOpt f w env a3 = some u) := by
  rw [show evalOpt (f + 1) w env
        (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 (.cons a3 .nil))))
        = evalOptStep (evalOpt f) w env
            (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 (.cons a3 .nil))))
        from rfl] at h
  unfold evalOptStep at h
  simp only [Symbol.isNamed, SExpr.toList?] at h
  obtain ⟨hq, hi, hl, hls⟩ := h_ns
  simp only [Symbol.isNamed] at hq hi hl hls
  simp only [hq, hi, hl, hls, Bool.or_eq_true, Bool.false_eq_true, or_self,
             ↓reduceIte] at h
  cases hu1 : evalOpt f w env a1 with
  | none => simp [List.mapM, List.mapM.loop, hu1] at h
  | some u1 =>
    cases hu2 : evalOpt f w env a2 with
    | none => simp [List.mapM, List.mapM.loop, hu1, hu2] at h
    | some u2 =>
      cases hu3 : evalOpt f w env a3 with
      | none => simp [List.mapM, List.mapM.loop, hu1, hu2, hu3] at h
      | some u3 => exact ⟨⟨u1, rfl⟩, ⟨u2, rfl⟩, ⟨u3, rfl⟩⟩

private theorem conv_args3_of_conv_app (w : World) (env : Env) (s : Symbol)
    (a1 a2 a3 v : SExpr)
    (h_ns : s.isNamed "QUOTE" = false ∧ s.isNamed "IF" = false ∧
            s.isNamed "LET" = false ∧ s.isNamed "LET*" = false)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w env
      (.cons (.atom (.symbol s)) (.cons a1 (.cons a2 (.cons a3 .nil))))
      = some v) :
    (∃ N, ∃ u, ∀ f ≥ N, evalOpt f w env a1 = some u) ∧
    (∃ N, ∃ u, ∀ f ≥ N, evalOpt f w env a2 = some u) ∧
    (∃ N, ∃ u, ∀ f ≥ N, evalOpt f w env a3 = some u) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨conv_fix ⟨N, fun f hf => ?_⟩, conv_fix ⟨N, fun f hf => ?_⟩,
          conv_fix ⟨N, fun f hf => ?_⟩⟩
  · exact (evalOpt_app3_args f w env s a1 a2 a3 v h_ns
      (hN (f + 1) (by omega))).1
  · exact (evalOpt_app3_args f w env s a1 a2 a3 v h_ns
      (hN (f + 1) (by omega))).2.1
  · exact (evalOpt_app3_args f w env s a1 a2 a3 v h_ns
      (hN (f + 1) (by omega))).2.2

/-- `allRelExec` is two-valued. -/
theorem allRelExec_t_or_nil (fv x ev : SExpr) :
    allRelExec fv x ev = SExpr.t ∨ allRelExec fv x ev = SExpr.nil := by
  fun_induction allRelExec fv x ev with
  | case1 x _ _ ih => exact ih
  | case2 x _ _ => exact Or.inr rfl
  | case3 x _ => exact Or.inl rfl

/-- `tp:ALL-REL`, world-parametric — the emitted boolean TP corollary. -/
theorem dis_all_rel_tp (w : World)
    (h_rel : w.defs.get? rel_sym = some ([fnS, iS, jS], relBody))
    (h_ar : w.defs.get? all_rel_sym = some ([fnS, xS, eS], allRelBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (e' : Env) (a0 a1 a2 v : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e' (allRelT a0 a1 a2) = some v) :
    (bif Logic.toBool (Logic.equal v SExpr.t) then SExpr.t
     else Logic.equal v SExpr.nil) = SExpr.t := by
  obtain ⟨⟨N0, u0, h0⟩, ⟨N1, u1, h1⟩, ⟨N2, u2, h2⟩⟩ :=
    conv_args3_of_conv_app w e' { name := "ALL-REL" } a0 a1 a2 v
      (by decide) h
  have happ := all_rel_exec_corr w h_rel h_ar h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_lexorder e' a0 a1 a2 u0 u1 u2
    ⟨N0, h0⟩ ⟨N1, h1⟩ ⟨N2, h2⟩
  rw [val_unique h happ]
  rcases allRelExec_t_or_nil u0 u1 u2 with ht | hn
  · rw [ht]; simp [Logic.equal, Logic.toBool]
  · rw [hn]; rfl

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

/-! ## The FILTER kit -/

abbrev filterT (f x e : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "FILTER" }))
    (.cons f (.cons x (.cons e .nil)))

/-- `(defun filter (fn x e) …)`, macroexpanded. -/
def filterBody : SExpr :=
  ifT (conspT xT)
    (ifT (relT fnT (carT xT) eT)
      (consT (carT xT) (filterT fnT (cdrT xT) eT))
      (filterT fnT (cdrT xT) eT))
    qNil

private def filter_sym : Symbol := { package := "ACL2", name := "FILTER" }

private theorem filter_ns :
    (filter_sym.isNamed "QUOTE" = false ∧ filter_sym.isNamed "IF" = false ∧
     filter_sym.isNamed "LET" = false ∧
     filter_sym.isNamed "LET*" = false) := by decide

/-- `filter`'s body as a total Lean function. -/
def filterExec (fv x ev : SExpr) : SExpr :=
  if Logic.toBool (Logic.consp x) = true then
    if Logic.toBool (relExec fv (Logic.car x) ev) = true then
      Logic.cons (Logic.car x) (filterExec fv (Logic.cdr x) ev)
    else filterExec fv (Logic.cdr x) ev
  else SExpr.nil
termination_by x.consCount
decreasing_by all_goals exact consCount_cdr_lt_of_consp (by assumption)

/-- Stage 1: a `filter` call converges to `filterExec` of its argument
    values. -/
theorem filter_exec_corr (w : World)
    (h_rel : w.defs.get? rel_sym = some ([fnS, iS, jS], relBody))
    (h_filter : w.defs.get? filter_sym = some ([fnS, xS, eS], filterBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none) :
    ∀ (env : Env) (a x b av xv bv : SExpr),
      ConvTo w env a av → ConvTo w env x xv → ConvTo w env b bv →
      ConvTo w env (filterT a x b) (filterExec av xv bv) := by
  have hbody : ∀ (xv : SExpr) (vf ve : SExpr),
      ConvTo w (bindArgs [fnS, xS, eS] [vf, xv, ve]) filterBody
        (filterExec vf xv ve) := by
    refine consCount_strong_induction
      (fun xv => ∀ vf ve, ConvTo w (bindArgs [fnS, xS, eS] [vf, xv, ve])
        filterBody (filterExec vf xv ve)) ?_
    intro xv ih vf ve
    have hf := re_val_var_get w (bindArgs [fnS, xS, eS] [vf, xv, ve])
      { name := "FN" } vf (bindArgs_fxe_fn vf xv ve)
    have hx := re_val_var_get w (bindArgs [fnS, xS, eS] [vf, xv, ve])
      { name := "X" } xv (bindArgs_fxe_x vf xv ve)
    have he := re_val_var_get w (bindArgs [fnS, xS, eS] [vf, xv, ve])
      { name := "E" } ve (bindArgs_fxe_e vf xv ve)
    have hconsp := conv_builtin1 w _ { name := "CONSP" } xT xv
      (Logic.consp xv) (by decide) h_no_consp hx (callBuiltin_consp _)
    have hcar := conv_builtin1 w _ { name := "CAR" } xT xv
      (Logic.car xv) (by decide) h_no_car hx (callBuiltin_car _)
    have hcdr := conv_builtin1 w _ { name := "CDR" } xT xv
      (Logic.cdr xv) (by decide) h_no_cdr hx (callBuiltin_cdr _)
    have hrel := rel_exec_corr w h_rel h_no_equal h_no_lexorder _
      fnT (carT xT) eT vf (Logic.car xv) ve hf hcar he
    have houter := conv_if_lift w (bindArgs [fnS, xS, eS] [vf, xv, ve])
      (conspT xT)
      (ifT (relT fnT (carT xT) eT)
        (consT (carT xT) (filterT fnT (cdrT xT) eT))
        (filterT fnT (cdrT xT) eT))
      qNil (Logic.consp xv)
      (if Logic.toBool (relExec vf (Logic.car xv) ve) = true then
        Logic.cons (Logic.car xv) (filterExec vf (Logic.cdr xv) ve)
       else filterExec vf (Logic.cdr xv) ve)
      SExpr.nil hconsp
      (fun hb =>
        have hrecc : ConvTo w (bindArgs [fnS, xS, eS] [vf, xv, ve])
            (filterT fnT (cdrT xT) eT)
            (filterExec vf (Logic.cdr xv) ve) :=
          conv_defn_3 w _ filter_sym fnT (cdrT xT) eT vf (Logic.cdr xv) ve
            fnS xS eS filterBody _ filter_ns h_filter hf hcdr he
            (ih (Logic.cdr xv) (consCount_cdr_lt_of_consp hb) vf ve)
        conv_if_lift w _ (relT fnT (carT xT) eT)
          (consT (carT xT) (filterT fnT (cdrT xT) eT))
          (filterT fnT (cdrT xT) eT)
          (relExec vf (Logic.car xv) ve)
          (Logic.cons (Logic.car xv) (filterExec vf (Logic.cdr xv) ve))
          (filterExec vf (Logic.cdr xv) ve) hrel
          (fun _ =>
            conv_builtin2 w _ { name := "CONS" } (carT xT)
              (filterT fnT (cdrT xT) eT) (Logic.car xv)
              (filterExec vf (Logic.cdr xv) ve) _ (by decide) h_no_cons
              hcar hrecc rfl)
          (fun _ => hrecc))
      (fun _ => re_val_quote w _ SExpr.nil)
    rw [filterExec.eq_def]
    exact houter
  intro env a x b av xv bv ha hx hb
  exact conv_defn_3 w env filter_sym a x b av xv bv fnS xS eS filterBody _
    filter_ns h_filter ha hx hb (hbody xv av bv)

/-- The native reading of FILTER: `List.filter` by the `relL` verdict. -/
def filterL (fv ev : SExpr) (xs : List SExpr) : List SExpr :=
  xs.filter (fun a => relL fv a ev)

/-- Stage 2: `filterExec` on an encoded list computes `filterL`. -/
theorem filterExec_enc (fv ev : SExpr) (xs : List SExpr) :
    filterExec fv (enc xs) ev = enc (filterL fv ev xs) := by
  induction xs with
  | nil => rw [filterExec.eq_def]; rfl
  | cons hd tl ih =>
    rw [filterExec.eq_def, show enc (hd :: tl) = .cons hd (enc tl) from rfl,
        if_pos (show Logic.toBool (Logic.consp (.cons hd (enc tl))) = true
          from rfl),
        show Logic.car (SExpr.cons hd (enc tl)) = hd from rfl,
        show Logic.cdr (SExpr.cons hd (enc tl)) = enc tl from rfl]
    cases hb : relL fv hd ev with
    | true =>
      rw [if_pos (show Logic.toBool (relExec fv hd ev) = true from by
        rw [toBool_relExec, hb]), ih]
      simp only [filterL, List.filter_cons, hb, if_true]
      rfl
    | false =>
      rw [if_neg (show ¬(Logic.toBool (relExec fv hd ev) = true) from by
        rw [toBool_relExec, hb]; simp), ih]
      simp only [filterL, List.filter_cons, hb, Bool.false_eq_true,
        if_false]

/-! ## The concrete comparison modes (native vocabulary for the FILTER
rows: the quoted mode symbols specialize `relL` to plain `lexorderB`
combinations). -/

/-- Strict lexorder: `≤` and not equal. -/
def lexLtB (a e : SExpr) : Bool := lexorderB a e && !(a == e)

theorem relL_LT (a e : SExpr) : relL (symV "LT") a e = lexLtB a e := by
  rw [relL, if_pos (by decide)]; rfl
theorem relL_LTE (a e : SExpr) : relL (symV "LTE") a e = lexorderB a e := by
  rw [relL, if_neg (by decide), if_pos (by decide)]
theorem relL_GTE (a e : SExpr) : relL (symV "GTE") a e = lexorderB e a := by
  rw [relL, if_neg (by decide), if_neg (by decide), if_neg (by decide)]

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

end ACL2.Worlds.Sorting
