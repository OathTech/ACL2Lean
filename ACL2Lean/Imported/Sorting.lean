import ACL2Lean.Imported.Perm
import ACL2Lean.Imported.ExecGen

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

open ACL2 ACL2.Replay ACL2.Lifting ACL2.Worlds.Perm ACL2.ExecGen

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

private theorem callBuiltin_lexorder (a b : SExpr) :
    callBuiltin "LEXORDER" [a, b] = some (lexorder a b) := rfl

/-- `insert`'s body as a total Lean function (shape-exact, D2) —
    GENERATED (1b retirement: the hand def this replaces is reproduced
    by the generator's body walk; every downstream consumer, starting
    with the hand `insert_exec_corr`, re-elaborates against it). -/
derive_exec% insertExec corr insert_exec_corr for insert_sym
  formals [eS, xS] body insertBody measured 1

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

/-- `isort`'s body as a total Lean function — GENERATED (the INSERT call
    resolves through the kit registry). -/
derive_exec% isortExec corr isort_exec_corr for isort_sym
  formals [xS] body isortBody measured 0

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

/-- `tp:INSERT` — the emitted `(CONSP (INSERT E X))` corollary; wrapper
    GENERATED (1c), value-shape ending human. -/
derive_exec_tp% dis_insert_tp for "INSERT"
  (v => Logic.consp v = SExpr.t)
  ending exact insertExec_consp u0 u1

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

/-! ## ORDERED-PERMS — the book's capstone: for lexorder-sorted lists,
    equality IS permutation-equivalence -/

private def permT' (x y : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "PERM" })) (.cons x (.cons y .nil))
private def trueListpT (x : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "TRUE-LISTP" })) (.cons x .nil)

/-- The ORDERED-PERMS replayed-statement formula — the root Goal clause,
    exactly as the log emits it:
    `(IMPLIES (IF (TRUE-LISTP A) (IF (TRUE-LISTP B)
                 (IF (ORDEREDP A) (ORDEREDP B) 'NIL) 'NIL) 'NIL)
              (EQUAL (EQUAL A B) (PERM A B)))`. -/
def ordered_permsFormula : SExpr :=
  impliesT
    (ifT (trueListpT aT)
      (ifT (trueListpT bT)
        (ifT (orderedpT aT) (orderedpT bT) qNil) qNil) qNil)
    (equalT (equalT aT bT) (permT' aT bT))

/-- Encodings are BEq exactly when the lists are (`enc` is injective and
    `SExpr`'s BEq is lawful decidable equality). -/
private theorem enc_beq (xs ys : List SExpr) :
    (enc xs == enc ys) = (xs == ys) := by
  by_cases h : xs = ys
  · subst h; simp
  · have hne : enc xs ≠ enc ys := fun hE => h (enc_inj hE)
    simp [h, hne]

/-- ORDERED-PERMS, natively: for lexorder-sorted lists, list equality IS
    permutation-equivalence (the Bool identity `(xs == ys) = xs.isPerm ys`).
    The replayed statement is consumed at exactly one seam. -/
theorem ordered_perms_native_of_replayed (w : World)
    (h_orderedp : w.defs.get? { package := "ACL2", name := "ORDEREDP" }
      = some ([{ package := "ACL2", name := "X" }],
              chain2Body "LEXORDER" "ORDEREDP"))
    (h_perm : w.defs.get? { package := "ACL2", name := "PERM" }
      = some ([{ package := "ACL2", name := "X" },
               { package := "ACL2", name := "Y" }], permBody))
    (h_memb : w.defs.get? { package := "ACL2", name := "MEMB" }
      = some ([{ package := "ACL2", name := "A" },
               { package := "ACL2", name := "X" }], membBody))
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
    (h_no_truelistp : w.defs.get? ({ name := "TRUE-LISTP" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env ordered_permsFormula = some v ∧ v ≠ SExpr.nil)
    (xs ys : List SExpr)
    (hx : orderedpRec xs = true) (hy : orderedpRec ys = true) :
    (xs == ys) = xs.isPerm ys := by
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
  -- the four antecedent conjuncts, all truthy
  have htlA : ∃ N, ∀ f ≥ N,
      evalOpt f w e (trueListpT aT) = some SExpr.t := by
    have := conv_builtin1 w e { name := "TRUE-LISTP" } aT (enc xs)
      (Logic.trueListp (enc xs)) (by decide) h_no_truelistp ha rfl
    rwa [trueListp_enc] at this
  have htlB : ∃ N, ∀ f ≥ N,
      evalOpt f w e (trueListpT bT) = some SExpr.t := by
    have := conv_builtin1 w e { name := "TRUE-LISTP" } bT (enc ys)
      (Logic.trueListp (enc ys)) (by decide) h_no_truelistp hb rfl
    rwa [trueListp_enc] at this
  have hoA := corr_orderedp_enc w h_orderedp h_no_consp h_no_cdr h_no_car
    h_no_lexorder xs e aT ha
  have hoB := corr_orderedp_enc w h_orderedp h_no_consp h_no_cdr h_no_car
    h_no_lexorder ys e bT hb
  -- the antecedent IF-nest evaluates through its all-true spine to the
  -- innermost conjunct's value, `boolEnc (orderedpRec ys)` = t
  have hAnt : ∃ N, ∀ f ≥ N,
      evalOpt f w e (ifT (trueListpT aT)
        (ifT (trueListpT bT)
          (ifT (orderedpT aT) (orderedpT bT) qNil) qNil) qNil)
        = some (boolEnc (orderedpRec ys)) := by
    have h3 := conv_if_true w e (orderedpT aT) (orderedpT bT) qNil
      (boolEnc (orderedpRec xs)) (boolEnc (orderedpRec ys)) hoA
      (by rw [hx]; rfl) hoB
    have h2 := conv_if_true w e (trueListpT bT)
      (ifT (orderedpT aT) (orderedpT bT) qNil) qNil SExpr.t
      (boolEnc (orderedpRec ys)) htlB rfl h3
    exact conv_if_true w e (trueListpT aT)
      (ifT (trueListpT bT)
        (ifT (orderedpT aT) (orderedpT bT) qNil) qNil) qNil SExpr.t
      (boolEnc (orderedpRec ys)) htlA rfl h2
  -- the conclusion's value: Logic.equal of the two boolean sides
  have hEqAB := conv_builtin2 w e { name := "EQUAL" } aT bT (enc xs)
    (enc ys) (Logic.equal (enc xs) (enc ys)) (by decide) h_no_equal
    ha hb (callBuiltin_equal _ _)
  have hPerm := corr_perm_enc w h_perm h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons xs ys e aT bT ha hb
  have hConcl := conv_builtin2 w e { name := "EQUAL" } (equalT aT bT)
    (permT' aT bT) (Logic.equal (enc xs) (enc ys))
    (boolEnc (xs.isPerm ys))
    (Logic.equal (Logic.equal (enc xs) (enc ys)) (boolEnc (xs.isPerm ys)))
    (by decide) h_no_equal hEqAB hPerm (callBuiltin_equal _ _)
  -- the whole formula's value, pinned truthy by the replayed statement
  have hImp := conv_builtin2 w e { name := "IMPLIES" }
    (ifT (trueListpT aT)
      (ifT (trueListpT bT)
        (ifT (orderedpT aT) (orderedpT bT) qNil) qNil) qNil)
    (equalT (equalT aT bT) (permT' aT bT))
    (boolEnc (orderedpRec ys))
    (Logic.equal (Logic.equal (enc xs) (enc ys)) (boolEnc (xs.isPerm ys)))
    (Logic.implies (boolEnc (orderedpRec ys))
      (Logic.equal (Logic.equal (enc xs) (enc ys))
        (boolEnc (xs.isPerm ys))))
    (by decide) h_no_implies hAnt hConcl (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (replayed_pins_ne_nil (hreplayed e) hImp)
  have htq := truthy_of_implies_t hIt (by rw [hy]; rfl)
  have hEq : Logic.equal (enc xs) (enc ys) = boolEnc (xs.isPerm ys) :=
    eq_of_equal_truthy htq
  have hL : Logic.equal (enc xs) (enc ys)
      = boolEnc (enc xs == enc ys) := by
    cases h : enc xs == enc ys <;> simp [Logic.equal, boolEnc, h]
  rw [← enc_beq]
  exact bool_of_cond_eq (hL.symm.trans hEq)

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

/-- `rule:(+ y x) ≡ (+ x y)` — the arithmetic-3 rune `|(+ y x)|`
    (NOT ground-zero COMMUTATIVITY-OF-+, whose stored orientation is
    the reverse — audit 2026-07-31 inside finding 1). -/
theorem dis_plus_comm (w : World)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none) :
    ∀ env' : Env, ∃ N, ∀ f ≥ N,
      evalOpt f w env' (plusT yT xT) = evalOpt f w env' (plusT xT yT) := by
  intro env'
  obtain ⟨vx, hx⟩ := conv_var w env' xS (by decide)
  obtain ⟨vy, hy⟩ := conv_var w env' yS (by decide)
  exact fuel_eq_of_conv (conv_plusT w env' yT xT vy vx h_no_plus hy hx)
    (conv_plusT w env' xT yT vx vy h_no_plus hx hy) (logic_plus_comm vy vx)

/-- `rule:(+ y (+ x z)) ≡ (+ x (+ y z))` — the arithmetic-3 rune
    `|(+ y (+ x z))|`. -/
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

/-- `rule:(+ (+ x y) z) ≡ (+ x (+ y z))` — the arithmetic-3 rune
    `|(+ (+ x y) z)|` (no ASSOCIATIVITY-OF-+ is stored in these
    logs). -/
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

/-- `how-many`'s body as a total Lean function. -/
derive_exec% howManyExec corr how_many_exec_corr for how_many_sym
  formals [eS, xS] body howManyBody measured 1

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
      simp [Logic.plus, Logic.toRat, Logic.mkNumber]
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
    exact ⟨n + 1, by rw [hn]; simp [Logic.plus, Logic.toRat,
      Logic.mkNumber]; omega⟩
  | case2 x _ _ ih => exact ih
  | case3 x _ => exact ⟨0, rfl⟩

/-- `tp:HOW-MANY` — the emitted non-negative-integer corollary; wrapper
    GENERATED (1c). -/
derive_exec_tp% dis_how_many_tp for "HOW-MANY"
  (v => (bif Logic.toBool (Logic.integerp v) then
      Logic.not (Logic.lt v (.atom (.number (.int 0))))
    else SExpr.nil) = SExpr.t)
  ending
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

/-! ## The convert-perm book: NOT-MEMB-IMPLIES-HOW-MANY-IS-0 -/

/-- The NOT-MEMB-IMPLIES-HOW-MANY-IS-0 replayed-statement formula:
    `(IMPLIES (NOT (MEMB A X)) (EQUAL (HOW-MANY A X) '0))`. -/
def not_memb_how_many_0Formula : SExpr :=
  impliesT (notT (membT aT xT)) (equalT (howManyT aT xT) q0)

/-- NOT-MEMB-IMPLIES-HOW-MANY-IS-0, natively: an absent element has
    `List.count` zero. -/
theorem not_memb_how_many_0_native_of_replayed (w : World)
    (h_memb : w.defs.get? { package := "ACL2", name := "MEMB" }
      = some ([{ package := "ACL2", name := "A" },
               { package := "ACL2", name := "X" }], membBody))
    (h_hm : w.defs.get? how_many_sym = some ([eS, xS], howManyBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (h_no_not : w.defs.get? ({ name := "NOT" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env not_memb_how_many_0Formula = some v ∧ v ≠ SExpr.nil)
    (av : SExpr) (xs : List SExpr) (hmem : xs.contains av = false) :
    xs.count av = 0 := by
  let e : Env := (({} : Env).insert xS (enc xs)).insert aS av
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some av :=
    re_val_var_get w e { name := "A" } av (by
      show e.get? aS = some av
      rw [show e = (({} : Env).insert xS (enc xs)).insert aS av from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = (({} : Env).insert xS (enc xs)).insert aS av from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  -- the antecedent: (memb a x) computes nil (absent), so (not …) is truthy
  have hMemb := corr_memb_enc w h_memb h_no_consp h_no_equal h_no_car
    h_no_cdr xs e aT xT av ha hx
  have hNot := conv_builtin1 w e { name := "NOT" } (membT aT xT)
    (bif xs.contains av then SExpr.t else SExpr.nil)
    (Logic.not (bif xs.contains av then SExpr.t else SExpr.nil))
    (by decide) h_no_not hMemb (callBuiltin_not _)
  -- the count side: (how-many a x) computes the int count; '0 is int 0
  have hHM : ∃ N, ∀ f ≥ N, evalOpt f w e (howManyT aT xT)
      = some (.atom (.number (.int (xs.count av)))) := by
    have h := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
      h_no_cdr h_no_plus e aT xT av (enc xs) ha hx
    rw [howManyExec_enc] at h
    exact h
  have h0 : ∃ N, ∀ f ≥ N, evalOpt f w e q0
      = some (.atom (.number (.int 0))) := re_val_quote w e _
  have hEq := conv_builtin2 w e { name := "EQUAL" } _ _ _ _ _ (by decide)
    h_no_equal hHM h0 (callBuiltin_equal _ _)
  have hImp := conv_builtin2 w e { name := "IMPLIES" } _ _ _ _ _ (by decide)
    h_no_implies hNot hEq (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (replayed_pins_ne_nil (hreplayed e) hImp)
  have hconc := truthy_of_implies_t hIt (by rw [hmem]; rfl)
  have hEqv : SExpr.atom (.number (.int (xs.count av)))
      = SExpr.atom (.number (.int 0)) := by
    refine Logic.eq_of_equal_ne_nil (fun hnil => ?_)
    rw [hnil] at hconc
    exact absurd hconc (by decide)
  have : (xs.count av : Int) = 0 := by
    injection hEqv with h1; injection h1 with h2; injection h2
  omega

/-- The NOT-MEMB-IMPLIES-RM-IS-NO-OP replayed-statement formula (the
    source AND translated to an IF):
    `(IMPLIES (IF (NOT (MEMB A X)) (TRUE-LISTP X) 'NIL)
              (EQUAL (RM A X) X))`. -/
def not_memb_rm_noopFormula : SExpr :=
  impliesT
    (ifT (notT (membT aT xT)) (trueListpT xT) qNil)
    (equalT (rmT aT xT) xT)

/-- NOT-MEMB-IMPLIES-RM-IS-NO-OP, natively: erasing an absent element is
    the identity (`List.erase_of_not_mem` class; the source's true-listp
    hypothesis is intrinsic to the encoding — `trueListp_enc`). -/
theorem not_memb_rm_noop_native_of_replayed (w : World)
    (h_memb : w.defs.get? { package := "ACL2", name := "MEMB" }
      = some ([{ package := "ACL2", name := "A" },
               { package := "ACL2", name := "X" }], membBody))
    (h_rm : w.defs.get? { package := "ACL2", name := "RM" }
      = some ([{ package := "ACL2", name := "E" },
               { package := "ACL2", name := "X" }], rmBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_not : w.defs.get? ({ name := "NOT" } : Symbol) = none)
    (h_no_truelistp : w.defs.get? ({ name := "TRUE-LISTP" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env not_memb_rm_noopFormula = some v ∧ v ≠ SExpr.nil)
    (av : SExpr) (xs : List SExpr) (hmem : xs.contains av = false) :
    xs.erase av = xs := by
  let e : Env := (({} : Env).insert xS (enc xs)).insert aS av
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some av :=
    re_val_var_get w e { name := "A" } av (by
      show e.get? aS = some av
      rw [show e = (({} : Env).insert xS (enc xs)).insert aS av from rfl,
          Env.get?_insert, if_pos (by decide)])
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = (({} : Env).insert xS (enc xs)).insert aS av from rfl,
          Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  -- the antecedent: (not (memb a x)) is truthy (absent) and
  -- (true-listp x) computes t on any encoded list
  have hMemb := corr_memb_enc w h_memb h_no_consp h_no_equal h_no_car
    h_no_cdr xs e aT xT av ha hx
  have hMembNil : ∃ N, ∀ f ≥ N,
      evalOpt f w e (membT aT xT) = some SExpr.nil := by
    simpa only [hmem, cond_false] using hMemb
  have hNot := conv_builtin1 w e { name := "NOT" } (membT aT xT)
    SExpr.nil (Logic.not SExpr.nil) (by decide) h_no_not hMembNil
    (callBuiltin_not _)
  have hTl : ∃ N, ∀ f ≥ N,
      evalOpt f w e (trueListpT xT) = some SExpr.t := by
    have h := conv_builtin1 w e { name := "TRUE-LISTP" } xT (enc xs)
      (Logic.trueListp (enc xs)) (by decide) h_no_truelistp hx rfl
    rwa [trueListp_enc] at h
  have hAnte : ∃ N, ∀ f ≥ N, evalOpt f w e
      (ifT (notT (membT aT xT)) (trueListpT xT) qNil) = some SExpr.t := by
    have h := conv_if_lift w e (notT (membT aT xT)) (trueListpT xT) qNil
      (Logic.not SExpr.nil) SExpr.t SExpr.nil hNot
      (fun _ => hTl) (fun hb => absurd hb (by decide))
    simpa [Logic.not, Logic.toBool] using h
  -- the consequent sides: (rm a x) computes the erase; x itself
  have hRm : ∃ N, ∀ f ≥ N,
      evalOpt f w e (rmT aT xT) = some (enc (xs.erase av)) :=
    corr_rm_enc w h_rm h_no_consp h_no_equal h_no_car h_no_cdr h_no_cons
      xs e aT xT av ha hx
  have hEq := conv_builtin2 w e { name := "EQUAL" } _ _ _ _ _ (by decide)
    h_no_equal hRm hx (callBuiltin_equal _ _)
  have hImp := conv_builtin2 w e { name := "IMPLIES" } _ _ _ _ _ (by decide)
    h_no_implies hAnte hEq (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (replayed_pins_ne_nil (hreplayed e) hImp)
  have hconc := truthy_of_implies_t hIt rfl
  have hEqv : enc (xs.erase av) = enc xs := by
    refine Logic.eq_of_equal_ne_nil (fun hnil => ?_)
    rw [hnil] at hconc
    exact absurd hconc (by decide)
  exact enc_inj hEqv

/-- The HOW-MANY-RM replayed-statement formula:
    `(IMPLIES (NOT (EQUAL A B)) (EQUAL (HOW-MANY A (RM B X)) (HOW-MANY A X)))`. -/
def how_many_rmFormula : SExpr :=
  impliesT (notT (equalT aT bT))
    (equalT (howManyT aT (rmT bT xT)) (howManyT aT xT))

/-- HOW-MANY-RM, natively: erasing a DIFFERENT element preserves the
    count (the count-of-erase class). -/
theorem how_many_rm_native_of_replayed (w : World)
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
    (h_no_not : w.defs.get? ({ name := "NOT" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env how_many_rmFormula = some v ∧ v ≠ SExpr.nil)
    (av bv : SExpr) (xs : List SExpr) (h : (av == bv) = false) :
    (xs.erase bv).count av = xs.count av := by
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
  -- the antecedent: (not (equal a b)) is truthy on distinct values
  have hEqAB := conv_equalT w e aT bT av bv h_no_equal ha hb
  have hNe : Logic.equal av bv = SExpr.nil := by simp [Logic.equal, h]
  have hNot := conv_builtin1 w e { name := "NOT" } (equalT aT bT)
    (Logic.equal av bv) (Logic.not (Logic.equal av bv)) (by decide)
    h_no_not hEqAB (callBuiltin_not _)
  -- the two count sides
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
  have hR : ∃ N, ∀ f ≥ N, evalOpt f w e (howManyT aT xT)
      = some (.atom (.number (.int (xs.count av)))) := by
    have hcorr := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
      h_no_cdr h_no_plus e aT xT av (enc xs) ha hx
    rw [howManyExec_enc] at hcorr
    exact hcorr
  have hEq := conv_builtin2 w e { name := "EQUAL" } _ _ _ _ _ (by decide)
    h_no_equal hL hR (callBuiltin_equal _ _)
  have hImp := conv_builtin2 w e { name := "IMPLIES" } _ _ _ _ _ (by decide)
    h_no_implies hNot hEq (callBuiltin_implies _ _)
  have hIt := implies_t_of_ne_nil (replayed_pins_ne_nil (hreplayed e) hImp)
  have hconc := truthy_of_implies_t hIt (by rw [hNe]; rfl)
  have hEqv : SExpr.atom (.number (.int ((xs.erase bv).count av)))
      = SExpr.atom (.number (.int (xs.count av))) := by
    refine Logic.eq_of_equal_ne_nil (fun hnil => ?_)
    rw [hnil] at hconc
    exact absurd hconc (by decide)
  have : ((xs.erase bv).count av : Int) = (xs.count av : Int) := by
    injection hEqv with h1; injection h1 with h2; injection h2
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

/-- `rel`'s body as a total Lean function (non-recursive dispatch). -/
derive_exec% relExec corr rel_exec_corr for rel_sym
  formals [fnS, iS, jS] body relBody

theorem relExec_t_or_nil (f i j : SExpr) :
    relExec f i j = SExpr.t ∨ relExec f i j = SExpr.nil := by
  unfold relExec
  repeat' split
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exact lexorder_t_or_nil _ _

/-- `all-rel`'s body as a total Lean function. -/
derive_exec% allRelExec corr all_rel_exec_corr for all_rel_sym
  formals [fnS, xS, eS] body allRelBody measured 1

/-- The NATIVE reading of one REL verdict — an ordinary Lean match on the
    four comparison modes, in `lexorderB`/`==` vocabulary only (the mirror
    criterion: no exec function in a mirror statement). -/
def relL (fv a e : SExpr) : Bool :=
  if fv == symV "LT" then lexorderB a e && !(a == e)
  else if fv == symV "LTE" then lexorderB a e
  else if fv == symV "GT" then lexorderB e a && !(a == e)
  else lexorderB e a

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

/-- `allRelExec` is two-valued. -/
theorem allRelExec_t_or_nil (fv x ev : SExpr) :
    allRelExec fv x ev = SExpr.t ∨ allRelExec fv x ev = SExpr.nil := by
  fun_induction allRelExec fv x ev with
  | case1 x _ _ ih => exact ih
  | case2 x _ _ => exact Or.inr rfl
  | case3 x _ => exact Or.inl rfl

/-- `tp:ALL-REL` — the emitted boolean corollary; wrapper GENERATED (1c). -/
derive_exec_tp% dis_all_rel_tp for "ALL-REL"
  (v => (bif Logic.toBool (Logic.equal v SExpr.t) then SExpr.t
     else Logic.equal v SExpr.nil) = SExpr.t)
  ending
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

/-- `filter`'s body as a total Lean function. -/
derive_exec% filterExec corr filter_exec_corr for filter_sym
  formals [fnS, xS, eS] body filterBody measured 1

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

/-! ## ORDEREDP-APPEND -/

private def append_sym : Symbol := { package := "ACL2", name := "BINARY-APPEND" }

private theorem append_ns :
    (append_sym.isNamed "QUOTE" = false ∧ append_sym.isNamed "IF" = false ∧
     append_sym.isNamed "LET" = false ∧
     append_sym.isNamed "LET*" = false) := by decide

private theorem bindArgs_xy_x' (vx vy : SExpr) :
    (bindArgs [xS, yS] [vx, vy]).get? xS = some vx := by
  show ((({} : Env).insert yS vy).insert xS vx).get? xS = some vx
  rw [Env.get?_insert, if_pos (by decide)]
private theorem bindArgs_xy_y' (vx vy : SExpr) :
    (bindArgs [xS, yS] [vx, vy]).get? yS = some vy := by
  show ((({} : Env).insert yS vy).insert xS vx).get? yS = some vy
  rw [Env.get?_insert, if_neg (by decide), Env.get?_insert,
      if_pos (by decide)]

/-- `binary-append`'s body as a total Lean function (over ARBITRARY
    values — the enc-only `corr_append_enc` cannot serve the args-valued
    TP hypothesis). -/
def appendExec (x y : SExpr) : SExpr :=
  if Logic.toBool (Logic.consp x) = true then
    Logic.cons (Logic.car x) (appendExec (Logic.cdr x) y)
  else y
termination_by x.consCount
decreasing_by exact consCount_cdr_lt_of_consp (by assumption)

/-- Stage 1: a `binary-append` call converges to `appendExec`. -/
theorem append_exec_corr (w : World)
    (h_app : w.defs.get? append_sym
      = some ([{ package := "ACL2", name := "X" },
               { package := "ACL2", name := "Y" }],
              appendBody "BINARY-APPEND"))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none) :
    ∀ (env : Env) (a b av bv : SExpr),
      ConvTo w env a av → ConvTo w env b bv →
      ConvTo w env (appendT a b) (appendExec av bv) := by
  have hbody : ∀ xv yv : SExpr,
      ConvTo w (bindArgs [xS, yS] [xv, yv]) (appendBody "BINARY-APPEND")
        (appendExec xv yv) := by
    refine consCount_strong_induction
      (fun xv => ∀ yv, ConvTo w (bindArgs [xS, yS] [xv, yv])
        (appendBody "BINARY-APPEND") (appendExec xv yv)) ?_
    intro xv ih yv
    have hxv := re_val_var_get w (bindArgs [xS, yS] [xv, yv])
      { name := "X" } xv (bindArgs_xy_x' xv yv)
    have hyv := re_val_var_get w (bindArgs [xS, yS] [xv, yv])
      { name := "Y" } yv (bindArgs_xy_y' xv yv)
    have hconsp := conv_builtin1 w _ { name := "CONSP" } xT xv
      (Logic.consp xv) (by decide) h_no_consp hxv (callBuiltin_consp _)
    have hcar := conv_builtin1 w _ { name := "CAR" } xT xv
      (Logic.car xv) (by decide) h_no_car hxv (callBuiltin_car _)
    have hcdr := conv_builtin1 w _ { name := "CDR" } xT xv
      (Logic.cdr xv) (by decide) h_no_cdr hxv (callBuiltin_cdr _)
    have houter := conv_if_lift w (bindArgs [xS, yS] [xv, yv]) (conspT xT)
      (consT (carT xT) (appendT (cdrT xT) yT)) yT (Logic.consp xv)
      (Logic.cons (Logic.car xv) (appendExec (Logic.cdr xv) yv)) yv hconsp
      (fun hb =>
        conv_builtin2 w _ { name := "CONS" } (carT xT)
          (appendT (cdrT xT) yT) (Logic.car xv)
          (appendExec (Logic.cdr xv) yv) _ (by decide) h_no_cons hcar
          (conv_defn_2 w _ append_sym (cdrT xT) yT (Logic.cdr xv) yv
            xS yS (appendBody "BINARY-APPEND") _ append_ns h_app hcdr hyv
            (ih (Logic.cdr xv) (consCount_cdr_lt_of_consp hb) yv))
          rfl)
      (fun _ => hyv)
    rw [appendExec.eq_def]
    exact houter
  intro env a b av bv ha hb
  exact conv_defn_2 w env append_sym a b av bv xS yS
    (appendBody "BINARY-APPEND") _ append_ns h_app ha hb (hbody av bv)

/-- `appendExec` is a cons or its second argument — the emitted TP
    corollary's content. -/
theorem appendExec_consp_or_eq (x y : SExpr) :
    Logic.consp (appendExec x y) = SExpr.t ∨ appendExec x y = y := by
  fun_induction appendExec x y with
  | case1 x _ _ => exact Or.inl rfl
  | case2 x _ => exact Or.inr rfl

/-- `tp:BINARY-APPEND`, world-parametric — the args-valued TP hypothesis
    (`(IF (CONSP (BINARY-APPEND X Y)) 'T (EQUAL (BINARY-APPEND X Y) Y))`). -/
theorem dis_append_tp (w : World)
    (h_app : w.defs.get? append_sym
      = some ([{ package := "ACL2", name := "X" },
               { package := "ACL2", name := "Y" }],
              appendBody "BINARY-APPEND"))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (e' : Env) (a0 a1 u0 u1 v : SExpr)
    (h0 : ∃ N, ∀ f ≥ N, evalOpt f w e' a0 = some u0)
    (h1 : ∃ N, ∀ f ≥ N, evalOpt f w e' a1 = some u1)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e' (appendT a0 a1) = some v) :
    (bif Logic.toBool (Logic.consp v) then SExpr.t else Logic.equal v u1)
      = SExpr.t := by
  have happ := append_exec_corr w h_app h_no_consp h_no_car h_no_cdr
    h_no_cons e' a0 a1 u0 u1 h0 h1
  rw [val_unique h happ]
  rcases appendExec_consp_or_eq u0 u1 with ht | heq
  · rw [ht]; rfl
  · rw [heq]
    cases hb : Logic.toBool (Logic.consp u1) with
    | true => rfl
    | false => simp [Logic.equal]

abbrev iffT (a b : SExpr) : SExpr := app2 "IFF" a b

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

/-! ## The msort book: `merge2` / `evens` / `odds` / `msort` exec kit -/

abbrev merge2T (x y : SExpr) : SExpr := app2 "MERGE2" x y
abbrev evensT (x : SExpr) : SExpr := app1 "EVENS" x
abbrev oddsT (x : SExpr) : SExpr := app1 "ODDS" x
abbrev msortT (x : SExpr) : SExpr := app1 "MSORT" x

private def lS : Symbol := { package := "ACL2", name := "L" }
private def lT : SExpr := .atom (.symbol { name := "L" })

/-- `(defun merge2 (x y) …)`, macroexpanded. -/
def merge2Body : SExpr :=
  ifT (conspT xT)
    (ifT (conspT yT)
      (ifT (lexT (carT xT) (carT yT))
        (consT (carT xT) (merge2T (cdrT xT) yT))
        (consT (carT yT) (merge2T xT (cdrT yT))))
      xT)
    yT

/-- `(defun evens (l) …)`, macroexpanded. -/
def evensBody : SExpr :=
  ifT (conspT lT) (consT (carT lT) (evensT (cdrT (cdrT lT)))) qNil

/-- `(defun odds (l) …)` — `(EVENS (CDR L))`. -/
def oddsBody : SExpr := evensT (cdrT lT)

/-- `(defun msort (x) …)`, macroexpanded. -/
def msortBody : SExpr :=
  ifT (conspT xT)
    (ifT (conspT (cdrT xT))
      (merge2T (msortT (evensT xT)) (msortT (oddsT xT)))
      (consT (carT xT) qNil))
    qNil

private def merge2_sym : Symbol := { package := "ACL2", name := "MERGE2" }
private def evens_sym : Symbol := { package := "ACL2", name := "EVENS" }
private def odds_sym : Symbol := { package := "ACL2", name := "ODDS" }
private def msort_sym : Symbol := { package := "ACL2", name := "MSORT" }

private theorem odds_ns :
    (odds_sym.isNamed "QUOTE" = false ∧ odds_sym.isNamed "IF" = false ∧
     odds_sym.isNamed "LET" = false ∧
     odds_sym.isNamed "LET*" = false) := by decide
private theorem msort_ns :
    (msort_sym.isNamed "QUOTE" = false ∧ msort_sym.isNamed "IF" = false ∧
     msort_sym.isNamed "LET" = false ∧
     msort_sym.isNamed "LET*" = false) := by decide

private theorem bindArgs_l_l (v : SExpr) :
    (bindArgs [lS] [v]).get? lS = some v :=
  bindArgs_single_get_self lS v

/-- `merge2`'s body as a total Lean function — GENERATED (M2: the emitted
    pair-sum measure `(+ (ACL2-COUNT X) (ACL2-COUNT Y))`; per-site
    single-CDR one-side decreases; corr by Nat strong induction over the
    sum). -/
derive_exec% merge2Exec corr merge2_exec_corr for merge2_sym
  formals [xS, yS] body merge2Body measured 0 1

/-- The native merge: Lean's ordinary two-list merge by `lexorderB`. -/
def merge2L : List SExpr → List SExpr → List SExpr
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | a :: xs, b :: ys =>
    bif lexorderB a b then a :: merge2L xs (b :: ys)
    else b :: merge2L (a :: xs) ys
termination_by xs ys => xs.length + ys.length

/-- Stage 2: `merge2Exec` on encoded lists computes `merge2L`. -/
theorem merge2Exec_enc : ∀ (xs ys : List SExpr),
    merge2Exec (enc xs) (enc ys) = enc (merge2L xs ys)
  | [], ys => by
    rw [merge2Exec.eq_def, show enc ([] : List SExpr) = SExpr.nil from rfl,
        if_neg (by simp [Logic.consp, Logic.toBool])]
    simp [merge2L]
  | x :: xs, [] => by
    rw [merge2Exec.eq_def,
        if_pos (show Logic.toBool (Logic.consp (enc (x :: xs))) = true
          from rfl),
        show enc ([] : List SExpr) = SExpr.nil from rfl,
        if_neg (by simp [Logic.consp, Logic.toBool])]
    simp [merge2L]
  | a :: xs, b :: ys => by
    rw [merge2Exec.eq_def,
        if_pos (show Logic.toBool (Logic.consp (enc (a :: xs))) = true
          from rfl),
        if_pos (show Logic.toBool (Logic.consp (enc (b :: ys))) = true
          from rfl),
        show Logic.car (enc (a :: xs)) = a from rfl,
        show Logic.car (enc (b :: ys)) = b from rfl,
        show Logic.cdr (enc (a :: xs)) = enc xs from rfl,
        show Logic.cdr (enc (b :: ys)) = enc ys from rfl,
        toBool_lexorder]
    cases hb : lexorderB a b with
    | true =>
      rw [if_pos rfl, merge2Exec_enc xs (b :: ys)]
      simp only [merge2L, hb, cond_true]
      rfl
    | false =>
      rw [if_neg (by simp), merge2Exec_enc (a :: xs) ys]
      simp only [merge2L, hb, cond_false]
      rfl
termination_by xs ys => xs.length + ys.length

/-- `evens`'s body as a total Lean function. -/
derive_exec% evensExec corr evens_exec_corr for evens_sym
  formals [lS] body evensBody measured 0

/-- The native evens: every other element, starting at the head. -/
def evensL : List SExpr → List SExpr
  | [] => []
  | a :: t => a :: evensL t.tail
termination_by l => l.length
decreasing_by
  cases t with
  | nil => simp
  | cons b t' => simp

/-- Stage 2: `evensExec` on an encoded list computes `evensL`. -/
theorem evensExec_enc : ∀ xs : List SExpr,
    evensExec (enc xs) = enc (evensL xs)
  | [] => by
    rw [evensExec.eq_def, show enc ([] : List SExpr) = SExpr.nil from rfl,
        if_neg (by simp [Logic.consp, Logic.toBool])]
    simp [evensL, enc]
  | a :: t => by
    rw [evensExec.eq_def,
        if_pos (show Logic.toBool (Logic.consp (enc (a :: t))) = true
          from rfl),
        show Logic.car (enc (a :: t)) = a from rfl,
        show Logic.cdr (enc (a :: t)) = enc t from rfl,
        show Logic.cdr (enc t) = enc t.tail from by cases t <;> rfl,
        evensExec_enc t.tail,
        show evensL (a :: t) = a :: evensL t.tail from by simp [evensL]]
    rfl
termination_by xs => xs.length
decreasing_by
  cases t with
  | nil => simp
  | cons b t' => simp

/-- `evensExec` never increases the count. -/
theorem evensExec_consCount_le (l : SExpr) :
    (evensExec l).consCount ≤ l.consCount := by
  fun_induction evensExec l with
  | case1 l hb ih =>
    cases l with
    | nil => simp [Logic.consp, Logic.toBool] at hb
    | atom _ => simp [Logic.consp, Logic.toBool] at hb
    | cons a d =>
      have hle : (Logic.cdr (Logic.cdr (SExpr.cons a d))).consCount
          ≤ d.consCount := by
        calc (Logic.cdr (Logic.cdr (SExpr.cons a d))).consCount
            = (Logic.cdr d).consCount := rfl
          _ ≤ d.consCount := consCount_cdr_le _
      simp only [Logic.cons, Logic.car, consCount_cons]
      omega
  | case2 l _ => simp

/-- `evensExec` strictly decreases the count on a two-or-more list. -/
theorem evensExec_consCount_lt {l : SExpr}
    (h1 : Logic.toBool (Logic.consp l) = true)
    (h2 : Logic.toBool (Logic.consp (Logic.cdr l)) = true) :
    (evensExec l).consCount < l.consCount := by
  cases l with
  | nil => simp [Logic.consp, Logic.toBool] at h1
  | atom _ => simp [Logic.consp, Logic.toBool] at h1
  | cons a d =>
    cases d with
    | nil => simp [Logic.cdr, Logic.consp, Logic.toBool] at h2
    | atom _ => simp [Logic.cdr, Logic.consp, Logic.toBool] at h2
    | cons b d' =>
      rw [evensExec.eq_def, if_pos h1,
          show Logic.cdr (Logic.cdr (SExpr.cons a (SExpr.cons b d'))) = d'
            from rfl,
          show Logic.car (SExpr.cons a (SExpr.cons b d')) = a from rfl]
      have hle := evensExec_consCount_le d'
      simp only [Logic.cons, consCount_cons]
      omega

/-- `msort`'s body as a total Lean function. -/
def msortExec (x : SExpr) : SExpr :=
  if _h1 : Logic.toBool (Logic.consp x) = true then
    if _h2 : Logic.toBool (Logic.consp (Logic.cdr x)) = true then
      merge2Exec (msortExec (evensExec x))
        (msortExec (evensExec (Logic.cdr x)))
    else Logic.cons (Logic.car x) SExpr.nil
  else SExpr.nil
termination_by x.consCount
decreasing_by
  · exact evensExec_consCount_lt _h1 _h2
  · calc (evensExec (Logic.cdr x)).consCount
        ≤ (Logic.cdr x).consCount := evensExec_consCount_le _
      _ < x.consCount := consCount_cdr_lt_of_consp _h1

/-- Stage 1: an `msort` call converges to `msortExec`. -/
theorem msort_exec_corr (w : World)
    (h_m2 : w.defs.get? merge2_sym = some ([xS, yS], merge2Body))
    (h_evens : w.defs.get? evens_sym = some ([lS], evensBody))
    (h_odds : w.defs.get? odds_sym = some ([lS], oddsBody))
    (h_msort : w.defs.get? msort_sym = some ([xS], msortBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none) :
    ∀ (env : Env) (x xv : SExpr),
      ConvTo w env x xv → ConvTo w env (msortT x) (msortExec xv) := by
  have hbody : ∀ xv : SExpr,
      ConvTo w (bindArgs [xS] [xv]) msortBody (msortExec xv) := by
    refine consCount_strong_induction
      (fun xv => ConvTo w (bindArgs [xS] [xv]) msortBody (msortExec xv)) ?_
    intro xv ih
    have hxv := re_val_var_get w (bindArgs [xS] [xv]) { name := "X" } xv
      (bindArgs_single_get_self xS xv)
    have hconsp := conv_builtin1 w _ { name := "CONSP" } xT xv
      (Logic.consp xv) (by decide) h_no_consp hxv (callBuiltin_consp _)
    have hcar := conv_builtin1 w _ { name := "CAR" } xT xv
      (Logic.car xv) (by decide) h_no_car hxv (callBuiltin_car _)
    have hcdr := conv_builtin1 w _ { name := "CDR" } xT xv
      (Logic.cdr xv) (by decide) h_no_cdr hxv (callBuiltin_cdr _)
    have hconsp2 := conv_builtin1 w _ { name := "CONSP" } (cdrT xT)
      (Logic.cdr xv) (Logic.consp (Logic.cdr xv)) (by decide) h_no_consp
      hcdr (callBuiltin_consp _)
    -- the two-element-plus branch, conditional on BOTH consp verdicts
    have hbig : Logic.toBool (Logic.consp xv) = true →
        Logic.toBool (Logic.consp (Logic.cdr xv)) = true →
        ConvTo w (bindArgs [xS] [xv])
          (merge2T (msortT (evensT xT)) (msortT (oddsT xT)))
          (merge2Exec (msortExec (evensExec xv))
            (msortExec (evensExec (Logic.cdr xv)))) := by
      intro hb1 hb2
      have hevens := evens_exec_corr w h_evens h_no_consp h_no_car
        h_no_cdr h_no_cons _ xT xv hxv
      have hodds : ConvTo w (bindArgs [xS] [xv]) (oddsT xT)
          (evensExec (Logic.cdr xv)) := by
        refine conv_defn_1 w _ odds_sym xT xv lS oddsBody _
          odds_ns h_odds hxv ?_
        -- odds' body walk: (EVENS (CDR L)) at l ↦ xv
        have hl := re_val_var_get w (bindArgs [lS] [xv]) { name := "L" }
          xv (bindArgs_l_l xv)
        have hcdrl := conv_builtin1 w _ { name := "CDR" } lT xv
          (Logic.cdr xv) (by decide) h_no_cdr hl (callBuiltin_cdr _)
        exact evens_exec_corr w h_evens h_no_consp h_no_car h_no_cdr
          h_no_cons _ (cdrT lT) (Logic.cdr xv) hcdrl
      have hmsE := conv_defn_1 w _ msort_sym (evensT xT) (evensExec xv)
        xS msortBody _ msort_ns h_msort hevens
        (ih (evensExec xv) (evensExec_consCount_lt hb1 hb2))
      have hmsO := conv_defn_1 w _ msort_sym (oddsT xT)
        (evensExec (Logic.cdr xv)) xS msortBody _ msort_ns h_msort hodds
        (ih (evensExec (Logic.cdr xv))
          (lt_of_le_of_lt (evensExec_consCount_le _)
            (consCount_cdr_lt_of_consp hb1)))
      exact merge2_exec_corr w h_m2 h_no_consp h_no_car h_no_cdr h_no_cons
        h_no_lexorder _ (msortT (evensT xT)) (msortT (oddsT xT))
        (msortExec (evensExec xv)) (msortExec (evensExec (Logic.cdr xv)))
        hmsE hmsO
    have houter := conv_if_lift w (bindArgs [xS] [xv]) (conspT xT)
      (ifT (conspT (cdrT xT))
        (merge2T (msortT (evensT xT)) (msortT (oddsT xT)))
        (consT (carT xT) qNil))
      qNil (Logic.consp xv)
      (if Logic.toBool (Logic.consp (Logic.cdr xv)) = true then
        merge2Exec (msortExec (evensExec xv))
          (msortExec (evensExec (Logic.cdr xv)))
       else Logic.cons (Logic.car xv) SExpr.nil)
      SExpr.nil hconsp
      (fun hb1 =>
        conv_if_lift w _ (conspT (cdrT xT))
          (merge2T (msortT (evensT xT)) (msortT (oddsT xT)))
          (consT (carT xT) qNil) (Logic.consp (Logic.cdr xv))
          (merge2Exec (msortExec (evensExec xv))
            (msortExec (evensExec (Logic.cdr xv))))
          (Logic.cons (Logic.car xv) SExpr.nil) hconsp2
          (fun hb2 => hbig hb1 hb2)
          (fun _ =>
            conv_builtin2 w _ { name := "CONS" } (carT xT) qNil
              (Logic.car xv) SExpr.nil _ (by decide) h_no_cons hcar
              (re_val_quote w _ SExpr.nil) rfl))
      (fun _ => re_val_quote w _ SExpr.nil)
    rw [msortExec.eq_def]
    -- the exec's dite matches the walk's ite branch values
    simp only [dite_eq_ite] at *
    exact houter
  intro env x xv hx
  exact conv_defn_1 w env msort_sym x xv xS msortBody _
    msort_ns h_msort hx (hbody xv)

/-- The evens split halves the length (rounding up). -/
theorem evensL_length : ∀ l : List SExpr,
    (evensL l).length = (l.length + 1) / 2
  | [] => by simp [evensL]
  | [_] => by simp [evensL]
  | _ :: _ :: t => by
    have := evensL_length t
    simp only [evensL, List.tail_cons, List.length_cons, this]
    omega
termination_by l => l.length

/-- The native merge sort. -/
def msortL (xs : List SExpr) : List SExpr :=
  match xs with
  | [] => []
  | [a] => [a]
  | a :: b :: t =>
    merge2L (msortL (evensL (a :: b :: t))) (msortL (evensL (b :: t)))
termination_by xs.length
decreasing_by
  · rw [evensL_length]; simp; omega
  · rw [evensL_length]; simp; omega

/-- Stage 2: `msortExec` on an encoded list computes `msortL`. -/
theorem msortExec_enc : ∀ xs : List SExpr,
    msortExec (enc xs) = enc (msortL xs)
  | [] => by
    rw [msortExec.eq_def, show enc ([] : List SExpr) = SExpr.nil from rfl,
        dif_neg (by simp [Logic.consp, Logic.toBool])]
    simp [msortL, enc]
  | [a] => by
    rw [msortExec.eq_def,
        dif_pos (show Logic.toBool (Logic.consp (enc [a])) = true from rfl),
        dif_neg (show ¬(Logic.toBool (Logic.consp
          (Logic.cdr (enc [a]))) = true) from by
            simp [enc, Logic.cdr, Logic.consp, Logic.toBool]),
        show Logic.car (enc [a]) = a from rfl]
    simp [msortL, Logic.cons, enc]
  | a :: b :: t => by
    rw [msortExec.eq_def,
        dif_pos (show Logic.toBool (Logic.consp (enc (a :: b :: t)))
          = true from rfl),
        dif_pos (show Logic.toBool (Logic.consp
          (Logic.cdr (enc (a :: b :: t)))) = true from rfl),
        show Logic.cdr (enc (a :: b :: t)) = enc (b :: t) from rfl,
        evensExec_enc (a :: b :: t), evensExec_enc (b :: t),
        msortExec_enc (evensL (a :: b :: t)), msortExec_enc (evensL (b :: t)),
        merge2Exec_enc]
    simp [msortL]
termination_by xs => xs.length
decreasing_by
  · rw [evensL_length]; simp; omega
  · rw [evensL_length]; simp; omega

/-! ## The msort dischargers -/

/-- `total:MERGE2` — GENERATED (1c). -/
derive_exec_total% dis_merge2_total for "MERGE2"

/-- `total:MSORT` — the driver-shape totality statement. -/
theorem dis_msort_total (w : World)
    (h_m2 : w.defs.get? merge2_sym = some ([xS, yS], merge2Body))
    (h_evens : w.defs.get? evens_sym = some ([lS], evensBody))
    (h_odds : w.defs.get? odds_sym = some ([lS], oddsBody))
    (h_msort : w.defs.get? msort_sym = some ([xS], msortBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none) :
    ∀ (env' : Env) (a0 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' (msortT a0) = some v := by
  intro env' a0 ⟨N0, v0, h0⟩
  obtain ⟨N, h⟩ := msort_exec_corr w h_m2 h_evens h_odds h_msort h_no_consp
    h_no_car h_no_cdr h_no_cons h_no_lexorder env' a0 v0 ⟨N0, h0⟩
  exact ⟨N, msortExec v0, h⟩

/-- `evensExec` always yields a true-list. -/
theorem evensExec_trueListp (l : SExpr) :
    Logic.trueListp (evensExec l) = SExpr.t := by
  fun_induction evensExec l with
  | case1 l _ ih => simpa [Logic.cons, Logic.trueListp] using ih
  | case2 l _ => rfl

/-- `tp:EVENS` — the emitted `(TRUE-LISTP (EVENS L))` corollary; wrapper
    GENERATED (1c). -/
derive_exec_tp% dis_evens_tp for "EVENS"
  (v => Logic.trueListp v = SExpr.t)
  ending exact evensExec_trueListp u0

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

/-! ## The ordinal kit (`total:O<`): O-FINP / O-FIRST-EXPT /
O-FIRST-COEFF / O-RST / O< — the ground-zero ordinal fns the qsort
admissions cite. -/

abbrev oFinpT (x : SExpr) : SExpr := app1 "O-FINP" x
abbrev oFirstExptT (x : SExpr) : SExpr := app1 "O-FIRST-EXPT" x
abbrev oFirstCoeffT (x : SExpr) : SExpr := app1 "O-FIRST-COEFF" x
abbrev oRstT (x : SExpr) : SExpr := app1 "O-RST" x
abbrev oLtT (x y : SExpr) : SExpr := app2 "O<" x y
private abbrev ltT (a b : SExpr) : SExpr := app2 "<" a b

def oFinpBody : SExpr := ifT (conspT xT) qNil qT'
def oFirstExptBody : SExpr := ifT (oFinpT xT) q0 (carT (carT xT))
def oFirstCoeffBody : SExpr := ifT (oFinpT xT) xT (cdrT (carT xT))
def oRstBody : SExpr := cdrT xT
def oLtBody : SExpr :=
  ifT (oFinpT xT)
    (ifT (oFinpT yT) (ltT xT yT) qT')
    (ifT (oFinpT yT) qNil
      (ifT (equalT (oFirstExptT xT) (oFirstExptT yT))
        (ifT (equalT (oFirstCoeffT xT) (oFirstCoeffT yT))
          (oLtT (oRstT xT) (oRstT yT))
          (ltT (oFirstCoeffT xT) (oFirstCoeffT yT)))
        (oLtT (oFirstExptT xT) (oFirstExptT yT))))

private def o_finp_sym : Symbol := { package := "ACL2", name := "O-FINP" }
private def o_fe_sym : Symbol := { package := "ACL2", name := "O-FIRST-EXPT" }
private def o_fc_sym : Symbol :=
  { package := "ACL2", name := "O-FIRST-COEFF" }
private def o_rst_sym : Symbol := { package := "ACL2", name := "O-RST" }
private def o_lt_sym : Symbol := { package := "ACL2", name := "O<" }

private theorem o_finp_ns :
    (o_finp_sym.isNamed "QUOTE" = false ∧ o_finp_sym.isNamed "IF" = false ∧
     o_finp_sym.isNamed "LET" = false ∧
     o_finp_sym.isNamed "LET*" = false) := by decide
private theorem o_fe_ns :
    (o_fe_sym.isNamed "QUOTE" = false ∧ o_fe_sym.isNamed "IF" = false ∧
     o_fe_sym.isNamed "LET" = false ∧
     o_fe_sym.isNamed "LET*" = false) := by decide
private theorem o_fc_ns :
    (o_fc_sym.isNamed "QUOTE" = false ∧ o_fc_sym.isNamed "IF" = false ∧
     o_fc_sym.isNamed "LET" = false ∧
     o_fc_sym.isNamed "LET*" = false) := by decide
private theorem o_rst_ns :
    (o_rst_sym.isNamed "QUOTE" = false ∧ o_rst_sym.isNamed "IF" = false ∧
     o_rst_sym.isNamed "LET" = false ∧
     o_rst_sym.isNamed "LET*" = false) := by decide
private theorem o_lt_ns :
    (o_lt_sym.isNamed "QUOTE" = false ∧ o_lt_sym.isNamed "IF" = false ∧
     o_lt_sym.isNamed "LET" = false ∧
     o_lt_sym.isNamed "LET*" = false) := by decide

def oFinpExec (x : SExpr) : SExpr :=
  if Logic.toBool (Logic.consp x) = true then SExpr.nil else SExpr.t

def oFirstExptExec (x : SExpr) : SExpr :=
  if Logic.toBool (oFinpExec x) = true then .atom (.number (.int 0))
  else Logic.car (Logic.car x)

def oFirstCoeffExec (x : SExpr) : SExpr :=
  if Logic.toBool (oFinpExec x) = true then x
  else Logic.cdr (Logic.car x)

/-- `oFinpExec x` is false exactly on conses. -/
private theorem oFinpExec_false_consp {x : SExpr}
    (h : Logic.toBool (oFinpExec x) = false) :
    Logic.toBool (Logic.consp x) = true := by
  unfold oFinpExec at h
  by_cases hc : Logic.toBool (Logic.consp x) = true
  · exact hc
  · rw [if_neg hc] at h; exact absurd h (by decide)

private theorem oFirstExptExec_consCount_lt {x : SExpr}
    (h : Logic.toBool (oFinpExec x) = false) :
    (oFirstExptExec x).consCount < x.consCount := by
  rw [oFirstExptExec, if_neg (by rw [h]; decide)]
  exact lt_of_le_of_lt (consCount_car_le _)
    (consCount_car_lt_of_consp (oFinpExec_false_consp h))

def oLtExec (x y : SExpr) : SExpr :=
  if _h1 : Logic.toBool (oFinpExec x) = true then
    (if Logic.toBool (oFinpExec y) = true then Logic.lt x y else SExpr.t)
  else if Logic.toBool (oFinpExec y) = true then SExpr.nil
  else if Logic.toBool (Logic.equal (oFirstExptExec x) (oFirstExptExec y))
      = true then
    (if Logic.toBool (Logic.equal (oFirstCoeffExec x) (oFirstCoeffExec y))
        = true then
      oLtExec (Logic.cdr x) (Logic.cdr y)
     else Logic.lt (oFirstCoeffExec x) (oFirstCoeffExec y))
  else oLtExec (oFirstExptExec x) (oFirstExptExec y)
termination_by x.consCount
decreasing_by
  · exact consCount_cdr_lt_of_consp (oFinpExec_false_consp
      (Bool.not_eq_true _ ▸ eq_false_of_ne_true _h1))
  · exact oFirstExptExec_consCount_lt
      (Bool.not_eq_true _ ▸ eq_false_of_ne_true _h1)

/-- Stage 1 for the small ordinal fns (non-recursive walks). -/
theorem o_finp_exec_corr (w : World)
    (h_fn : w.defs.get? o_finp_sym = some ([xS], oFinpBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none) :
    ∀ (env : Env) (x xv : SExpr),
      ConvTo w env x xv → ConvTo w env (oFinpT x) (oFinpExec xv) := by
  intro env x xv hx
  refine conv_defn_1 w env o_finp_sym x xv xS oFinpBody _
    o_finp_ns h_fn hx ?_
  have hxv := re_val_var_get w (bindArgs [xS] [xv]) { name := "X" } xv
    (bindArgs_single_get_self xS xv)
  have hconsp := conv_builtin1 w _ { name := "CONSP" } xT xv
    (Logic.consp xv) (by decide) h_no_consp hxv (callBuiltin_consp _)
  have h := conv_if_lift w (bindArgs [xS] [xv]) (conspT xT) qNil qT'
    (Logic.consp xv) SExpr.nil SExpr.t hconsp
    (fun _ => re_val_quote w _ SExpr.nil)
    (fun _ => re_val_quote w _ SExpr.t)
  rw [oFinpExec]
  exact h

theorem o_fe_exec_corr (w : World)
    (h_fn : w.defs.get? o_fe_sym = some ([xS], oFirstExptBody))
    (h_finp : w.defs.get? o_finp_sym = some ([xS], oFinpBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none) :
    ∀ (env : Env) (x xv : SExpr),
      ConvTo w env x xv → ConvTo w env (oFirstExptT x) (oFirstExptExec xv)
    := by
  intro env x xv hx
  refine conv_defn_1 w env o_fe_sym x xv xS oFirstExptBody _
    o_fe_ns h_fn hx ?_
  have hxv := re_val_var_get w (bindArgs [xS] [xv]) { name := "X" } xv
    (bindArgs_single_get_self xS xv)
  have hfinp := o_finp_exec_corr w h_finp h_no_consp _ xT xv hxv
  have hcar := conv_builtin1 w _ { name := "CAR" } xT xv
    (Logic.car xv) (by decide) h_no_car hxv (callBuiltin_car _)
  have hcarcar := conv_builtin1 w _ { name := "CAR" } (carT xT)
    (Logic.car xv) (Logic.car (Logic.car xv)) (by decide) h_no_car hcar
    (callBuiltin_car _)
  have h := conv_if_lift w (bindArgs [xS] [xv]) (oFinpT xT) q0
    (carT (carT xT)) (oFinpExec xv) (.atom (.number (.int 0)))
    (Logic.car (Logic.car xv)) hfinp
    (fun _ => re_val_quote w _ (.atom (.number (.int 0))))
    (fun _ => hcarcar)
  rw [oFirstExptExec]
  exact h

theorem o_fc_exec_corr (w : World)
    (h_fn : w.defs.get? o_fc_sym = some ([xS], oFirstCoeffBody))
    (h_finp : w.defs.get? o_finp_sym = some ([xS], oFinpBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none) :
    ∀ (env : Env) (x xv : SExpr),
      ConvTo w env x xv →
      ConvTo w env (oFirstCoeffT x) (oFirstCoeffExec xv) := by
  intro env x xv hx
  refine conv_defn_1 w env o_fc_sym x xv xS oFirstCoeffBody _
    o_fc_ns h_fn hx ?_
  have hxv := re_val_var_get w (bindArgs [xS] [xv]) { name := "X" } xv
    (bindArgs_single_get_self xS xv)
  have hfinp := o_finp_exec_corr w h_finp h_no_consp _ xT xv hxv
  have hcar := conv_builtin1 w _ { name := "CAR" } xT xv
    (Logic.car xv) (by decide) h_no_car hxv (callBuiltin_car _)
  have hcdrcar := conv_builtin1 w _ { name := "CDR" } (carT xT)
    (Logic.car xv) (Logic.cdr (Logic.car xv)) (by decide) h_no_cdr hcar
    (callBuiltin_cdr _)
  have h := conv_if_lift w (bindArgs [xS] [xv]) (oFinpT xT) xT
    (cdrT (carT xT)) (oFinpExec xv) xv (Logic.cdr (Logic.car xv)) hfinp
    (fun _ => hxv)
    (fun _ => hcdrcar)
  rw [oFirstCoeffExec]
  exact h

private theorem callBuiltin_lt (a b : SExpr) :
    callBuiltin "<" [a, b] = some (Logic.lt a b) := rfl

/-- Stage 1: an `O<` call converges to `oLtExec` (strong induction on
    the FIRST argument's count — both recursion sites descend into
    `x`). -/
theorem o_lt_exec_corr (w : World)
    (h_lt : w.defs.get? o_lt_sym = some ([xS, yS], oLtBody))
    (h_finp : w.defs.get? o_finp_sym = some ([xS], oFinpBody))
    (h_fe : w.defs.get? o_fe_sym = some ([xS], oFirstExptBody))
    (h_fc : w.defs.get? o_fc_sym = some ([xS], oFirstCoeffBody))
    (h_rst : w.defs.get? o_rst_sym = some ([xS], oRstBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_ltb : w.defs.get? ({ name := "<" } : Symbol) = none) :
    ∀ (env : Env) (a b av bv : SExpr),
      ConvTo w env a av → ConvTo w env b bv →
      ConvTo w env (oLtT a b) (oLtExec av bv) := by
  have hbody : ∀ (n : Nat) (xv yv : SExpr), xv.consCount = n →
      ConvTo w (bindArgs [xS, yS] [xv, yv]) oLtBody (oLtExec xv yv) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro xv yv hn
      have hxv := re_val_var_get w (bindArgs [xS, yS] [xv, yv])
        { name := "X" } xv (bindArgs_xy_x' xv yv)
      have hyv := re_val_var_get w (bindArgs [xS, yS] [xv, yv])
        { name := "Y" } yv (bindArgs_xy_y' xv yv)
      have hfx := o_finp_exec_corr w h_finp h_no_consp _ xT xv hxv
      have hfy := o_finp_exec_corr w h_finp h_no_consp _ yT yv hyv
      have hfex := o_fe_exec_corr w h_fe h_finp h_no_consp h_no_car _
        xT xv hxv
      have hfey := o_fe_exec_corr w h_fe h_finp h_no_consp h_no_car _
        yT yv hyv
      have hfcx := o_fc_exec_corr w h_fc h_finp h_no_consp h_no_car
        h_no_cdr _ xT xv hxv
      have hfcy := o_fc_exec_corr w h_fc h_finp h_no_consp h_no_car
        h_no_cdr _ yT yv hyv
      have heqFe := conv_builtin2 w _ { name := "EQUAL" } (oFirstExptT xT)
        (oFirstExptT yT) (oFirstExptExec xv) (oFirstExptExec yv) _
        (by decide) h_no_equal hfex hfey (callBuiltin_equal _ _)
      have heqFc := conv_builtin2 w _ { name := "EQUAL" } (oFirstCoeffT xT)
        (oFirstCoeffT yT) (oFirstCoeffExec xv) (oFirstCoeffExec yv) _
        (by decide) h_no_equal hfcx hfcy (callBuiltin_equal _ _)
      have hltxy := conv_builtin2 w _ { name := "<" } xT yT xv yv _
        (by decide) h_no_ltb hxv hyv (callBuiltin_lt _ _)
      have hltFc := conv_builtin2 w _ { name := "<" } (oFirstCoeffT xT)
        (oFirstCoeffT yT) (oFirstCoeffExec xv) (oFirstCoeffExec yv) _
        (by decide) h_no_ltb hfcx hfcy (callBuiltin_lt _ _)
      -- (o-rst x/y) values
      have hcdrx := conv_builtin1 w _ { name := "CDR" } xT xv
        (Logic.cdr xv) (by decide) h_no_cdr hxv (callBuiltin_cdr _)
      have hcdry := conv_builtin1 w _ { name := "CDR" } yT yv
        (Logic.cdr yv) (by decide) h_no_cdr hyv (callBuiltin_cdr _)
      have hrstx : ConvTo w (bindArgs [xS, yS] [xv, yv]) (oRstT xT)
          (Logic.cdr xv) := by
        refine conv_defn_1 w _ o_rst_sym xT xv xS oRstBody _
          o_rst_ns h_rst hxv ?_
        have hxv' := re_val_var_get w (bindArgs [xS] [xv]) { name := "X" }
          xv (bindArgs_single_get_self xS xv)
        exact conv_builtin1 w _ { name := "CDR" } xT xv (Logic.cdr xv)
          (by decide) h_no_cdr hxv' (callBuiltin_cdr _)
      have hrsty : ConvTo w (bindArgs [xS, yS] [xv, yv]) (oRstT yT)
          (Logic.cdr yv) := by
        refine conv_defn_1 w _ o_rst_sym yT yv xS oRstBody _
          o_rst_ns h_rst hyv ?_
        have hyv' := re_val_var_get w (bindArgs [xS] [yv]) { name := "X" }
          yv (bindArgs_single_get_self xS yv)
        exact conv_builtin1 w _ { name := "CDR" } xT yv (Logic.cdr yv)
          (by decide) h_no_cdr hyv' (callBuiltin_cdr _)
      have houter := conv_if_lift w (bindArgs [xS, yS] [xv, yv])
        (oFinpT xT)
        (ifT (oFinpT yT) (ltT xT yT) qT')
        (ifT (oFinpT yT) qNil
          (ifT (equalT (oFirstExptT xT) (oFirstExptT yT))
            (ifT (equalT (oFirstCoeffT xT) (oFirstCoeffT yT))
              (oLtT (oRstT xT) (oRstT yT))
              (ltT (oFirstCoeffT xT) (oFirstCoeffT yT)))
            (oLtT (oFirstExptT xT) (oFirstExptT yT))))
        (oFinpExec xv)
        (if Logic.toBool (oFinpExec yv) = true then Logic.lt xv yv
         else SExpr.t)
        (if Logic.toBool (oFinpExec yv) = true then SExpr.nil
         else if Logic.toBool (Logic.equal (oFirstExptExec xv)
             (oFirstExptExec yv)) = true then
           (if Logic.toBool (Logic.equal (oFirstCoeffExec xv)
               (oFirstCoeffExec yv)) = true then
             oLtExec (Logic.cdr xv) (Logic.cdr yv)
            else Logic.lt (oFirstCoeffExec xv) (oFirstCoeffExec yv))
         else oLtExec (oFirstExptExec xv) (oFirstExptExec yv))
        hfx
        (fun _ =>
          conv_if_lift w _ (oFinpT yT) (ltT xT yT) qT' (oFinpExec yv)
            (Logic.lt xv yv) SExpr.t hfy
            (fun _ => hltxy)
            (fun _ => re_val_quote w _ SExpr.t))
        (fun hb1 =>
          conv_if_lift w _ (oFinpT yT) qNil _ (oFinpExec yv) SExpr.nil
            (if Logic.toBool (Logic.equal (oFirstExptExec xv)
                (oFirstExptExec yv)) = true then
              (if Logic.toBool (Logic.equal (oFirstCoeffExec xv)
                  (oFirstCoeffExec yv)) = true then
                oLtExec (Logic.cdr xv) (Logic.cdr yv)
               else Logic.lt (oFirstCoeffExec xv) (oFirstCoeffExec yv))
             else oLtExec (oFirstExptExec xv) (oFirstExptExec yv))
            hfy
            (fun _ => re_val_quote w _ SExpr.nil)
            (fun _ =>
              conv_if_lift w _
                (equalT (oFirstExptT xT) (oFirstExptT yT)) _
                (oLtT (oFirstExptT xT) (oFirstExptT yT))
                (Logic.equal (oFirstExptExec xv) (oFirstExptExec yv))
                (if Logic.toBool (Logic.equal (oFirstCoeffExec xv)
                    (oFirstCoeffExec yv)) = true then
                  oLtExec (Logic.cdr xv) (Logic.cdr yv)
                 else Logic.lt (oFirstCoeffExec xv) (oFirstCoeffExec yv))
                (oLtExec (oFirstExptExec xv) (oFirstExptExec yv))
                heqFe
                (fun _ =>
                  conv_if_lift w _
                    (equalT (oFirstCoeffT xT) (oFirstCoeffT yT))
                    (oLtT (oRstT xT) (oRstT yT))
                    (ltT (oFirstCoeffT xT) (oFirstCoeffT yT))
                    (Logic.equal (oFirstCoeffExec xv) (oFirstCoeffExec yv))
                    (oLtExec (Logic.cdr xv) (Logic.cdr yv))
                    (Logic.lt (oFirstCoeffExec xv) (oFirstCoeffExec yv))
                    heqFc
                    (fun _ =>
                      conv_defn_2 w _ o_lt_sym (oRstT xT) (oRstT yT)
                        (Logic.cdr xv) (Logic.cdr yv) xS yS oLtBody _
                        o_lt_ns h_lt hrstx hrsty
                        (ih (Logic.cdr xv).consCount
                          (hn ▸ consCount_cdr_lt_of_consp
                            (oFinpExec_false_consp hb1))
                          (Logic.cdr xv) (Logic.cdr yv) rfl))
                    (fun _ => hltFc))
                (fun _ =>
                  conv_defn_2 w _ o_lt_sym (oFirstExptT xT)
                    (oFirstExptT yT) (oFirstExptExec xv)
                    (oFirstExptExec yv) xS yS oLtBody _
                    o_lt_ns h_lt hfex hfey
                    (ih (oFirstExptExec xv).consCount
                      (hn ▸ oFirstExptExec_consCount_lt hb1)
                      (oFirstExptExec xv) (oFirstExptExec yv) rfl))))
      rw [oLtExec.eq_def]
      simp only [dite_eq_ite]
      exact houter
  intro env a b av bv ha hb
  exact conv_defn_2 w env o_lt_sym a b av bv xS yS oLtBody _
    o_lt_ns h_lt ha hb (hbody av.consCount av bv rfl)

/-- `total:O<` — the driver-shape totality statement. -/
theorem dis_o_lt_total (w : World)
    (h_lt : w.defs.get? o_lt_sym = some ([xS, yS], oLtBody))
    (h_finp : w.defs.get? o_finp_sym = some ([xS], oFinpBody))
    (h_fe : w.defs.get? o_fe_sym = some ([xS], oFirstExptBody))
    (h_fc : w.defs.get? o_fc_sym = some ([xS], oFirstCoeffBody))
    (h_rst : w.defs.get? o_rst_sym = some ([xS], oRstBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_ltb : w.defs.get? ({ name := "<" } : Symbol) = none) :
    ∀ (env' : Env) (a0 a1 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a1 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' (oLtT a0 a1) = some v := by
  intro env' a0 a1 ⟨N0, v0, h0⟩ ⟨N1, v1, h1⟩
  obtain ⟨N, h⟩ := o_lt_exec_corr w h_lt h_finp h_fe h_fc h_rst h_no_consp
    h_no_equal h_no_car h_no_cdr h_no_ltb env' a0 a1 v0 v1
    ⟨N0, h0⟩ ⟨N1, h1⟩
  exact ⟨N, oLtExec v0 v1, h⟩

/-! ## The `acl2-count` kit (`tp:ACL2-COUNT`): INTEGER-ABS / LENGTH /
ACL2-COUNT. The COMPLEX-RATIONALP branch is DEAD in the model (the
predicate is constantly nil — complexes are unrepresentable), so its
recursion is discharged by contradiction. -/

abbrev integerAbsT (x : SExpr) : SExpr := app1 "INTEGER-ABS" x
abbrev lengthT (x : SExpr) : SExpr := app1 "LENGTH" x
abbrev acl2CountT (x : SExpr) : SExpr := app1 "ACL2-COUNT" x

def integerAbsBody : SExpr :=
  ifT (app1 "INTEGERP" xT)
    (ifT (ltT xT q0) (app1 "UNARY--" xT) xT)
    q0

def lengthBody : SExpr :=
  ifT (app1 "STRINGP" xT)
    (app1 "LEN" (app2 "COERCE" xT (qSym "LIST")))
    (app1 "LEN" xT)

def acl2CountBody : SExpr :=
  ifT (conspT xT)
    (plusT q1 (plusT (acl2CountT (carT xT)) (acl2CountT (cdrT xT))))
    (ifT (app1 "RATIONALP" xT)
      (ifT (app1 "INTEGERP" xT)
        (integerAbsT xT)
        (plusT (integerAbsT (app1 "NUMERATOR" xT))
          (app1 "DENOMINATOR" xT)))
      (ifT (app1 "COMPLEX-RATIONALP" xT)
        (plusT q1 (plusT (acl2CountT (app1 "REALPART" xT))
          (acl2CountT (app1 "IMAGPART" xT))))
        (ifT (app1 "STRINGP" xT) (lengthT xT) q0)))

private def integer_abs_sym : Symbol :=
  { package := "ACL2", name := "INTEGER-ABS" }
private def length_sym : Symbol := { package := "ACL2", name := "LENGTH" }
private def acl2_count_sym : Symbol :=
  { package := "ACL2", name := "ACL2-COUNT" }

private theorem integer_abs_ns :
    (integer_abs_sym.isNamed "QUOTE" = false ∧
     integer_abs_sym.isNamed "IF" = false ∧
     integer_abs_sym.isNamed "LET" = false ∧
     integer_abs_sym.isNamed "LET*" = false) := by decide
private theorem length_ns :
    (length_sym.isNamed "QUOTE" = false ∧
     length_sym.isNamed "IF" = false ∧
     length_sym.isNamed "LET" = false ∧
     length_sym.isNamed "LET*" = false) := by decide
private theorem acl2_count_ns :
    (acl2_count_sym.isNamed "QUOTE" = false ∧
     acl2_count_sym.isNamed "IF" = false ∧
     acl2_count_sym.isNamed "LET" = false ∧
     acl2_count_sym.isNamed "LET*" = false) := by decide

private theorem callBuiltin_integerp (a : SExpr) :
    callBuiltin "INTEGERP" [a] = some (Logic.integerp a) := rfl
private theorem callBuiltin_neg (a : SExpr) :
    callBuiltin "UNARY--" [a] = some (Logic.neg a) := rfl
private theorem callBuiltin_stringp (a : SExpr) :
    callBuiltin "STRINGP" [a] = some (Logic.stringp a) := rfl
private theorem callBuiltin_len (a : SExpr) :
    callBuiltin "LEN" [a] = some (Logic.len a) := rfl
private theorem callBuiltin_coerce (a b : SExpr) :
    callBuiltin "COERCE" [a, b] = some (Logic.coerce a b) := rfl
private theorem callBuiltin_rationalp (a : SExpr) :
    callBuiltin "RATIONALP" [a]
      = some (match a with
              | .atom (.number _) => SExpr.t
              | _ => SExpr.nil) := rfl
private theorem callBuiltin_numerator (a : SExpr) :
    callBuiltin "NUMERATOR" [a] = some (Logic.numerator a) := rfl
private theorem callBuiltin_denominator (a : SExpr) :
    callBuiltin "DENOMINATOR" [a] = some (Logic.denominator a) := rfl
private theorem callBuiltin_complexRationalp (a : SExpr) :
    callBuiltin "COMPLEX-RATIONALP" [a]
      = some (Logic.complexRationalp a) := rfl
private theorem callBuiltin_realpart (a : SExpr) :
    callBuiltin "REALPART" [a] = some (Logic.realpart a) := rfl
private theorem callBuiltin_imagpart (a : SExpr) :
    callBuiltin "IMAGPART" [a] = some (Logic.imagpart a) := rfl

/-- `rationalp`'s value as the callBuiltin match (the Logic twin). -/
private abbrev rationalpV (a : SExpr) : SExpr :=
  match a with
  | .atom (.number _) => SExpr.t
  | _ => SExpr.nil

def integerAbsExec (x : SExpr) : SExpr :=
  if Logic.toBool (Logic.integerp x) = true then
    (if Logic.toBool (Logic.lt x (.atom (.number (.int 0)))) = true then
      Logic.neg x
     else x)
  else .atom (.number (.int 0))

def lengthExec (x : SExpr) : SExpr :=
  if Logic.toBool (Logic.stringp x) = true then
    Logic.len (Logic.coerce x (symV "LIST"))
  else Logic.len x

def acl2CountExec (x : SExpr) : SExpr :=
  if Logic.toBool (Logic.consp x) = true then
    Logic.plus int1 (Logic.plus (acl2CountExec (Logic.car x))
      (acl2CountExec (Logic.cdr x)))
  else if Logic.toBool (rationalpV x) = true then
    (if Logic.toBool (Logic.integerp x) = true then integerAbsExec x
     else Logic.plus (integerAbsExec (Logic.numerator x))
       (Logic.denominator x))
  else if _hc : Logic.toBool (Logic.complexRationalp x) = true then
    Logic.plus int1 (Logic.plus (acl2CountExec (Logic.realpart x))
      (acl2CountExec (Logic.imagpart x)))
  else if Logic.toBool (Logic.stringp x) = true then lengthExec x
  else .atom (.number (.int 0))
termination_by x.consCount
decreasing_by
  · exact consCount_car_lt_of_consp (by assumption)
  · exact consCount_cdr_lt_of_consp (by assumption)
  · exact absurd _hc (by simp [Logic.complexRationalp, Logic.toBool])
  · exact absurd _hc (by simp [Logic.complexRationalp, Logic.toBool])

/-- Stage 1 for `integer-abs` (non-recursive). -/
theorem integer_abs_exec_corr (w : World)
    (h_fn : w.defs.get? integer_abs_sym = some ([xS], integerAbsBody))
    (h_no_integerp : w.defs.get? ({ name := "INTEGERP" } : Symbol) = none)
    (h_no_ltb : w.defs.get? ({ name := "<" } : Symbol) = none)
    (h_no_neg : w.defs.get? ({ name := "UNARY--" } : Symbol) = none) :
    ∀ (env : Env) (x xv : SExpr),
      ConvTo w env x xv → ConvTo w env (integerAbsT x) (integerAbsExec xv)
    := by
  intro env x xv hx
  refine conv_defn_1 w env integer_abs_sym x xv xS integerAbsBody _
    integer_abs_ns h_fn hx ?_
  have hxv := re_val_var_get w (bindArgs [xS] [xv]) { name := "X" } xv
    (bindArgs_single_get_self xS xv)
  have hip := conv_builtin1 w _ { name := "INTEGERP" } xT xv
    (Logic.integerp xv) (by decide) h_no_integerp hxv
    (callBuiltin_integerp _)
  have hq0 : ConvTo w (bindArgs [xS] [xv]) q0 (.atom (.number (.int 0))) :=
    re_val_quote w _ (.atom (.number (.int 0)))
  have hlt := conv_builtin2 w _ { name := "<" } xT q0 xv
    (.atom (.number (.int 0))) _ (by decide) h_no_ltb hxv hq0
    (callBuiltin_lt _ _)
  have hneg := conv_builtin1 w _ { name := "UNARY--" } xT xv
    (Logic.neg xv) (by decide) h_no_neg hxv (callBuiltin_neg _)
  have h := conv_if_lift w (bindArgs [xS] [xv]) (app1 "INTEGERP" xT)
    (ifT (ltT xT q0) (app1 "UNARY--" xT) xT) q0 (Logic.integerp xv)
    (if Logic.toBool (Logic.lt xv (.atom (.number (.int 0)))) = true then
      Logic.neg xv
     else xv)
    (.atom (.number (.int 0))) hip
    (fun _ => conv_if_lift w _ (ltT xT q0) (app1 "UNARY--" xT) xT
      (Logic.lt xv (.atom (.number (.int 0)))) (Logic.neg xv) xv hlt
      (fun _ => hneg) (fun _ => hxv))
    (fun _ => hq0)
  rw [integerAbsExec]
  exact h

/-- Stage 1 for `length` (non-recursive). -/
theorem length_exec_corr (w : World)
    (h_fn : w.defs.get? length_sym = some ([xS], lengthBody))
    (h_no_stringp : w.defs.get? ({ name := "STRINGP" } : Symbol) = none)
    (h_no_len : w.defs.get? ({ name := "LEN" } : Symbol) = none)
    (h_no_coerce : w.defs.get? ({ name := "COERCE" } : Symbol) = none) :
    ∀ (env : Env) (x xv : SExpr),
      ConvTo w env x xv → ConvTo w env (lengthT x) (lengthExec xv) := by
  intro env x xv hx
  refine conv_defn_1 w env length_sym x xv xS lengthBody _
    length_ns h_fn hx ?_
  have hxv := re_val_var_get w (bindArgs [xS] [xv]) { name := "X" } xv
    (bindArgs_single_get_self xS xv)
  have hsp := conv_builtin1 w _ { name := "STRINGP" } xT xv
    (Logic.stringp xv) (by decide) h_no_stringp hxv (callBuiltin_stringp _)
  have hco := conv_builtin2 w _ { name := "COERCE" } xT (qSym "LIST") xv
    (symV "LIST") _ (by decide) h_no_coerce hxv
    (re_val_quote w _ (symV "LIST")) (callBuiltin_coerce _ _)
  have hlen1 := conv_builtin1 w _ { name := "LEN" }
    (app2 "COERCE" xT (qSym "LIST")) (Logic.coerce xv (symV "LIST"))
    (Logic.len (Logic.coerce xv (symV "LIST"))) (by decide) h_no_len hco
    (callBuiltin_len _)
  have hlen2 := conv_builtin1 w _ { name := "LEN" } xT xv
    (Logic.len xv) (by decide) h_no_len hxv (callBuiltin_len _)
  have h := conv_if_lift w (bindArgs [xS] [xv]) (app1 "STRINGP" xT)
    (app1 "LEN" (app2 "COERCE" xT (qSym "LIST"))) (app1 "LEN" xT)
    (Logic.stringp xv) (Logic.len (Logic.coerce xv (symV "LIST")))
    (Logic.len xv) hsp
    (fun _ => hlen1) (fun _ => hlen2)
  rw [lengthExec]
  exact h

/-- Stage 1: an `acl2-count` call converges to `acl2CountExec`. -/
theorem acl2_count_exec_corr (w : World)
    (h_ac : w.defs.get? acl2_count_sym = some ([xS], acl2CountBody))
    (h_ia : w.defs.get? integer_abs_sym = some ([xS], integerAbsBody))
    (h_len : w.defs.get? length_sym = some ([xS], lengthBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (h_no_rationalp : w.defs.get? ({ name := "RATIONALP" } : Symbol) = none)
    (h_no_integerp : w.defs.get? ({ name := "INTEGERP" } : Symbol) = none)
    (h_no_num : w.defs.get? ({ name := "NUMERATOR" } : Symbol) = none)
    (h_no_den : w.defs.get? ({ name := "DENOMINATOR" } : Symbol) = none)
    (h_no_crp : w.defs.get?
      ({ name := "COMPLEX-RATIONALP" } : Symbol) = none)
    (h_no_stringp : w.defs.get? ({ name := "STRINGP" } : Symbol) = none)
    (h_no_len : w.defs.get? ({ name := "LEN" } : Symbol) = none)
    (h_no_coerce : w.defs.get? ({ name := "COERCE" } : Symbol) = none)
    (h_no_ltb : w.defs.get? ({ name := "<" } : Symbol) = none)
    (h_no_neg : w.defs.get? ({ name := "UNARY--" } : Symbol) = none) :
    ∀ (env : Env) (x xv : SExpr),
      ConvTo w env x xv → ConvTo w env (acl2CountT x) (acl2CountExec xv)
    := by
  have hbody : ∀ xv : SExpr,
      ConvTo w (bindArgs [xS] [xv]) acl2CountBody (acl2CountExec xv) := by
    refine consCount_strong_induction
      (fun xv => ConvTo w (bindArgs [xS] [xv]) acl2CountBody
        (acl2CountExec xv)) ?_
    intro xv ih
    have hxv := re_val_var_get w (bindArgs [xS] [xv]) { name := "X" } xv
      (bindArgs_single_get_self xS xv)
    have hconsp := conv_builtin1 w _ { name := "CONSP" } xT xv
      (Logic.consp xv) (by decide) h_no_consp hxv (callBuiltin_consp _)
    have hcar := conv_builtin1 w _ { name := "CAR" } xT xv
      (Logic.car xv) (by decide) h_no_car hxv (callBuiltin_car _)
    have hcdr := conv_builtin1 w _ { name := "CDR" } xT xv
      (Logic.cdr xv) (by decide) h_no_cdr hxv (callBuiltin_cdr _)
    have hrp := conv_builtin1 w _ { name := "RATIONALP" } xT xv
      (rationalpV xv) (by decide) h_no_rationalp hxv
      (callBuiltin_rationalp _)
    have hip := conv_builtin1 w _ { name := "INTEGERP" } xT xv
      (Logic.integerp xv) (by decide) h_no_integerp hxv
      (callBuiltin_integerp _)
    have hcrp := conv_builtin1 w _ { name := "COMPLEX-RATIONALP" } xT xv
      (Logic.complexRationalp xv) (by decide) h_no_crp hxv
      (callBuiltin_complexRationalp _)
    have hsp := conv_builtin1 w _ { name := "STRINGP" } xT xv
      (Logic.stringp xv) (by decide) h_no_stringp hxv
      (callBuiltin_stringp _)
    have hnum := conv_builtin1 w _ { name := "NUMERATOR" } xT xv
      (Logic.numerator xv) (by decide) h_no_num hxv
      (callBuiltin_numerator _)
    have hden := conv_builtin1 w _ { name := "DENOMINATOR" } xT xv
      (Logic.denominator xv) (by decide) h_no_den hxv
      (callBuiltin_denominator _)
    -- the cons branch: 1 + (count car + count cdr)
    have hconsBranch : Logic.toBool (Logic.consp xv) = true →
        ConvTo w (bindArgs [xS] [xv])
          (plusT q1 (plusT (acl2CountT (carT xT)) (acl2CountT (cdrT xT))))
          (Logic.plus int1 (Logic.plus (acl2CountExec (Logic.car xv))
            (acl2CountExec (Logic.cdr xv)))) := by
      intro hb
      have hrec1 := conv_defn_1 w _ acl2_count_sym (carT xT)
        (Logic.car xv) xS acl2CountBody _ acl2_count_ns h_ac hcar
        (ih (Logic.car xv) (consCount_car_lt_of_consp hb))
      have hrec2 := conv_defn_1 w _ acl2_count_sym (cdrT xT)
        (Logic.cdr xv) xS acl2CountBody _ acl2_count_ns h_ac hcdr
        (ih (Logic.cdr xv) (consCount_cdr_lt_of_consp hb))
      have hinner := conv_builtin2 w _ { name := "BINARY-+" }
        (acl2CountT (carT xT)) (acl2CountT (cdrT xT)) _ _ _ (by decide)
        h_no_plus hrec1 hrec2 (callBuiltin_plus _ _)
      exact conv_builtin2 w _ { name := "BINARY-+" } q1 _ int1 _ _
        (by decide) h_no_plus (re_val_quote w _ int1) hinner
        (callBuiltin_plus _ _)
    -- the rational branch
    have hIA := integer_abs_exec_corr w h_ia h_no_integerp h_no_ltb
      h_no_neg _ xT xv hxv
    have hIAnum := integer_abs_exec_corr w h_ia h_no_integerp h_no_ltb
      h_no_neg _ (app1 "NUMERATOR" xT) (Logic.numerator xv) hnum
    have hratBranch : ConvTo w (bindArgs [xS] [xv])
        (ifT (app1 "INTEGERP" xT)
          (integerAbsT xT)
          (plusT (integerAbsT (app1 "NUMERATOR" xT))
            (app1 "DENOMINATOR" xT)))
        (if Logic.toBool (Logic.integerp xv) = true then integerAbsExec xv
         else Logic.plus (integerAbsExec (Logic.numerator xv))
           (Logic.denominator xv)) :=
      conv_if_lift w _ (app1 "INTEGERP" xT) _ _ (Logic.integerp xv)
        (integerAbsExec xv)
        (Logic.plus (integerAbsExec (Logic.numerator xv))
          (Logic.denominator xv)) hip
        (fun _ => hIA)
        (fun _ =>
          conv_builtin2 w _ { name := "BINARY-+" }
            (integerAbsT (app1 "NUMERATOR" xT)) (app1 "DENOMINATOR" xT)
            _ _ _ (by decide) h_no_plus hIAnum hden
            (callBuiltin_plus _ _))
    -- the string branch
    have hLen := length_exec_corr w h_len h_no_stringp h_no_len
      h_no_coerce _ xT xv hxv
    have houter := conv_if_lift w (bindArgs [xS] [xv]) (conspT xT)
      (plusT q1 (plusT (acl2CountT (carT xT)) (acl2CountT (cdrT xT))))
      (ifT (app1 "RATIONALP" xT)
        (ifT (app1 "INTEGERP" xT)
          (integerAbsT xT)
          (plusT (integerAbsT (app1 "NUMERATOR" xT))
            (app1 "DENOMINATOR" xT)))
        (ifT (app1 "COMPLEX-RATIONALP" xT)
          (plusT q1 (plusT (acl2CountT (app1 "REALPART" xT))
            (acl2CountT (app1 "IMAGPART" xT))))
          (ifT (app1 "STRINGP" xT) (lengthT xT) q0)))
      (Logic.consp xv)
      (Logic.plus int1 (Logic.plus (acl2CountExec (Logic.car xv))
        (acl2CountExec (Logic.cdr xv))))
      (if Logic.toBool (rationalpV xv) = true then
        (if Logic.toBool (Logic.integerp xv) = true then integerAbsExec xv
         else Logic.plus (integerAbsExec (Logic.numerator xv))
           (Logic.denominator xv))
       else if Logic.toBool (Logic.stringp xv) = true then lengthExec xv
       else .atom (.number (.int 0)))
      hconsp hconsBranch
      (fun _ =>
        conv_if_lift w _ (app1 "RATIONALP" xT) _ _ (rationalpV xv)
          (if Logic.toBool (Logic.integerp xv) = true then
            integerAbsExec xv
           else Logic.plus (integerAbsExec (Logic.numerator xv))
             (Logic.denominator xv))
          (if Logic.toBool (Logic.stringp xv) = true then lengthExec xv
           else .atom (.number (.int 0)))
          hrp
          (fun _ => hratBranch)
          (fun _ =>
            have hcomplex : ConvTo w (bindArgs [xS] [xv])
                (ifT (app1 "COMPLEX-RATIONALP" xT)
                  (plusT q1 (plusT (acl2CountT (app1 "REALPART" xT))
                    (acl2CountT (app1 "IMAGPART" xT))))
                  (ifT (app1 "STRINGP" xT) (lengthT xT) q0))
                (if Logic.toBool (Logic.stringp xv) = true then
                  lengthExec xv
                 else .atom (.number (.int 0))) := by
              have := conv_if_lift w (bindArgs [xS] [xv])
                (app1 "COMPLEX-RATIONALP" xT)
                (plusT q1 (plusT (acl2CountT (app1 "REALPART" xT))
                  (acl2CountT (app1 "IMAGPART" xT))))
                (ifT (app1 "STRINGP" xT) (lengthT xT) q0)
                (Logic.complexRationalp xv)
                (if Logic.toBool (Logic.stringp xv) = true then
                  lengthExec xv
                 else .atom (.number (.int 0)))
                (if Logic.toBool (Logic.stringp xv) = true then
                  lengthExec xv
                 else .atom (.number (.int 0)))
                hcrp
                (fun hb =>
                  absurd hb (by
                    simp [Logic.complexRationalp, Logic.toBool]))
                (fun _ =>
                  conv_if_lift w _ (app1 "STRINGP" xT) (lengthT xT) q0
                    (Logic.stringp xv) (lengthExec xv)
                    (.atom (.number (.int 0))) hsp
                    (fun _ => hLen)
                    (fun _ => re_val_quote w _ (.atom (.number (.int 0)))))
              simpa [ite_self] using this
            hcomplex))
    rw [acl2CountExec.eq_def]
    simp only [dite_eq_ite]
    exact houter
  intro env x xv hx
  exact conv_defn_1 w env acl2_count_sym x xv xS acl2CountBody _
    acl2_count_ns h_ac hx (hbody xv)

/-- `Logic.neg` of an integer atom. -/
private theorem logic_neg_int (m : Int) :
    Logic.neg (.atom (.number (.int m))) = .atom (.number (.int (-m))) := by
  simp [Logic.neg, Logic.toRat, Logic.mkNumber]

/-- `integerAbsExec` always yields a non-negative integer. -/
theorem integerAbsExec_nat (x : SExpr) :
    ∃ n : Nat, integerAbsExec x = .atom (.number (.int n)) := by
  unfold integerAbsExec
  match x with
  | .nil => exact ⟨0, rfl⟩
  | .cons a b => exact ⟨0, rfl⟩
  | .atom (.symbol s) => exact ⟨0, rfl⟩
  | .atom (.keyword k) => exact ⟨0, rfl⟩
  | .atom (.char c) => exact ⟨0, rfl⟩
  | .atom (.string s) => exact ⟨0, rfl⟩
  | .atom (.number (.rational n d hc)) => exact ⟨0, rfl⟩
  | .atom (.number (.int m)) =>
    rw [if_pos (show Logic.toBool
      (Logic.integerp (.atom (.number (.int m)))) = true from rfl)]
    have hcond : Logic.lt (.atom (.number (.int m)))
        (.atom (.number (.int 0)))
        = (if m < 0 then SExpr.t else SExpr.nil) := by
      simp [Logic.lt, Logic.toRat]
    rcases lt_or_ge m 0 with hm | hm
    · rw [if_pos (by rw [hcond, if_pos hm]; rfl), logic_neg_int]
      exact ⟨(-m).toNat, by rw [Int.toNat_of_nonneg (by omega)]⟩
    · rw [if_neg (by rw [hcond, if_neg (by omega)]; decide)]
      exact ⟨m.toNat, by rw [Int.toNat_of_nonneg hm]⟩

/-- `Logic.len` always yields a non-negative integer. -/
private theorem logic_len_nat (x : SExpr) :
    ∃ n : Nat, Logic.len x = .atom (.number (.int n)) := by
  induction x with
  | nil => exact ⟨0, rfl⟩
  | atom a => exact ⟨0, rfl⟩
  | cons a b iha ihb =>
    obtain ⟨n, hn⟩ := ihb
    exact ⟨n + 1, by rw [Logic.len, hn]; simp [Logic.toInt]⟩

/-- `lengthExec` always yields a non-negative integer. -/
theorem lengthExec_nat (x : SExpr) :
    ∃ n : Nat, lengthExec x = .atom (.number (.int n)) := by
  unfold lengthExec
  by_cases h : Logic.toBool (Logic.stringp x) = true
  · rw [if_pos h]; exact logic_len_nat _
  · rw [if_neg h]; exact logic_len_nat _

/-- `Logic.denominator` always yields a non-negative integer. -/
private theorem logic_denominator_nat (x : SExpr) :
    ∃ n : Nat, Logic.denominator x = .atom (.number (.int n)) := by
  cases x with
  | nil => exact ⟨1, rfl⟩
  | cons a b => exact ⟨1, rfl⟩
  | atom a =>
    cases a with
    | number nm =>
      cases nm with
      | int m => exact ⟨1, rfl⟩
      | rational n d hc => exact ⟨d, rfl⟩
    | _ => exact ⟨1, rfl⟩

/-- `acl2CountExec` always yields a non-negative integer. -/
theorem acl2CountExec_nat (x : SExpr) :
    ∃ n : Nat, acl2CountExec x = .atom (.number (.int n)) := by
  fun_induction acl2CountExec x with
  | case1 x _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1
    obtain ⟨n2, h2⟩ := ih2
    rw [h1, h2, logic_plus_int,
        show int1 = (.atom (.number (.int 1)) : SExpr) from rfl,
        logic_plus_int]
    exact ⟨1 + (n1 + n2), by push_cast; ring_nf⟩
  | case2 x _ _ _ => exact integerAbsExec_nat _
  | case3 x _ _ _ =>
    obtain ⟨n1, h1⟩ := integerAbsExec_nat (Logic.numerator x)
    obtain ⟨n2, h2⟩ := logic_denominator_nat x
    rw [h1, h2, logic_plus_int]
    exact ⟨n1 + n2, by push_cast; ring_nf⟩
  | case4 x _ _ hc =>
    exact absurd hc (by simp [Logic.complexRationalp, Logic.toBool])
  | case5 x _ _ _ _ => exact lengthExec_nat _
  | case6 x _ _ _ _ => exact ⟨0, rfl⟩

/-- `tp:ACL2-COUNT`, world-parametric — the emitted non-negative-integer
    TP corollary (unary). -/
theorem dis_acl2_count_tp (w : World)
    (h_ac : w.defs.get? acl2_count_sym = some ([xS], acl2CountBody))
    (h_ia : w.defs.get? integer_abs_sym = some ([xS], integerAbsBody))
    (h_len : w.defs.get? length_sym = some ([xS], lengthBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (h_no_rationalp : w.defs.get? ({ name := "RATIONALP" } : Symbol) = none)
    (h_no_integerp : w.defs.get? ({ name := "INTEGERP" } : Symbol) = none)
    (h_no_num : w.defs.get? ({ name := "NUMERATOR" } : Symbol) = none)
    (h_no_den : w.defs.get? ({ name := "DENOMINATOR" } : Symbol) = none)
    (h_no_crp : w.defs.get?
      ({ name := "COMPLEX-RATIONALP" } : Symbol) = none)
    (h_no_stringp : w.defs.get? ({ name := "STRINGP" } : Symbol) = none)
    (h_no_len : w.defs.get? ({ name := "LEN" } : Symbol) = none)
    (h_no_coerce : w.defs.get? ({ name := "COERCE" } : Symbol) = none)
    (h_no_ltb : w.defs.get? ({ name := "<" } : Symbol) = none)
    (h_no_neg : w.defs.get? ({ name := "UNARY--" } : Symbol) = none)
    (e' : Env) (a0 v : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e' (acl2CountT a0) = some v) :
    (bif Logic.toBool (Logic.integerp v) then
      Logic.not (Logic.lt v (.atom (.number (.int 0))))
    else SExpr.nil) = SExpr.t := by
  obtain ⟨N0, u0, h0⟩ :=
    conv_args1_of_conv_app w e' { name := "ACL2-COUNT" } a0 v (by decide) h
  have happ := acl2_count_exec_corr w h_ac h_ia h_len h_no_consp h_no_car
    h_no_cdr h_no_plus h_no_rationalp h_no_integerp h_no_num h_no_den
    h_no_crp h_no_stringp h_no_len h_no_coerce h_no_ltb h_no_neg
    e' a0 u0 ⟨N0, h0⟩
  rw [val_unique h happ]
  obtain ⟨n, hn⟩ := acl2CountExec_nat u0
  rw [hn]
  simp [Logic.integerp, Logic.lt, Logic.not, Logic.toRat, Logic.toBool,
    show ¬((n : Int) < 0) from by omega]

/-! ## The `qsort` exec kit -/

abbrev qsortT (x : SExpr) : SExpr := app1 "QSORT" x

/-- `(defun qsort (x) …)`, macroexpanded. -/
def qsortBody : SExpr :=
  ifT (conspT xT)
    (ifT (conspT (cdrT xT))
      (appendT
        (qsortT (filterT (qSym "LT") (cdrT xT) (carT xT)))
        (consT (carT xT)
          (qsortT (filterT (qSym "GTE") (cdrT xT) (carT xT)))))
      (consT (carT xT) qNil))
    qNil

private def qsort_sym : Symbol := { package := "ACL2", name := "QSORT" }

private theorem qsort_ns :
    (qsort_sym.isNamed "QUOTE" = false ∧ qsort_sym.isNamed "IF" = false ∧
     qsort_sym.isNamed "LET" = false ∧
     qsort_sym.isNamed "LET*" = false) := by decide

/-- `filterExec` never increases the count. -/
theorem filterExec_consCount_le (fv x ev : SExpr) :
    (filterExec fv x ev).consCount ≤ x.consCount := by
  fun_induction filterExec fv x ev with
  | case1 x hc _ ih =>
    cases x with
    | nil => simp [Logic.consp, Logic.toBool] at hc
    | atom _ => simp [Logic.consp, Logic.toBool] at hc
    | cons a d =>
      rw [show Logic.cdr (SExpr.cons a d) = d from rfl] at ih
      simp only [Logic.cons, Logic.car, Logic.cdr, consCount_cons]
      omega
  | case2 x hc _ ih =>
    exact le_trans ih (consCount_cdr_le _)
  | case3 x _ => simp

def qsortExec (x : SExpr) : SExpr :=
  if _h1 : Logic.toBool (Logic.consp x) = true then
    if Logic.toBool (Logic.consp (Logic.cdr x)) = true then
      appendExec
        (qsortExec (filterExec (symV "LT") (Logic.cdr x) (Logic.car x)))
        (Logic.cons (Logic.car x)
          (qsortExec (filterExec (symV "GTE") (Logic.cdr x) (Logic.car x))))
    else Logic.cons (Logic.car x) SExpr.nil
  else SExpr.nil
termination_by x.consCount
decreasing_by
  · exact lt_of_le_of_lt (filterExec_consCount_le _ _ _)
      (consCount_cdr_lt_of_consp _h1)
  · exact lt_of_le_of_lt (filterExec_consCount_le _ _ _)
      (consCount_cdr_lt_of_consp _h1)

/-- Stage 1: a `qsort` call converges to `qsortExec`. -/
theorem qsort_exec_corr (w : World)
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
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none) :
    ∀ (env : Env) (x xv : SExpr),
      ConvTo w env x xv → ConvTo w env (qsortT x) (qsortExec xv) := by
  have hbody : ∀ xv : SExpr,
      ConvTo w (bindArgs [xS] [xv]) qsortBody (qsortExec xv) := by
    refine consCount_strong_induction
      (fun xv => ConvTo w (bindArgs [xS] [xv]) qsortBody (qsortExec xv)) ?_
    intro xv ih
    have hxv := re_val_var_get w (bindArgs [xS] [xv]) { name := "X" } xv
      (bindArgs_single_get_self xS xv)
    have hconsp := conv_builtin1 w _ { name := "CONSP" } xT xv
      (Logic.consp xv) (by decide) h_no_consp hxv (callBuiltin_consp _)
    have hcar := conv_builtin1 w _ { name := "CAR" } xT xv
      (Logic.car xv) (by decide) h_no_car hxv (callBuiltin_car _)
    have hcdr := conv_builtin1 w _ { name := "CDR" } xT xv
      (Logic.cdr xv) (by decide) h_no_cdr hxv (callBuiltin_cdr _)
    have hconsp2 := conv_builtin1 w _ { name := "CONSP" } (cdrT xT)
      (Logic.cdr xv) (Logic.consp (Logic.cdr xv)) (by decide) h_no_consp
      hcdr (callBuiltin_consp _)
    have hfilLT := filter_exec_corr w h_rel h_filter h_no_consp h_no_equal
      h_no_car h_no_cdr h_no_cons h_no_lexorder _ (qSym "LT") (cdrT xT)
      (carT xT) (symV "LT") (Logic.cdr xv) (Logic.car xv)
      (re_val_quote w _ (symV "LT")) hcdr hcar
    have hfilGTE := filter_exec_corr w h_rel h_filter h_no_consp h_no_equal
      h_no_car h_no_cdr h_no_cons h_no_lexorder _ (qSym "GTE") (cdrT xT)
      (carT xT) (symV "GTE") (Logic.cdr xv) (Logic.car xv)
      (re_val_quote w _ (symV "GTE")) hcdr hcar
    have hbig : Logic.toBool (Logic.consp xv) = true →
        ConvTo w (bindArgs [xS] [xv])
          (appendT
            (qsortT (filterT (qSym "LT") (cdrT xT) (carT xT)))
            (consT (carT xT)
              (qsortT (filterT (qSym "GTE") (cdrT xT) (carT xT)))))
          (appendExec
            (qsortExec (filterExec (symV "LT") (Logic.cdr xv)
              (Logic.car xv)))
            (Logic.cons (Logic.car xv)
              (qsortExec (filterExec (symV "GTE") (Logic.cdr xv)
                (Logic.car xv))))) := by
      intro hb1
      have hlt : (filterExec (symV "LT") (Logic.cdr xv)
          (Logic.car xv)).consCount < xv.consCount :=
        lt_of_le_of_lt (filterExec_consCount_le _ _ _)
          (consCount_cdr_lt_of_consp hb1)
      have hgte : (filterExec (symV "GTE") (Logic.cdr xv)
          (Logic.car xv)).consCount < xv.consCount :=
        lt_of_le_of_lt (filterExec_consCount_le _ _ _)
          (consCount_cdr_lt_of_consp hb1)
      have hqsLT := conv_defn_1 w _ qsort_sym
        (filterT (qSym "LT") (cdrT xT) (carT xT))
        (filterExec (symV "LT") (Logic.cdr xv) (Logic.car xv))
        xS qsortBody _ qsort_ns h_qs hfilLT
        (ih _ hlt)
      have hqsGTE := conv_defn_1 w _ qsort_sym
        (filterT (qSym "GTE") (cdrT xT) (carT xT))
        (filterExec (symV "GTE") (Logic.cdr xv) (Logic.car xv))
        xS qsortBody _ qsort_ns h_qs hfilGTE
        (ih _ hgte)
      have hcons2 := conv_builtin2 w _ { name := "CONS" } (carT xT)
        (qsortT (filterT (qSym "GTE") (cdrT xT) (carT xT)))
        (Logic.car xv) _ _ (by decide) h_no_cons hcar hqsGTE rfl
      exact append_exec_corr w h_app h_no_consp h_no_car h_no_cdr
        h_no_cons _ _ _ _ _ hqsLT hcons2
    have houter := conv_if_lift w (bindArgs [xS] [xv]) (conspT xT)
      (ifT (conspT (cdrT xT))
        (appendT
          (qsortT (filterT (qSym "LT") (cdrT xT) (carT xT)))
          (consT (carT xT)
            (qsortT (filterT (qSym "GTE") (cdrT xT) (carT xT)))))
        (consT (carT xT) qNil))
      qNil (Logic.consp xv)
      (if Logic.toBool (Logic.consp (Logic.cdr xv)) = true then
        appendExec
          (qsortExec (filterExec (symV "LT") (Logic.cdr xv) (Logic.car xv)))
          (Logic.cons (Logic.car xv)
            (qsortExec (filterExec (symV "GTE") (Logic.cdr xv)
              (Logic.car xv))))
       else Logic.cons (Logic.car xv) SExpr.nil)
      SExpr.nil hconsp
      (fun hb1 =>
        conv_if_lift w _ (conspT (cdrT xT)) _ (consT (carT xT) qNil)
          (Logic.consp (Logic.cdr xv))
          (appendExec
            (qsortExec (filterExec (symV "LT") (Logic.cdr xv)
              (Logic.car xv)))
            (Logic.cons (Logic.car xv)
              (qsortExec (filterExec (symV "GTE") (Logic.cdr xv)
                (Logic.car xv)))))
          (Logic.cons (Logic.car xv) SExpr.nil) hconsp2
          (fun _ => hbig hb1)
          (fun _ =>
            conv_builtin2 w _ { name := "CONS" } (carT xT) qNil
              (Logic.car xv) SExpr.nil _ (by decide) h_no_cons hcar
              (re_val_quote w _ SExpr.nil) rfl))
      (fun _ => re_val_quote w _ SExpr.nil)
    rw [qsortExec.eq_def]
    simp only [dite_eq_ite]
    exact houter
  intro env x xv hx
  exact conv_defn_1 w env qsort_sym x xv xS qsortBody _
    qsort_ns h_qs hx (hbody xv)

/-- Pure append on encodings (the world-free twin of
    `corr_append_enc`). -/
theorem appendExec_enc : ∀ (xs ys : List SExpr),
    appendExec (enc xs) (enc ys) = enc (xs ++ ys)
  | [], ys => by
    rw [appendExec.eq_def, show enc ([] : List SExpr) = SExpr.nil from rfl,
        if_neg (by simp [Logic.consp, Logic.toBool])]
    rfl
  | a :: t, ys => by
    rw [appendExec.eq_def,
        if_pos (show Logic.toBool (Logic.consp (enc (a :: t))) = true
          from rfl),
        show Logic.car (enc (a :: t)) = a from rfl,
        show Logic.cdr (enc (a :: t)) = enc t from rfl,
        appendExec_enc t ys]
    rfl

/-- The native quicksort. -/
def qsortL (xs : List SExpr) : List SExpr :=
  match xs with
  | [] => []
  | [a] => [a]
  | a :: b :: t =>
    qsortL ((b :: t).filter (fun c => relL (symV "LT") c a))
      ++ a :: qsortL ((b :: t).filter (fun c => relL (symV "GTE") c a))
termination_by xs.length
decreasing_by
  · exact Nat.lt_succ_of_le (List.length_filter_le _ _)
  · exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Stage 2: `qsortExec` on an encoded list computes `qsortL`. -/
theorem qsortExec_enc (xs : List SExpr) :
    qsortExec (enc xs) = enc (qsortL xs) := by
  induction hn : xs.length using Nat.strong_induction_on generalizing xs
    with
  | _ n ih =>
    match xs with
    | [] => rw [qsortExec.eq_def,
        show enc ([] : List SExpr) = SExpr.nil from rfl,
        dif_neg (by simp [Logic.consp, Logic.toBool])]; simp [qsortL, enc]
    | [a] =>
      rw [qsortExec.eq_def,
          dif_pos (show Logic.toBool (Logic.consp (enc [a])) = true
            from rfl),
          if_neg (show ¬(Logic.toBool (Logic.consp
            (Logic.cdr (enc [a]))) = true) from by
              simp [enc, Logic.cdr, Logic.consp, Logic.toBool]),
          show Logic.car (enc [a]) = a from rfl]
      simp [qsortL, Logic.cons, enc]
    | a :: b :: t =>
      rw [qsortExec.eq_def,
          dif_pos (show Logic.toBool (Logic.consp (enc (a :: b :: t)))
            = true from rfl),
          if_pos (show Logic.toBool (Logic.consp
            (Logic.cdr (enc (a :: b :: t)))) = true from rfl),
          show Logic.cdr (enc (a :: b :: t)) = enc (b :: t) from rfl,
          show Logic.car (enc (a :: b :: t)) = a from rfl,
          filterExec_enc, filterExec_enc,
          ih (filterL (symV "LT") a (b :: t)).length
            (by subst hn; simp only [filterL, List.length_cons]
                exact Nat.lt_succ_of_le (List.length_filter_le _ _))
            _ rfl,
          ih (filterL (symV "GTE") a (b :: t)).length
            (by subst hn; simp only [filterL, List.length_cons]
                exact Nat.lt_succ_of_le (List.length_filter_le _ _))
            _ rfl,
          show Logic.cons a (enc (qsortL (filterL (symV "GTE") a (b :: t))))
            = enc (a :: qsortL (filterL (symV "GTE") a (b :: t))) from rfl,
          appendExec_enc]
      simp only [filterL, qsortL]

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

/-! ## The PERM-COUNTER-EXAMPLE kit + the CONVERT-PERM-TO-HOW-MANY
discharger (the perm-lane content of the qsort flagship: the counting
characterization of permutation, proved at the exec level over ALL
values — the included convert-perm-to-how-many book's main theorem,
transcribed as the rule discharger). -/

abbrev pceT (x y : SExpr) : SExpr := app2 "PERM-COUNTER-EXAMPLE" x y

/-- `(defun perm-counter-example (x y) …)`, macroexpanded. -/
def pceBody : SExpr :=
  ifT (conspT xT)
    (ifT (membT (carT xT) yT)
      (pceT (cdrT xT) (rmT (carT xT) yT))
      (carT xT))
    (carT yT)

private def pce_sym : Symbol :=
  { package := "ACL2", name := "PERM-COUNTER-EXAMPLE" }

private theorem pce_ns :
    (pce_sym.isNamed "QUOTE" = false ∧ pce_sym.isNamed "IF" = false ∧
     pce_sym.isNamed "LET" = false ∧ pce_sym.isNamed "LET*" = false) := by
  decide

/-- `perm-counter-example`'s body as a total Lean function. -/
def pceExec (x y : SExpr) : SExpr :=
  if Logic.toBool (Logic.consp x) = true then
    if Logic.toBool (membExec (Logic.car x) y) = true then
      pceExec (Logic.cdr x) (rmExec (Logic.car x) y)
    else Logic.car x
  else Logic.car y
termination_by x.consCount
decreasing_by exact consCount_cdr_lt_of_consp (by assumption)

/-- Stage 1: a `perm-counter-example` call converges to `pceExec`. -/
theorem pce_exec_corr (w : World)
    (h_pce : w.defs.get? pce_sym = some ([xS, yS], pceBody))
    (h_memb : w.defs.get? { package := "ACL2", name := "MEMB" }
      = some ([{ package := "ACL2", name := "A" },
               { package := "ACL2", name := "X" }], membBody))
    (h_rm : w.defs.get? { package := "ACL2", name := "RM" }
      = some ([{ package := "ACL2", name := "E" },
               { package := "ACL2", name := "X" }], rmBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none) :
    ∀ (env : Env) (a b av bv : SExpr),
      ConvTo w env a av → ConvTo w env b bv →
      ConvTo w env (pceT a b) (pceExec av bv) := by
  have hbody : ∀ xv yv : SExpr,
      ConvTo w (bindArgs [xS, yS] [xv, yv]) pceBody (pceExec xv yv) := by
    refine consCount_strong_induction
      (fun xv => ∀ yv, ConvTo w (bindArgs [xS, yS] [xv, yv]) pceBody
        (pceExec xv yv)) ?_
    intro xv ih yv
    have hxv := re_val_var_get w (bindArgs [xS, yS] [xv, yv])
      { name := "X" } xv (bindArgs_xy_x' xv yv)
    have hyv := re_val_var_get w (bindArgs [xS, yS] [xv, yv])
      { name := "Y" } yv (bindArgs_xy_y' xv yv)
    have hconsp := conv_builtin1 w _ { name := "CONSP" } xT xv
      (Logic.consp xv) (by decide) h_no_consp hxv (callBuiltin_consp _)
    have hcarx := conv_builtin1 w _ { name := "CAR" } xT xv
      (Logic.car xv) (by decide) h_no_car hxv (callBuiltin_car _)
    have hcary := conv_builtin1 w _ { name := "CAR" } yT yv
      (Logic.car yv) (by decide) h_no_car hyv (callBuiltin_car _)
    have hcdrx := conv_builtin1 w _ { name := "CDR" } xT xv
      (Logic.cdr xv) (by decide) h_no_cdr hxv (callBuiltin_cdr _)
    have hmemb := memb_exec_corr w h_memb h_no_consp h_no_equal h_no_car
      h_no_cdr _ (carT xT) yT (Logic.car xv) yv hcarx hyv
    have hrm := rm_exec_corr w h_rm h_no_consp h_no_equal h_no_car
      h_no_cdr h_no_cons _ (carT xT) yT (Logic.car xv) yv hcarx hyv
    have houter := conv_if_lift w (bindArgs [xS, yS] [xv, yv]) (conspT xT)
      (ifT (membT (carT xT) yT)
        (pceT (cdrT xT) (rmT (carT xT) yT))
        (carT xT))
      (carT yT) (Logic.consp xv)
      (if Logic.toBool (membExec (Logic.car xv) yv) = true then
        pceExec (Logic.cdr xv) (rmExec (Logic.car xv) yv)
       else Logic.car xv)
      (Logic.car yv) hconsp
      (fun hb =>
        conv_if_lift w _ (membT (carT xT) yT)
          (pceT (cdrT xT) (rmT (carT xT) yT)) (carT xT)
          (membExec (Logic.car xv) yv)
          (pceExec (Logic.cdr xv) (rmExec (Logic.car xv) yv))
          (Logic.car xv) hmemb
          (fun _ =>
            conv_defn_2 w _ pce_sym (cdrT xT) (rmT (carT xT) yT)
              (Logic.cdr xv) (rmExec (Logic.car xv) yv) xS yS pceBody _
              pce_ns h_pce hcdrx hrm
              (ih (Logic.cdr xv) (consCount_cdr_lt_of_consp hb)
                (rmExec (Logic.car xv) yv)))
          (fun _ => hcarx))
      (fun _ => hcary)
    rw [pceExec.eq_def]
    exact houter
  intro env a b av bv ha hb
  exact conv_defn_2 w env pce_sym a b av bv xS yS pceBody _
    pce_ns h_pce ha hb (hbody av bv)

/-- `total:PERM-COUNTER-EXAMPLE` — the driver-shape totality statement. -/
theorem dis_pce_total (w : World)
    (h_pce : w.defs.get? pce_sym = some ([xS, yS], pceBody))
    (h_memb : w.defs.get? { package := "ACL2", name := "MEMB" }
      = some ([{ package := "ACL2", name := "A" },
               { package := "ACL2", name := "X" }], membBody))
    (h_rm : w.defs.get? { package := "ACL2", name := "RM" }
      = some ([{ package := "ACL2", name := "E" },
               { package := "ACL2", name := "X" }], rmBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none) :
    ∀ (env' : Env) (a0 a1 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a1 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' (pceT a0 a1) = some v := by
  intro env' a0 a1 ⟨N0, v0, h0⟩ ⟨N1, v1, h1⟩
  obtain ⟨N, h⟩ := pce_exec_corr w h_pce h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons env' a0 a1 v0 v1 ⟨N0, h0⟩ ⟨N1, h1⟩
  exact ⟨N, pceExec v0 v1, h⟩

/-! ### The counting sub-lemmas (all at the exec level, over ALL
values — the convert-perm book's ingredient facts) -/

/-- `membExec` is two-valued. -/
theorem membExec_t_or_nil (a x : SExpr) :
    membExec a x = SExpr.t ∨ membExec a x = SExpr.nil := by
  fun_induction membExec a x with
  | case1 x _ _ => exact Or.inl rfl
  | case2 x _ _ ih => exact ih
  | case3 x _ => exact Or.inr rfl

/-- The head counts itself: `how-many (car x) x ≥ 1` on a cons. -/
private theorem howManyExec_head_pos (a d : SExpr) :
    ∃ n : Nat, howManyExec (Logic.car (SExpr.cons a d)) (SExpr.cons a d)
      = .atom (.number (.int (n + 1))) := by
  rw [howManyExec.eq_def,
      if_pos (show Logic.toBool (Logic.consp (SExpr.cons a d)) = true
        from rfl),
      if_pos (show Logic.toBool (Logic.equal (Logic.car (SExpr.cons a d))
        (Logic.car (SExpr.cons a d))) = true from by
          simp [Logic.equal, Logic.toBool, SExpr.t]),
      show Logic.cdr (SExpr.cons a d) = d from rfl]
  obtain ⟨n, hn⟩ := howManyExec_nat (Logic.car (SExpr.cons a d)) d
  rw [hn, logic_plus_int]
  refine ⟨n, ?_⟩
  congr 3
  omega

/-- One cons step of the count. -/
private theorem howManyExec_cons (e hd z : SExpr) :
    howManyExec e (SExpr.cons hd z)
      = (if (e == hd) = true then
          Logic.plus int1 (howManyExec e z)
         else howManyExec e z) := by
  rw [howManyExec.eq_def,
      if_pos (show Logic.toBool (Logic.consp (SExpr.cons hd z)) = true
        from rfl),
      show Logic.car (SExpr.cons hd z) = hd from rfl,
      show Logic.cdr (SExpr.cons hd z) = z from rfl,
      toBool_equal]
  rfl

/-- The count/erase interaction: erasing `b` decrements `e`'s count
    exactly when `e = b` and `b` was present, else leaves it
    unchanged. -/
private theorem howManyExec_rmExec (e b y : SExpr) :
    howManyExec e (rmExec b y)
      = (if e == b ∧ Logic.toBool (membExec b y) = true then
          .atom (.number (.int (Logic.toInt (howManyExec e y) - 1)))
         else howManyExec e y) := by
  fun_induction rmExec b y with
  | case1 y hc heq =>
    -- rm hit the head: b == car y
    cases y with
    | nil => simp [Logic.consp, Logic.toBool] at hc
    | atom _ => simp [Logic.consp, Logic.toBool] at hc
    | cons hd tl =>
      rw [show Logic.car (SExpr.cons hd tl) = hd from rfl,
          toBool_equal] at heq
      have h2 := eq_of_beq heq
      subst h2
      rw [show Logic.cdr (SExpr.cons b tl) = tl from rfl]
      have hmemb : Logic.toBool (membExec b (SExpr.cons b tl)) = true := by
        rw [membExec.eq_def, if_pos hc,
            if_pos (by rw [show Logic.car (SExpr.cons b tl) = b from rfl,
              toBool_equal]; simp)]
        rfl
      by_cases heb : (e == b) = true
      · rw [if_pos ⟨heb, hmemb⟩, howManyExec_cons,
            if_pos (by rw [show e = b from eq_of_beq heb]; simp)]
        obtain ⟨n, hn⟩ := howManyExec_nat e tl
        rw [hn, show int1 = (.atom (.number (.int 1)) : SExpr) from rfl,
            logic_plus_int]
        simp [Logic.toInt]
      · rw [if_neg (fun hcon => heb hcon.1), howManyExec_cons,
            if_neg (by intro hcon; exact heb (by
              rw [show (e == b) = (e == b) from rfl]
              have := eq_of_beq hcon
              subst this; simp))]
  | case2 y hc heq ih =>
    -- rm recursed past the head
    cases y with
    | nil => simp [Logic.consp, Logic.toBool] at hc
    | atom _ => simp [Logic.consp, Logic.toBool] at hc
    | cons hd tl =>
      rw [show Logic.car (SExpr.cons hd tl) = hd from rfl,
          toBool_equal] at heq
      have hbhd : (b == hd) = false := by
        cases h : b == hd with
        | true => exact absurd h (by simpa using heq)
        | false => rfl
      rw [show Logic.cdr (SExpr.cons hd tl) = tl from rfl] at ih ⊢
      rw [show Logic.car (SExpr.cons hd tl) = hd from rfl]
      have hmembEq : membExec b (SExpr.cons hd tl) = membExec b tl := by
        rw [membExec.eq_def, if_pos hc,
            if_neg (by rw [show Logic.car (SExpr.cons hd tl) = hd from rfl,
              toBool_equal, hbhd]; simp),
            show Logic.cdr (SExpr.cons hd tl) = tl from rfl]
      rw [show Logic.cons hd (rmExec b tl) = SExpr.cons hd (rmExec b tl)
            from rfl,
          howManyExec_cons, howManyExec_cons, ih, hmembEq]
      by_cases hcond : e == b ∧ Logic.toBool (membExec b tl) = true
      · rw [if_pos hcond, if_pos hcond]
        cases hehd : e == hd with
        | true =>
          rw [if_pos rfl, if_pos rfl]
          obtain ⟨n, hn⟩ := howManyExec_nat e tl
          rw [hn, show int1 = (.atom (.number (.int 1)) : SExpr) from rfl,
              logic_plus_int, logic_plus_int]
          simp only [Logic.toInt]
          congr 3
          omega
        | false =>
          rw [if_neg (by simp), if_neg (by simp)]
      · rw [if_neg hcond, if_neg hcond]
  | case3 y hc =>
    -- y non-cons: rm = nil, memb = nil
    have hm : membExec b y = SExpr.nil := by
      rw [membExec.eq_def, if_neg hc]
    rw [hm,
        if_neg (by intro hcon; exact absurd hcon.2 (by
          simp [Logic.toBool])),
        howManyExec.eq_def (x := y), if_neg hc,
        howManyExec.eq_def (x := SExpr.nil),
        if_neg (by simp [Logic.consp, Logic.toBool])]

private theorem logic_equal_int (a b : Int) :
    Logic.equal (.atom (.number (.int a))) (.atom (.number (.int b)))
      = (if a = b then SExpr.t else SExpr.nil) := by
  by_cases h : a = b
  · subst h; simp [Logic.equal]
  · simp [Logic.equal, h]

/-- THE CONVERT-PERM-TO-HOW-MANY content, at the exec level over ALL
    values: `perm` IS the count comparison at the counter-example
    element. (The included book's main theorem, value-level.) -/
theorem permExec_eq_convert (x y : SExpr) :
    permExec x y
      = Logic.equal (howManyExec (pceExec x y) x)
          (howManyExec (pceExec x y) y) := by
  fun_induction pceExec x y with
  | case1 x y hc hm ih =>
    -- x cons, (memb (car x) y) true
    cases x with
    | nil => simp [Logic.consp, Logic.toBool] at hc
    | atom _ => simp [Logic.consp, Logic.toBool] at hc
    | cons hd tl =>
      rw [show Logic.car (SExpr.cons hd tl) = hd from rfl] at hm ih
      rw [show Logic.cdr (SExpr.cons hd tl) = tl from rfl] at ih
      rw [permExec.eq_def, if_pos hc,
          show Logic.car (SExpr.cons hd tl) = hd from rfl,
          show Logic.cdr (SExpr.cons hd tl) = tl from rfl,
          if_pos hm, ih]
      set p := pceExec tl (rmExec hd y) with hp
      rw [howManyExec_cons, howManyExec_rmExec]
      obtain ⟨m, hmv⟩ := howManyExec_nat p tl
      obtain ⟨k, hkv⟩ := howManyExec_nat p y
      by_cases hph : (p == hd) = true
      · rw [if_pos ⟨hph, hm⟩, if_pos hph, hmv, hkv,
            show int1 = (.atom (.number (.int 1)) : SExpr) from rfl,
            logic_plus_int]
        simp only [Logic.toInt]
        rw [logic_equal_int, logic_equal_int]
        by_cases hmk : (m : Int) = (k : Int) - 1
        · rw [if_pos hmk, if_pos (by omega)]
        · rw [if_neg hmk, if_neg (by omega)]
      · rw [if_neg (fun hcon => hph hcon.1), if_neg hph]
  | case2 x y hc hm =>
    -- x cons, (memb (car x) y) false: perm is nil, and the counter-example
    -- (car x) witnesses it
    cases x with
    | nil => simp [Logic.consp, Logic.toBool] at hc
    | atom _ => simp [Logic.consp, Logic.toBool] at hc
    | cons hd tl =>
      rw [permExec.eq_def, if_pos hc, if_neg hm]
      have hmnil : membExec (Logic.car (SExpr.cons hd tl)) y
          = SExpr.nil := by
        rcases membExec_t_or_nil (Logic.car (SExpr.cons hd tl)) y with
          h | h
        · rw [h] at hm; exact absurd rfl hm
        · exact h
      rw [howManyExec_zero_of_membExec_nil _ _ hmnil]
      obtain ⟨n, hn⟩ := howManyExec_head_pos hd tl
      rw [hn, logic_equal_int, if_neg (by omega)]
  | case3 x y hc =>
    -- x non-cons: perm is (if (consp y) nil t); the counter-example is
    -- (car y)
    have hx0 : howManyExec (Logic.car y) x = .atom (.number (.int 0)) := by
      rw [howManyExec.eq_def, if_neg hc]
    rw [permExec.eq_def, if_neg hc, hx0]
    cases y with
    | nil =>
      rw [if_neg (by simp [Logic.consp, Logic.toBool]),
          show howManyExec (Logic.car SExpr.nil) SExpr.nil
            = .atom (.number (.int 0)) from by
              rw [howManyExec.eq_def]; rfl,
          logic_equal_int, if_pos rfl]
    | atom a =>
      rw [if_neg (by simp [Logic.consp, Logic.toBool]),
          show howManyExec (Logic.car (SExpr.atom a)) (SExpr.atom a)
            = .atom (.number (.int 0)) from by
              rw [howManyExec.eq_def]
              exact if_neg (by simp [Logic.consp, Logic.toBool]),
          logic_equal_int, if_pos rfl]
    | cons hd tl =>
      rw [if_pos (show Logic.toBool (Logic.consp (SExpr.cons hd tl))
        = true from rfl)]
      obtain ⟨n, hn⟩ := howManyExec_head_pos hd tl
      rw [hn, logic_equal_int, if_neg (by omega)]

/-- `rule:CONVERT-PERM-TO-HOW-MANY` — the stored included-book rule,
    world-parametric, from the exec-level characterization. -/
theorem dis_convert_perm (w : World)
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
    (h_pce : w.defs.get? pce_sym = some ([xS, yS], pceBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none) :
    ∀ env' : Env, ∃ N, ∀ f ≥ N,
      evalOpt f w env' (permT xT yT)
        = evalOpt f w env'
            (equalT (howManyT (pceT xT yT) xT)
              (howManyT (pceT xT yT) yT)) := by
  intro env'
  obtain ⟨vx, hx⟩ := conv_var w env' xS (by decide)
  obtain ⟨vy, hy⟩ := conv_var w env' yS (by decide)
  have hperm := perm_exec_corr w h_perm h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons env' xT yT vx vy hx hy
  have hpce := pce_exec_corr w h_pce h_memb h_rm h_no_consp h_no_equal
    h_no_car h_no_cdr h_no_cons env' xT yT vx vy hx hy
  have hhm1 := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus env' (pceT xT yT) xT (pceExec vx vy) vx hpce hx
  have hhm2 := how_many_exec_corr w h_hm h_no_consp h_no_equal h_no_car
    h_no_cdr h_no_plus env' (pceT xT yT) yT (pceExec vx vy) vy hpce hy
  have hEq := conv_builtin2 w env' { name := "EQUAL" } _ _ _ _ _
    (by decide) h_no_equal hhm1 hhm2 (callBuiltin_equal _ _)
  exact fuel_eq_of_conv hperm hEq (permExec_eq_convert vx vy)

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

/-! ## ORDEREDP-QSORT — the generic orderedp exec (arbitrary values,
where `corr_chain2_enc` is enc-only) + the in-book rule discharger. -/

/-- `orderedp`'s body as a total Lean function (the chain2 shape). -/
def orderedpExec (x : SExpr) : SExpr :=
  if Logic.toBool (Logic.consp x) = true then
    if Logic.toBool (Logic.consp (Logic.cdr x)) = true then
      if Logic.toBool (lexorder (Logic.car x) (Logic.car (Logic.cdr x)))
          = true then
        orderedpExec (Logic.cdr x)
      else SExpr.nil
    else SExpr.t
  else SExpr.t
termination_by x.consCount
decreasing_by exact consCount_cdr_lt_of_consp (by assumption)

theorem orderedpExec_t_or_nil (x : SExpr) :
    orderedpExec x = SExpr.t ∨ orderedpExec x = SExpr.nil := by
  fun_induction orderedpExec x with
  | case1 x _ _ _ ih => exact ih
  | case2 x _ _ _ => exact Or.inr rfl
  | case3 x _ _ => exact Or.inl rfl
  | case4 x _ => exact Or.inl rfl

private def orderedp_sym : Symbol := { package := "ACL2", name := "ORDEREDP" }

private theorem orderedp_ns :
    (orderedp_sym.isNamed "QUOTE" = false ∧
     orderedp_sym.isNamed "IF" = false ∧
     orderedp_sym.isNamed "LET" = false ∧
     orderedp_sym.isNamed "LET*" = false) := by decide

/-- Stage 1: an `orderedp` call converges to `orderedpExec` (over
    ARBITRARY values). -/
theorem orderedp_exec_corr (w : World)
    (h_ord : w.defs.get? orderedp_sym
      = some ([{ package := "ACL2", name := "X" }],
              chain2Body "LEXORDER" "ORDEREDP"))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none) :
    ∀ (env : Env) (x xv : SExpr),
      ConvTo w env x xv → ConvTo w env (orderedpT x) (orderedpExec xv)
    := by
  have hbody : ∀ xv : SExpr,
      ConvTo w (bindArgs [xS] [xv]) (chain2Body "LEXORDER" "ORDEREDP")
        (orderedpExec xv) := by
    refine consCount_strong_induction
      (fun xv => ConvTo w (bindArgs [xS] [xv])
        (chain2Body "LEXORDER" "ORDEREDP") (orderedpExec xv)) ?_
    intro xv ih
    have hxv := re_val_var_get w (bindArgs [xS] [xv]) { name := "X" } xv
      (bindArgs_single_get_self xS xv)
    have hconsp := conv_builtin1 w _ { name := "CONSP" } xT xv
      (Logic.consp xv) (by decide) h_no_consp hxv (callBuiltin_consp _)
    have hcar := conv_builtin1 w _ { name := "CAR" } xT xv
      (Logic.car xv) (by decide) h_no_car hxv (callBuiltin_car _)
    have hcdr := conv_builtin1 w _ { name := "CDR" } xT xv
      (Logic.cdr xv) (by decide) h_no_cdr hxv (callBuiltin_cdr _)
    have hconsp2 := conv_builtin1 w _ { name := "CONSP" } (cdrT xT)
      (Logic.cdr xv) (Logic.consp (Logic.cdr xv)) (by decide) h_no_consp
      hcdr (callBuiltin_consp _)
    have hcadr := conv_builtin1 w _ { name := "CAR" } (cdrT xT)
      (Logic.cdr xv) (Logic.car (Logic.cdr xv)) (by decide) h_no_car hcdr
      (callBuiltin_car _)
    have hlex := conv_builtin2 w _ { name := "LEXORDER" } (carT xT)
      (carT (cdrT xT)) (Logic.car xv) (Logic.car (Logic.cdr xv)) _
      (by decide) h_no_lexorder hcar hcadr (callBuiltin_lexorder _ _)
    have houter := conv_if_lift w (bindArgs [xS] [xv]) (conspT xT)
      (ifT (conspT (cdrT xT))
        (ifT (lexT (carT xT) (carT (cdrT xT)))
          (app1 "ORDEREDP" (cdrT xT)) qNil)
        qT')
      qT' (Logic.consp xv)
      (if Logic.toBool (Logic.consp (Logic.cdr xv)) = true then
        (if Logic.toBool (lexorder (Logic.car xv)
            (Logic.car (Logic.cdr xv))) = true then
          orderedpExec (Logic.cdr xv)
         else SExpr.nil)
       else SExpr.t)
      SExpr.t hconsp
      (fun hb =>
        conv_if_lift w _ (conspT (cdrT xT)) _ qT'
          (Logic.consp (Logic.cdr xv))
          (if Logic.toBool (lexorder (Logic.car xv)
              (Logic.car (Logic.cdr xv))) = true then
            orderedpExec (Logic.cdr xv)
           else SExpr.nil)
          SExpr.t hconsp2
          (fun _ =>
            conv_if_lift w _ (lexT (carT xT) (carT (cdrT xT)))
              (app1 "ORDEREDP" (cdrT xT)) qNil
              (lexorder (Logic.car xv) (Logic.car (Logic.cdr xv)))
              (orderedpExec (Logic.cdr xv)) SExpr.nil hlex
              (fun _ =>
                conv_defn_1 w _ orderedp_sym (cdrT xT) (Logic.cdr xv)
                  { package := "ACL2", name := "X" }
                  (chain2Body "LEXORDER" "ORDEREDP") _ orderedp_ns h_ord
                  hcdr
                  (ih (Logic.cdr xv) (consCount_cdr_lt_of_consp hb)))
              (fun _ => re_val_quote w _ SExpr.nil))
          (fun _ => re_val_quote w _ SExpr.t))
      (fun _ => re_val_quote w _ SExpr.t)
    rw [orderedpExec.eq_def]
    exact houter
  intro env x xv hx
  exact conv_defn_1 w env orderedp_sym x xv
    { package := "ACL2", name := "X" } (chain2Body "LEXORDER" "ORDEREDP")
    _ orderedp_ns h_ord hx (hbody xv)

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

/-! ## The bsort book: BNEXT (the bubble pass) — HOW-MANY-BNEXT

The P3 close-gap build: `bnext`'s recursion carries a CONS-argument call
site (`(BNEXT (CONS (CAR X) (CDR (CDR X))))`), beyond `derive_exec%`'s
reach — the hand route (the `msortExec` precedent). -/

/-- `(defun bnext (x) …)`, macroexpanded — the bubble pass: adjacent
    in-order heads keep, out-of-order heads swap; recursion continues past
    the (possibly swapped) head. -/
def bnextBody : SExpr :=
  ifT (conspT xT)
    (ifT (conspT (cdrT xT))
      (ifT (lexT (carT xT) (carT (cdrT xT)))
        (consT (carT xT) (app1 "BNEXT" (cdrT xT)))
        (consT (carT (cdrT xT))
          (app1 "BNEXT" (consT (carT xT) (cdrT (cdrT xT))))))
      xT)
    xT

def bnext_sym : Symbol := { package := "ACL2", name := "BNEXT" }

theorem bnext_ns :
    (bnext_sym.isNamed "QUOTE" = false ∧ bnext_sym.isNamed "IF" = false ∧
     bnext_sym.isNamed "LET" = false ∧
     bnext_sym.isNamed "LET*" = false) := by decide

/-- The swap-site decrease: replacing the two-element head prefix by the
    (single) first element strictly drops `consCount`. -/
theorem consCount_bnext_swap_lt {x : SExpr}
    (h1 : Logic.toBool (Logic.consp x) = true)
    (h2 : Logic.toBool (Logic.consp (Logic.cdr x)) = true) :
    (Logic.cons (Logic.car x) (Logic.cdr (Logic.cdr x))).consCount
      < x.consCount := by
  match x with
  | .cons a d =>
    match d with
    | .cons b d' =>
      simp only [Logic.car, Logic.cdr, Logic.cons, consCount_cons]
      omega
    | .atom _ => simp [Logic.cdr, Logic.consp, Logic.toBool] at h2
    | .nil => simp [Logic.cdr, Logic.consp, Logic.toBool] at h2
  | .atom _ => simp [Logic.consp, Logic.toBool] at h1
  | .nil => simp [Logic.consp, Logic.toBool] at h1

/-- `bnext`'s body as a total Lean function. -/
def bnextExec (x : SExpr) : SExpr :=
  if _h1 : Logic.toBool (Logic.consp x) = true then
    if _h2 : Logic.toBool (Logic.consp (Logic.cdr x)) = true then
      if Logic.toBool (lexorder (Logic.car x) (Logic.car (Logic.cdr x)))
          = true then
        Logic.cons (Logic.car x) (bnextExec (Logic.cdr x))
      else
        Logic.cons (Logic.car (Logic.cdr x))
          (bnextExec (Logic.cons (Logic.car x) (Logic.cdr (Logic.cdr x))))
    else x
  else x
termination_by x.consCount
decreasing_by
  all_goals first
    | exact consCount_cdr_lt_of_consp _h1
    | exact consCount_bnext_swap_lt _h1 _h2

/-- The NATIVE bubble pass over Lean lists — self-contained (mirror
    criterion: `lexorderB` only, no evaluator vocabulary). -/
def bnextL : List SExpr → List SExpr
  | [] => []
  | [x] => [x]
  | x1 :: x2 :: rest =>
    bif lexorderB x1 x2 then x1 :: bnextL (x2 :: rest)
    else x2 :: bnextL (x1 :: rest)
termination_by l => l.length

/-- Stage 2: `bnextExec` on an encoded list computes the native bubble
    pass. -/
theorem bnextExec_enc : ∀ (xs : List SExpr),
    bnextExec (enc xs) = enc (bnextL xs)
  | [] => by
    rw [bnextExec.eq_def]
    simp [bnextL, enc, Logic.consp, Logic.toBool]
  | [x] => by
    rw [bnextExec.eq_def]
    simp [bnextL, enc, Logic.consp, Logic.toBool, Logic.cdr, Logic.car]
  | x1 :: x2 :: rest => by
    rw [bnextExec.eq_def,
        show enc (x1 :: x2 :: rest) = .cons x1 (.cons x2 (enc rest))
          from rfl]
    simp only [show Logic.consp (SExpr.cons x1 (.cons x2 (enc rest)))
        = SExpr.t from rfl,
      show Logic.cdr (SExpr.cons x1 (.cons x2 (enc rest)))
        = .cons x2 (enc rest) from rfl,
      show Logic.car (SExpr.cons x1 (.cons x2 (enc rest))) = x1 from rfl,
      show Logic.consp (SExpr.cons x2 (enc rest)) = SExpr.t from rfl,
      show Logic.car (SExpr.cons x2 (enc rest)) = x2 from rfl,
      show Logic.cdr (SExpr.cons x2 (enc rest)) = enc rest from rfl]
    rw [lexorder_eq_boolEnc,
        dif_pos (show Logic.toBool SExpr.t = true from rfl),
        dif_pos (show Logic.toBool SExpr.t = true from rfl)]
    cases hlex : lexorderB x1 x2 with
    | true =>
      rw [if_pos (show Logic.toBool (boolEnc true) = true from rfl),
          show SExpr.cons x2 (enc rest) = enc (x2 :: rest) from rfl,
          bnextExec_enc (x2 :: rest)]
      simp [bnextL, hlex, Logic.cons, enc]
    | false =>
      rw [if_neg (show ¬ Logic.toBool (boolEnc false) = true by decide),
          show Logic.cons x1 (enc rest) = enc (x1 :: rest) from rfl,
          bnextExec_enc (x1 :: rest)]
      simp [bnextL, hlex, Logic.cons, enc]
termination_by xs => xs.length
decreasing_by all_goals simp

/-- Stage 1: a `bnext` call converges to `bnextExec`. -/
theorem bnext_exec_corr (w : World)
    (h_bnext : w.defs.get? bnext_sym = some ([xS], bnextBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none) :
    ∀ (env : Env) (x xv : SExpr),
      ConvTo w env x xv → ConvTo w env (app1 "BNEXT" x) (bnextExec xv) := by
  have hbody : ∀ xv : SExpr,
      ConvTo w (bindArgs [xS] [xv]) bnextBody (bnextExec xv) := by
    refine consCount_strong_induction
      (fun xv => ConvTo w (bindArgs [xS] [xv]) bnextBody (bnextExec xv)) ?_
    intro xv ih
    have hxv := re_val_var_get w (bindArgs [xS] [xv]) { name := "X" } xv
      (bindArgs_single_get_self xS xv)
    have hconsp := conv_builtin1 w _ { name := "CONSP" } xT xv
      (Logic.consp xv) (by decide) h_no_consp hxv (callBuiltin_consp _)
    have hcar := conv_builtin1 w _ { name := "CAR" } xT xv
      (Logic.car xv) (by decide) h_no_car hxv (callBuiltin_car _)
    have hcdr := conv_builtin1 w _ { name := "CDR" } xT xv
      (Logic.cdr xv) (by decide) h_no_cdr hxv (callBuiltin_cdr _)
    have hconsp2 := conv_builtin1 w _ { name := "CONSP" } (cdrT xT)
      (Logic.cdr xv) (Logic.consp (Logic.cdr xv)) (by decide) h_no_consp
      hcdr (callBuiltin_consp _)
    have hcar2 := conv_builtin1 w _ { name := "CAR" } (cdrT xT)
      (Logic.cdr xv) (Logic.car (Logic.cdr xv)) (by decide) h_no_car
      hcdr (callBuiltin_car _)
    have hcddr := conv_builtin1 w _ { name := "CDR" } (cdrT xT)
      (Logic.cdr xv) (Logic.cdr (Logic.cdr xv)) (by decide) h_no_cdr
      hcdr (callBuiltin_cdr _)
    have hlex := conv_builtin2 w _ { name := "LEXORDER" } (carT xT)
      (carT (cdrT xT)) (Logic.car xv) (Logic.car (Logic.cdr xv)) _
      (by decide) h_no_lexorder hcar hcar2 (callBuiltin_lexorder _ _)
    have hkeep : Logic.toBool (Logic.consp xv) = true →
        ConvTo w (bindArgs [xS] [xv])
          (consT (carT xT) (app1 "BNEXT" (cdrT xT)))
          (Logic.cons (Logic.car xv) (bnextExec (Logic.cdr xv))) := by
      intro hb1
      exact conv_builtin2 w _ { name := "CONS" } (carT xT)
        (app1 "BNEXT" (cdrT xT)) (Logic.car xv)
        (bnextExec (Logic.cdr xv)) _ (by decide) h_no_cons hcar
        (conv_defn_1 w _ bnext_sym (cdrT xT) (Logic.cdr xv) xS bnextBody _
          bnext_ns h_bnext hcdr
          (ih (Logic.cdr xv) (consCount_cdr_lt_of_consp hb1))) rfl
    have hswap : Logic.toBool (Logic.consp xv) = true →
        Logic.toBool (Logic.consp (Logic.cdr xv)) = true →
        ConvTo w (bindArgs [xS] [xv])
          (consT (carT (cdrT xT))
            (app1 "BNEXT" (consT (carT xT) (cdrT (cdrT xT)))))
          (Logic.cons (Logic.car (Logic.cdr xv))
            (bnextExec (Logic.cons (Logic.car xv)
              (Logic.cdr (Logic.cdr xv))))) := by
      intro hb1 hb2
      have hArg := conv_builtin2 w _ { name := "CONS" } (carT xT)
        (cdrT (cdrT xT)) (Logic.car xv) (Logic.cdr (Logic.cdr xv)) _
        (by decide) h_no_cons hcar hcddr rfl
      exact conv_builtin2 w _ { name := "CONS" } (carT (cdrT xT))
        (app1 "BNEXT" (consT (carT xT) (cdrT (cdrT xT))))
        (Logic.car (Logic.cdr xv))
        (bnextExec (Logic.cons (Logic.car xv) (Logic.cdr (Logic.cdr xv))))
        _ (by decide) h_no_cons hcar2
        (conv_defn_1 w _ bnext_sym (consT (carT xT) (cdrT (cdrT xT)))
          (Logic.cons (Logic.car xv) (Logic.cdr (Logic.cdr xv))) xS
          bnextBody _ bnext_ns h_bnext hArg
          (ih (Logic.cons (Logic.car xv) (Logic.cdr (Logic.cdr xv)))
            (consCount_bnext_swap_lt hb1 hb2))) rfl
    have houter := conv_if_lift w (bindArgs [xS] [xv]) (conspT xT)
      (ifT (conspT (cdrT xT))
        (ifT (lexT (carT xT) (carT (cdrT xT)))
          (consT (carT xT) (app1 "BNEXT" (cdrT xT)))
          (consT (carT (cdrT xT))
            (app1 "BNEXT" (consT (carT xT) (cdrT (cdrT xT))))))
        xT)
      xT (Logic.consp xv)
      (if Logic.toBool (Logic.consp (Logic.cdr xv)) = true then
        (if Logic.toBool (lexorder (Logic.car xv)
            (Logic.car (Logic.cdr xv))) = true then
          Logic.cons (Logic.car xv) (bnextExec (Logic.cdr xv))
        else
          Logic.cons (Logic.car (Logic.cdr xv))
            (bnextExec (Logic.cons (Logic.car xv)
              (Logic.cdr (Logic.cdr xv)))))
       else xv)
      xv hconsp
      (fun hb1 =>
        conv_if_lift w _ (conspT (cdrT xT))
          (ifT (lexT (carT xT) (carT (cdrT xT)))
            (consT (carT xT) (app1 "BNEXT" (cdrT xT)))
            (consT (carT (cdrT xT))
              (app1 "BNEXT" (consT (carT xT) (cdrT (cdrT xT))))))
          xT (Logic.consp (Logic.cdr xv))
          (if Logic.toBool (lexorder (Logic.car xv)
              (Logic.car (Logic.cdr xv))) = true then
            Logic.cons (Logic.car xv) (bnextExec (Logic.cdr xv))
          else
            Logic.cons (Logic.car (Logic.cdr xv))
              (bnextExec (Logic.cons (Logic.car xv)
                (Logic.cdr (Logic.cdr xv)))))
          xv hconsp2
          (fun hb2 =>
            conv_if_lift w _ (lexT (carT xT) (carT (cdrT xT)))
              (consT (carT xT) (app1 "BNEXT" (cdrT xT)))
              (consT (carT (cdrT xT))
                (app1 "BNEXT" (consT (carT xT) (cdrT (cdrT xT)))))
              (lexorder (Logic.car xv) (Logic.car (Logic.cdr xv)))
              (Logic.cons (Logic.car xv) (bnextExec (Logic.cdr xv)))
              (Logic.cons (Logic.car (Logic.cdr xv))
                (bnextExec (Logic.cons (Logic.car xv)
                  (Logic.cdr (Logic.cdr xv)))))
              hlex
              (fun _ => hkeep hb1) (fun _ => hswap hb1 hb2))
          (fun _ => hxv))
      (fun _ => hxv)
    rw [bnextExec.eq_def]
    simp only [dite_eq_ite] at *
    exact houter
  intro env x xv hx
  exact conv_defn_1 w env bnext_sym x xv xS bnextBody _
    bnext_ns h_bnext hx (hbody xv)

/-- The `total:BNEXT` discharger — bnext's totality from the corr. -/
theorem dis_bnext_total (w : World)
    (h_bnext : w.defs.get? bnext_sym = some ([xS], bnextBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none) :
    ∀ (env' : Env) (a0 : SExpr),
      (∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
      ∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env' (app1 "BNEXT" a0) = some v := by
  intro env' a0 ⟨N0, v0, h0⟩
  obtain ⟨N, h⟩ := bnext_exec_corr w h_bnext h_no_consp h_no_car h_no_cdr
    h_no_cons h_no_lexorder env' a0 v0 ⟨N0, h0⟩
  exact ⟨N, bnextExec v0, h⟩

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
