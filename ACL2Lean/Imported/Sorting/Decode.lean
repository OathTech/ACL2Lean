import ACL2Lean.Imported.Sorting.IsoAdmission

/-! # The sorting books — LAYER 3 of 4: THE DECODE

**The only layer that touches replayed statements.**

Each `*_native_of_replayed` theorem takes the driver's replayed
statement — "at this world, the goal formula evaluates to something
non-`nil`" — plus the world facts that pin the book's defuns, and
transports it into the native Lean statement using the `Iso`
correspondences. The theorem's actual CONTENT therefore flows through
the replayed statement: this is the seam the catalog's SEAM GATE and
`hreplayed`-USAGE GATE mechanize (`Mirrors/Catalog.lean`).

Also here: the `*Formula` constants (each book theorem's ACL2 formula
as an `SExpr`) and the decode-only support lemmas.

This module carries the ordered-perms, convert-perm-to-how-many and
isort books; `DecodeSorts.lean` carries qsort/msort/bsort. The split is
the 1500-line module norm, nothing more.
-/

open ACL2 ACL2.Replay ACL2.Lifting ACL2.Worlds.Perm ACL2.ExecGen

namespace ACL2.Worlds.Sorting

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

end ACL2.Worlds.Sorting
