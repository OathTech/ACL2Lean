import ACL2Lean.Imported.SimGen

/-! # Imported: the 02-rev book — the APP/REV kit and the APP-NIL /
    REV-APP / REV-REV decodes

World-parametric (invariant L3) support for lifting the driver's
APP-NIL, REV-APP and REV-REV replayed statements to the waypoint
statements

    `xs ++ [] = xs`
    `revL (xs ++ ys) = revL ys ++ revL xs`
    `revL (revL xs) = xs`

The book (`acl2_samples/recon-tests/02-rev.proof-log`), verbatim:

    (:DEFUN APP :FORMALS (X Y)
      :BODY (IF (CONSP X) (CONS (CAR X) (APP (CDR X) Y)) Y) …)
    (:DEFUN REV :FORMALS (X)
      :BODY (IF (CONSP X) (APP (REV (CDR X)) (CONS (CAR X) 'NIL)) 'NIL) …)
    (:DEFTHM APP-NIL
      :FORMULA  (IMPLIES (TRUE-LISTP X) (EQUAL (APP X NIL) X))
      :TFORMULA (IMPLIES (TRUE-LISTP X) (EQUAL (APP X 'NIL) X)))
    (:DEFTHM REV-APP
      :FORMULA (EQUAL (REV (APP A B)) (APP (REV B) (REV A))))
    (:DEFTHM REV-REV
      :FORMULA (IMPLIES (TRUE-LISTP X) (EQUAL (REV (REV X)) X)))

THE TRUE-LISTP HYPOTHESIS (APP-NIL, REV-REV). Both replayed statements
are `(IMPLIES (TRUE-LISTP X) …)`; the waypoint statements are
UNCONDITIONAL because the decode instantiates `X` at an ENCODED list and
every `enc` image is a true list — `Lifting.trueListp_enc`, the
kernel-checked enc-image fact that is one half of the
`List SExpr ≃ {s // trueListp s = t}` isomorphism the `listRep`
representation is built on. So the hypothesis is DISCHARGED at the seam,
by a machinery-side fact about the encoding, not assumed away: the
statement we decode is the full conditional one ACL2 proved.

THE APP READING is `++`, not an own-definition: it is the SPELLING
already fixed for this book by `Imported/AppAssoc.lean`'s
`corr_app_enc`/`app_assoc_native_driver` and, one layer up, by the
registered mirror square `MirrorProofs.app_agree_append`. `revL` is
therefore spelled with the same operator — the ALIGNED reading, argument
for argument off `REV`'s own recursion (`(APP (REV (CDR X)) (CONS (CAR X)
'NIL))` ⇒ `revL t ++ [a]`). Under the vocabulary practice (2026-08-13)
the append reading is one of the FIVE logged pre-existing non-compliant
readings whose compliance pass is a tracked TODO; `revL` inherits that
status rather than introducing a second, conflicting spelling of `APP`.

`TRUE-LISTP` is a BUILTIN (`builtinNames`), so it never enters `w.defs` —
the decode reads it through `callBuiltin`/`Logic.trueListp` rather than
through a definition unfold (the `LEN` precedent in `Imported/RevAcc`). -/

open ACL2 ACL2.Replay ACL2.Lifting ACL2.ExecGen

namespace ACL2.Worlds.Rev

/-! ## The defuns, exactly as the log-derived world carries them -/

def xS : Symbol := { package := "ACL2", name := "X" }
def yS : Symbol := { package := "ACL2", name := "Y" }
def aS : Symbol := { package := "ACL2", name := "A" }
def bS : Symbol := { package := "ACL2", name := "B" }

private def xT : SExpr := .atom (.symbol { name := "X" })
private def yT : SExpr := .atom (.symbol { name := "Y" })
private def aT : SExpr := .atom (.symbol { name := "A" })
private def bT : SExpr := .atom (.symbol { name := "B" })

abbrev appT (x y : SExpr) : SExpr := app2 "APP" x y
abbrev revT (x : SExpr) : SExpr := app1 "REV" x
abbrev trueListpT (x : SExpr) : SExpr := app1 "TRUE-LISTP" x
private abbrev ifT (c t e : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil)))
/-- `'NIL` — the quoted empty list the emitted bodies/formulas carry. -/
def qNil : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil)

/-- `(defun app (x y) …)`, macroexpanded — the emitted `:BODY`. -/
def appBody : SExpr := ifT (conspT xT) (consT (carT xT) (appT (cdrT xT) yT)) yT

/-- `(defun rev (x) …)`, macroexpanded — the emitted `:BODY`. -/
def revBody : SExpr :=
  ifT (conspT xT) (appT (revT (cdrT xT)) (consT (carT xT) qNil)) qNil

def app_sym : Symbol := { package := "ACL2", name := "APP" }
def rev_sym : Symbol := { package := "ACL2", name := "REV" }

/-- `app`'s body as a total Lean function (measure `(ACL2-COUNT X)`,
    measured formal `X` — index 0) — GENERATED. -/
derive_exec% appExec corr app_exec_corr for app_sym
  formals [xS, yS] body appBody measured 0

/-- Stage 2 for `APP`: the exec on encoded lists computes `++` —
    GENERATED (`derive_sim%`). -/
derive_sim% appExec_enc for "APP"
  vars (xs : list) (ys : list)
  exec [xs, ys]
  native (enc (xs ++ ys))
  simp []
  induct structural xs

/-- `rev`'s body as a total Lean function (measure `(ACL2-COUNT X)`,
    measured formal `X` — index 0) — GENERATED. -/
derive_exec% revExec corr rev_exec_corr for rev_sym
  formals [xS] body revBody measured 0

/-- `rev`'s native reading: THE ALIGNED ONE — the recursion of the exec
    itself, spelled in the append vocabulary this book's `APP` already
    reads as (see the header). -/
def revL : List SExpr → List SExpr
  | [] => []
  | a :: t => revL t ++ [a]

/-- Stage 2 for `REV`: the exec on encoded lists computes `revL` —
    GENERATED (`derive_sim%`); the iso is proved by the fixed template
    off `revL`'s own recursion, with `APP`'s registered iso supplying the
    callee step. -/
derive_sim% revExec_enc for "REV"
  vars (xs : list)
  exec [xs]
  native (enc (revL xs))
  simp [revL]
  induct functional (revL xs)

/-! ## The replayed statements' formulas + the decodes

Each formula is read off its theorem's root `Goal` clause in
`02-rev.proof-log` (a one-literal clause in all three cases, so
`disjoinTerm` is the literal itself). -/

/-- The APP-NIL replayed-statement formula (log line 93's `:INPUTCLAUSE`):
    `(IMPLIES (TRUE-LISTP X) (EQUAL (APP X 'NIL) X))`. -/
def app_nilFormula : SExpr :=
  impliesT (trueListpT xT) (equalT (appT xT qNil) xT)

/-- The REV-APP replayed-statement formula (log line 115's `:INPUTCLAUSE`):
    `(EQUAL (REV (APP A B)) (APP (REV B) (REV A)))`. -/
def rev_appFormula : SExpr :=
  equalT (revT (appT aT bT)) (appT (revT bT) (revT aT))

/-- The REV-REV replayed-statement formula (the root `Goal` clause):
    `(IMPLIES (TRUE-LISTP X) (EQUAL (REV (REV X)) X))`. -/
def rev_revFormula : SExpr :=
  impliesT (trueListpT xT) (equalT (revT (revT xT)) xT)

/-- The TRUE-LISTP antecedent, at an ENCODED list, converges to `t` — the
    hypothesis-absorption step of the two conditional rows. The content is
    `Lifting.trueListp_enc`: every `enc` image is a true list. -/
private theorem conv_trueListp_enc (w : World) (e : Env)
    (h_no_tlp : w.defs.get? ({ name := "TRUE-LISTP" } : Symbol) = none)
    (t : SExpr) (l : List SExpr)
    (ht : ∃ N, ∀ f ≥ N, evalOpt f w e t = some (enc l)) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (trueListpT t) = some SExpr.t := by
  have h := conv_builtin1 w e { name := "TRUE-LISTP" } t (enc l)
    (Logic.trueListp (enc l)) (by decide) h_no_tlp ht (callBuiltin_true_listp _)
  rwa [trueListp_enc] at h

/-- APP-NIL, at the waypoint layer: appending nothing changes nothing.
    Parameterized by the replayed statement — consumed at exactly ONE
    point (the seam). The `(TRUE-LISTP X)` antecedent is discharged by
    `conv_trueListp_enc` at the encoded instance. -/
theorem app_nil_native_of_replayed (w : World)
    (h_app : w.defs.get? app_sym = some ([xS, yS], appBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (h_no_tlp : w.defs.get? ({ name := "TRUE-LISTP" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env app_nilFormula = some v ∧ v ≠ SExpr.nil)
    (xs : List SExpr) :
    xs ++ [] = xs := by
  let e : Env := ({} : Env).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ({} : Env).insert xS (enc xs) from rfl, Env.get?_insert,
        if_pos (by decide)])
  have hnil : ∃ N, ∀ f ≥ N, evalOpt f w e qNil = some (enc ([] : List SExpr)) :=
    re_val_quote w e SExpr.nil
  -- the program value: (APP X 'NIL) ⇒ enc (xs ++ [])
  have happ : ∃ N, ∀ f ≥ N, evalOpt f w e (appT xT qNil)
      = some (enc (xs ++ [])) := by
    have h := app_exec_corr w h_app h_no_consp h_no_car h_no_cdr h_no_cons
      e xT qNil (enc xs) (enc []) hx hnil
    rwa [appExec_enc] at h
  -- the conditional: antecedent ⇒ t (the enc image is a true list)
  have himp := conv_impliesT w e (trueListpT xT) (equalT (appT xT qNil) xT)
    SExpr.t (Logic.equal (enc (xs ++ [])) (enc xs)) h_no_implies
    (conv_trueListp_enc w e h_no_tlp xT xs hx)
    (conv_equalT w e (appT xT qNil) xT _ _ h_no_equal happ hx)
  have hval : Logic.implies SExpr.t (Logic.equal (enc (xs ++ [])) (enc xs))
      = SExpr.t :=
    implies_t_of_ne_nil (ne_nil_of_evtrue_conv (hreplayed e) himp)
  exact enc_inj (eq_of_equal_truthy (truthy_of_implies_t hval rfl))

/-- REV-APP, at the waypoint layer: reversal turns an append around.
    Parameterized by the replayed statement (unconditional row). -/
theorem rev_app_native_of_replayed (w : World)
    (h_app : w.defs.get? app_sym = some ([xS, yS], appBody))
    (h_rev : w.defs.get? rev_sym = some ([xS], revBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env rev_appFormula = some v ∧ v ≠ SExpr.nil)
    (xs ys : List SExpr) :
    revL (xs ++ ys) = revL ys ++ revL xs := by
  let e : Env := (({} : Env).insert bS (enc ys)).insert aS (enc xs)
  have ha : ∃ N, ∀ f ≥ N, evalOpt f w e aT = some (enc xs) :=
    re_val_var_get w e { name := "A" } (enc xs) (by
      show e.get? aS = some (enc xs)
      rw [show e = (({} : Env).insert bS (enc ys)).insert aS (enc xs) from rfl,
        Env.get?_insert, if_pos (by decide)])
  have hb : ∃ N, ∀ f ≥ N, evalOpt f w e bT = some (enc ys) :=
    re_val_var_get w e { name := "B" } (enc ys) (by
      show e.get? bS = some (enc ys)
      rw [show e = (({} : Env).insert bS (enc ys)).insert aS (enc xs) from rfl,
        Env.get?_insert, if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  have hrev : ∀ (t : SExpr) (l : List SExpr),
      (∃ N, ∀ f ≥ N, evalOpt f w e t = some (enc l)) →
      ∃ N, ∀ f ≥ N, evalOpt f w e (revT t) = some (enc (revL l)) := by
    intro t l ht
    have h := rev_exec_corr w h_app h_rev h_no_consp h_no_car h_no_cdr
      h_no_cons e t (enc l) ht
    rwa [revExec_enc] at h
  have happ : ∀ (t u : SExpr) (l m : List SExpr),
      (∃ N, ∀ f ≥ N, evalOpt f w e t = some (enc l)) →
      (∃ N, ∀ f ≥ N, evalOpt f w e u = some (enc m)) →
      ∃ N, ∀ f ≥ N, evalOpt f w e (appT t u) = some (enc (l ++ m)) := by
    intro t u l m ht hu
    have h := app_exec_corr w h_app h_no_consp h_no_car h_no_cdr h_no_cons
      e t u (enc l) (enc m) ht hu
    rwa [appExec_enc] at h
  exact native_of_replayed_equal w e listRep
    (revT (appT aT bT)) (appT (revT bT) (revT aT))
    (revL (xs ++ ys)) (revL ys ++ revL xs) h_no_equal
    (hrev _ _ (happ _ _ _ _ ha hb))
    (happ _ _ _ _ (hrev _ _ hb) (hrev _ _ ha))
    (hreplayed e)

/-- REV-REV, at the waypoint layer: reversal is an involution.
    Parameterized by the replayed statement; the `(TRUE-LISTP X)`
    antecedent is discharged as in APP-NIL. -/
theorem rev_rev_native_of_replayed (w : World)
    (h_app : w.defs.get? app_sym = some ([xS, yS], appBody))
    (h_rev : w.defs.get? rev_sym = some ([xS], revBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (h_no_tlp : w.defs.get? ({ name := "TRUE-LISTP" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env rev_revFormula = some v ∧ v ≠ SExpr.nil)
    (xs : List SExpr) :
    revL (revL xs) = xs := by
  let e : Env := ({} : Env).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ({} : Env).insert xS (enc xs) from rfl, Env.get?_insert,
        if_pos (by decide)])
  have hrev : ∀ (t : SExpr) (l : List SExpr),
      (∃ N, ∀ f ≥ N, evalOpt f w e t = some (enc l)) →
      ∃ N, ∀ f ≥ N, evalOpt f w e (revT t) = some (enc (revL l)) := by
    intro t l ht
    have h := rev_exec_corr w h_app h_rev h_no_consp h_no_car h_no_cdr
      h_no_cons e t (enc l) ht
    rwa [revExec_enc] at h
  have himp := conv_impliesT w e (trueListpT xT) (equalT (revT (revT xT)) xT)
    SExpr.t (Logic.equal (enc (revL (revL xs))) (enc xs)) h_no_implies
    (conv_trueListp_enc w e h_no_tlp xT xs hx)
    (conv_equalT w e (revT (revT xT)) xT _ _ h_no_equal
      (hrev _ _ (hrev _ _ hx)) hx)
  have hval : Logic.implies SExpr.t (Logic.equal (enc (revL (revL xs))) (enc xs))
      = SExpr.t :=
    implies_t_of_ne_nil (ne_nil_of_evtrue_conv (hreplayed e) himp)
  exact enc_inj (eq_of_equal_truthy (truthy_of_implies_t hval rfl))

end ACL2.Worlds.Rev
