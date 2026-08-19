import ACL2Lean.Imported.Rev
import ACL2Lean.Imported.LiftingRel

/-! # Imported: the 17-rule-application book — the TLP kit and the
    TLP-APP-NIL / TLP-APP-NIL-TWICE decodes

World-parametric (invariant L3) support for lifting the driver's
TLP-APP-NIL and TLP-APP-NIL-TWICE replayed statements to the waypoint
statements

    `xs ++ [] = xs`
    `(xs ++ []) ++ [] = xs`

The book (`acl2_samples/recon-tests/17-rule-application.proof-log`),
verbatim:

    (:DEFUN TLP :FORMALS (X)
      :BODY (IF (CONSP X) (TLP (CDR X)) (EQUAL X 'NIL)) …)
    (:DEFUN APP :FORMALS (X Y)
      :BODY (IF (CONSP X) (CONS (CAR X) (APP (CDR X) Y)) Y) …)
    (:DEFTHM TLP-APP-NIL
      :FORMULA  (IMPLIES (TLP X) (EQUAL (APP X NIL) X))
      :TFORMULA (IMPLIES (TLP X) (EQUAL (APP X 'NIL) X)))
    (:DEFTHM TLP-APP-NIL-TWICE
      :FORMULA  (IMPLIES (TLP X) (EQUAL (APP (APP X NIL) NIL) X))
      :TFORMULA (IMPLIES (TLP X) (EQUAL (APP (APP X 'NIL) 'NIL) X)))

THE APP KIT IS REUSED, NOT REBUILT. This book's `APP` defun is the SAME
symbol with the SAME emitted body as the 02-rev book's, so
`Worlds.Rev.appExec` / `app_exec_corr` / `appExec_enc` (generated once,
world-parametric) instantiate directly at THIS book's world — every world
fact a `decide` at the consumer. Only `TLP` is new here. (The exec/iso
registries are keyed by ACL2 NAME, so re-deriving `APP` would be rejected
by `derive_sim%` as a duplicate registration — the reuse is structural,
not a convenience.)

THE TLP HYPOTHESIS. Both rows are `(IMPLIES (TLP X) …)`, where `TLP` is
this book's OWN structural true-list recognizer (a defun), not ACL2's
builtin `TRUE-LISTP` — so the 02-rev absorption (`Lifting.trueListp_enc`,
a fact about the builtin) does NOT apply. The analogous fact is proved
here from the book's own program: `tlpExec_enc` (the generated iso) reads
`TLP` on an encoded list as `tlpL`, and `tlpL_true` says that reading is
`true` on EVERY Lean list — i.e. every `enc` image satisfies THIS book's
recognizer. The hypothesis is therefore DISCHARGED at the encoded
instance by a kernel-checked machinery-side fact, exactly as in
`Imported/Rev.lean`; the statement we decode is the full conditional one
ACL2 proved.

THE APP READING is `++`, inherited from `Imported/AppAssoc.lean` /
`Imported/Rev.lean` (the same book function, so necessarily the same
spelling; see Rev.lean's header for the logged compliance status of that
pre-existing reading). -/

open ACL2 ACL2.Replay ACL2.Lifting ACL2.ExecGen

namespace ACL2.Worlds.RuleApp

/-! ## The `TLP` defun, exactly as the log-derived world carries it -/

def xS : Symbol := { package := "ACL2", name := "X" }

private def xT : SExpr := .atom (.symbol { name := "X" })

abbrev tlpT (x : SExpr) : SExpr := app1 "TLP" x
private abbrev ifT (c t e : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil)))

/-- `(defun tlp (x) …)`, macroexpanded — the emitted `:BODY`. -/
def tlpBody : SExpr :=
  ifT (conspT xT) (tlpT (cdrT xT)) (equalT xT Worlds.Rev.qNil)

def tlp_sym : Symbol := { package := "ACL2", name := "TLP" }

/-- `tlp`'s body as a total Lean function (measure `(ACL2-COUNT X)`,
    measured formal `X` — index 0) — GENERATED. -/
derive_exec% tlpExec corr tlp_exec_corr for tlp_sym
  formals [xS] body tlpBody measured 0

/-- `tlp`'s native reading: THE ALIGNED ONE — argument for argument off
    `TLP`'s own recursion. `(CONSP X)` selects the cons arm, so a Lean
    cons recurses on the tail; the else arm `(EQUAL X 'NIL)` is the base,
    and on the empty list `enc [] = nil` makes it `t`. -/
def tlpL : List SExpr → Bool
  | [] => true
  | _ :: t => tlpL t

/-- Stage 2 for `TLP`: the exec on encoded lists computes `tlpL` —
    GENERATED (`derive_sim%`). -/
derive_sim% tlpExec_enc for "TLP"
  vars (xs : list)
  exec [xs]
  native (boolEnc (tlpL xs))
  simp [tlpL]
  induct structural xs

/-- THE ENC-IMAGE FACT for this book's own recognizer: every `enc` image
    satisfies `TLP`. This is the `Lifting.trueListp_enc` analogue for a
    DEFUN recognizer — the half of the `List SExpr ≃ {s // …}` picture
    that the hypothesis absorption below consumes. -/
theorem tlpL_true : ∀ xs : List SExpr, tlpL xs = true := by
  intro xs
  induction xs with
  | nil => rfl
  | cons _ t ih => simpa [tlpL] using ih

/-! ## The replayed statements' formulas + the decodes

Each formula is read off its theorem's root `Goal` clause in
`17-rule-application.proof-log` (a one-literal clause in both cases, so
`disjoinTerm` is the literal itself):

    line 37: :INPUTCLAUSE ((IMPLIES (TLP X) (EQUAL (APP X 'NIL) X)))
    line 59: :INPUTCLAUSE ((IMPLIES (TLP X) (EQUAL (APP (APP X 'NIL) 'NIL) X)))
-/

/-- The TLP-APP-NIL replayed-statement formula. -/
def tlp_app_nilFormula : SExpr :=
  impliesT (tlpT xT) (equalT (Worlds.Rev.appT xT Worlds.Rev.qNil) xT)

/-- The TLP-APP-NIL-TWICE replayed-statement formula. -/
def tlp_app_nil_twiceFormula : SExpr :=
  impliesT (tlpT xT)
    (equalT (Worlds.Rev.appT (Worlds.Rev.appT xT Worlds.Rev.qNil)
      Worlds.Rev.qNil) xT)

/-- The `(TLP t)` antecedent, at an ENCODED list, converges to `t` — the
    hypothesis-absorption step of both rows. The content is `tlpL_true`
    routed through the generated iso: this book's own recognizer accepts
    every `enc` image. -/
private theorem conv_tlp_enc (w : World) (e : Env)
    (h_tlp : w.defs.get? tlp_sym = some ([xS], tlpBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (t : SExpr) (l : List SExpr)
    (ht : ∃ N, ∀ f ≥ N, evalOpt f w e t = some (enc l)) :
    ∃ N, ∀ f ≥ N, evalOpt f w e (tlpT t) = some SExpr.t := by
  have h := tlp_exec_corr w h_tlp h_no_consp h_no_equal h_no_cdr e t (enc l) ht
  rw [tlpExec_enc] at h
  -- v4.33 (4.31 #13636): `simpa using h` closes at reducible transparency;
  -- name the plain defs (`app1` under `tlpT`, `tlp_sym`, `ConvTo`) explicitly.
  simpa [tlpL_true l, boolEnc, ConvTo, app1, tlp_sym] using h

/-- TLP-APP-NIL, at the waypoint layer: appending nothing changes
    nothing. Parameterized by the replayed statement — consumed at
    exactly ONE point (the seam). The `(TLP X)` antecedent is discharged
    by `conv_tlp_enc` at the encoded instance. -/
theorem tlp_app_nil_native_of_replayed (w : World)
    (h_app : w.defs.get? Worlds.Rev.app_sym
      = some ([Worlds.Rev.xS, Worlds.Rev.yS], Worlds.Rev.appBody))
    (h_tlp : w.defs.get? tlp_sym = some ([xS], tlpBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env tlp_app_nilFormula = some v ∧ v ≠ SExpr.nil)
    (xs : List SExpr) :
    xs ++ [] = xs := by
  let e : Env := ({} : Env).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ({} : Env).insert xS (enc xs) from rfl, Env.get?_insert,
        if_pos (by decide)])
  have hnil : ∃ N, ∀ f ≥ N,
      evalOpt f w e Worlds.Rev.qNil = some (enc ([] : List SExpr)) :=
    re_val_quote w e SExpr.nil
  have happ : ∀ (t u : SExpr) (l m : List SExpr),
      (∃ N, ∀ f ≥ N, evalOpt f w e t = some (enc l)) →
      (∃ N, ∀ f ≥ N, evalOpt f w e u = some (enc m)) →
      ∃ N, ∀ f ≥ N, evalOpt f w e (Worlds.Rev.appT t u)
        = some (enc (l ++ m)) := by
    intro t u l m ht hu
    have h := Worlds.Rev.app_exec_corr w h_app h_no_consp h_no_car h_no_cdr
      h_no_cons e t u (enc l) (enc m) ht hu
    rwa [Worlds.Rev.appExec_enc] at h
  -- the conditional row reduces to the UNCONDITIONAL equational ender by
  -- the generic peel: the `(TLP X)` antecedent converges to `t` at the
  -- encoded instance, so the replayed implication IS the replayed
  -- equality (`Lifting.replayed_of_replayed_implies`)
  exact native_of_replayed_equal w e listRep
    (Worlds.Rev.appT xT Worlds.Rev.qNil) xT (xs ++ []) xs h_no_equal
    (happ _ _ _ _ hx hnil) hx
    (replayed_of_replayed_implies w e (tlpT xT)
      (equalT (Worlds.Rev.appT xT Worlds.Rev.qNil) xT) _ h_no_implies
      (conv_tlp_enc w e h_tlp h_no_consp h_no_equal h_no_cdr xT xs hx)
      (conv_equalT w e (Worlds.Rev.appT xT Worlds.Rev.qNil) xT _ _ h_no_equal
        (happ _ _ _ _ hx hnil) hx)
      (hreplayed e))

/-- TLP-APP-NIL-TWICE, at the waypoint layer: the book's capstone — the
    theorem ACL2 proves with NO induction of its own, by applying the
    stored TLP-APP-NIL rewrite rule twice (the inner redex, then the
    outer), each application's hypothesis relieved from the clause's own
    `(NOT (TLP X))` literal. Parameterized by the replayed statement; the
    `(TLP X)` antecedent is discharged as in TLP-APP-NIL. -/
theorem tlp_app_nil_twice_native_of_replayed (w : World)
    (h_app : w.defs.get? Worlds.Rev.app_sym
      = some ([Worlds.Rev.xS, Worlds.Rev.yS], Worlds.Rev.appBody))
    (h_tlp : w.defs.get? tlp_sym = some ([xS], tlpBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env tlp_app_nil_twiceFormula = some v ∧ v ≠ SExpr.nil)
    (xs : List SExpr) :
    (xs ++ []) ++ [] = xs := by
  let e : Env := ({} : Env).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ({} : Env).insert xS (enc xs) from rfl, Env.get?_insert,
        if_pos (by decide)])
  have hnil : ∃ N, ∀ f ≥ N,
      evalOpt f w e Worlds.Rev.qNil = some (enc ([] : List SExpr)) :=
    re_val_quote w e SExpr.nil
  have happ : ∀ (t u : SExpr) (l m : List SExpr),
      (∃ N, ∀ f ≥ N, evalOpt f w e t = some (enc l)) →
      (∃ N, ∀ f ≥ N, evalOpt f w e u = some (enc m)) →
      ∃ N, ∀ f ≥ N, evalOpt f w e (Worlds.Rev.appT t u)
        = some (enc (l ++ m)) := by
    intro t u l m ht hu
    have h := Worlds.Rev.app_exec_corr w h_app h_no_consp h_no_car h_no_cdr
      h_no_cons e t u (enc l) (enc m) ht hu
    rwa [Worlds.Rev.appExec_enc] at h
  exact native_of_replayed_equal w e listRep
    (Worlds.Rev.appT (Worlds.Rev.appT xT Worlds.Rev.qNil) Worlds.Rev.qNil)
    xT ((xs ++ []) ++ []) xs h_no_equal
    (happ _ _ _ _ (happ _ _ _ _ hx hnil) hnil) hx
    (replayed_of_replayed_implies w e (tlpT xT)
      (equalT (Worlds.Rev.appT (Worlds.Rev.appT xT Worlds.Rev.qNil)
        Worlds.Rev.qNil) xT) _ h_no_implies
      (conv_tlp_enc w e h_tlp h_no_consp h_no_equal h_no_cdr xT xs hx)
      (conv_equalT w e (Worlds.Rev.appT (Worlds.Rev.appT xT Worlds.Rev.qNil)
        Worlds.Rev.qNil) xT _ _ h_no_equal
        (happ _ _ _ _ (happ _ _ _ _ hx hnil) hnil) hx)
      (hreplayed e))

end ACL2.Worlds.RuleApp
