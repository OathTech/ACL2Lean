import ACL2Lean.Imported.Rev
import ACL2Lean.Imported.LiftingRel

/-! # Imported: the 15-nested-induction book — the DUP kit and the
    NESTED-INDUCTION decode (the first CONJUNCTIVE waypoint)

World-parametric (invariant L3) support for lifting the driver's
NESTED-INDUCTION replayed statement to the waypoint statement

    ((xs ++ ys).length : Int) = xs.length + ys.length   ∧
    ((dupL zs).length : Int) = zs.length + zs.length

The book (`acl2_samples/recon-tests/15-nested-induction.proof-log`),
verbatim:

    (:DEFUN APP :FORMALS (X Y)
      :BODY (IF (CONSP X) (CONS (CAR X) (APP (CDR X) Y)) Y) …)
    (:DEFUN DUP :FORMALS (X)
      :BODY (IF (CONSP X) (CONS (CAR X) (CONS (CAR X) (DUP (CDR X)))) 'NIL) …)
    (:DEFTHM NESTED-INDUCTION
      :FORMULA  (AND (EQUAL (LEN (APP X Y)) (+ (LEN X) (LEN Y)))
                     (EQUAL (LEN (DUP Z)) (+ (LEN Z) (LEN Z))))
      :TFORMULA (IF (EQUAL (LEN (APP X Y)) (BINARY-+ (LEN X) (LEN Y)))
                    (EQUAL (LEN (DUP Z)) (BINARY-+ (LEN Z) (LEN Z))) 'NIL))

The book's FEATURE is two inductions inside one theorem: ACL2 inducts on
`app`'s scheme for the first conjunct, then AGAIN on `dup`'s scheme for
the second, under a synthesized `*1.k` pool root. The decode does not
care — it consumes the ONE replayed statement of the whole conjunction —
but the conjunction is exactly why this row was decode-blocked: every
prior ender takes an `(EQUAL …)`-headed replayed statement, and this one
is `(IF … … 'NIL)`. `Lifting.native_of_replayed_and`
(`Imported/LiftingRel.lean`) is the ender; this module is its first
consumer.

WHAT IS REUSED. `APP` is the same symbol with the same emitted body as
02-rev's, so `Worlds.Rev.appExec`/`app_exec_corr`/`appExec_enc`
instantiate here directly. `LEN` needs no kit either, but NOT for the
reason its `:DEFUN` event suggests: it is in `EvalOpt.builtinNames`, so
the world-derivation deliberately keeps it OUT of `w.defs` (the D3/D2
design note: a world body for `LEN` would shadow the builtin and change
fuel profiles), and the decode reads it through `callBuiltin`/`Logic.len`
— the `TRUE-LISTP` precedent. `logic_len_enc` below is the enc-image
fact that bridges it. Only `DUP` is new.

THE `dupL` READING is the ALIGNED one, argument for argument off `DUP`'s
own recursion (`(CONS (CAR X) (CONS (CAR X) (DUP (CDR X))))` ⇒
`a :: a :: dupL t`); the DOUBLING content stays in the replayed theorem,
where it belongs — nothing in this file says `(dupL zs).length` is twice
anything. -/

open ACL2 ACL2.Replay ACL2.Lifting ACL2.ExecGen

namespace ACL2.Worlds.Nested

/-! ## The defuns, exactly as the log-derived world carries them -/

def xS : Symbol := { package := "ACL2", name := "X" }
def yS : Symbol := { package := "ACL2", name := "Y" }
def zS : Symbol := { package := "ACL2", name := "Z" }

private def xT : SExpr := .atom (.symbol { name := "X" })
private def yT : SExpr := .atom (.symbol { name := "Y" })
private def zT : SExpr := .atom (.symbol { name := "Z" })

abbrev lenT (x : SExpr) : SExpr := app1 "LEN" x
abbrev dupT (x : SExpr) : SExpr := app1 "DUP" x
private abbrev ifT (c t e : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil)))

def dup_sym : Symbol := { package := "ACL2", name := "DUP" }

/-- `(defun dup (x) …)`, macroexpanded — the emitted `:BODY`. -/
def dupBody : SExpr :=
  ifT (conspT xT)
    (consT (carT xT) (consT (carT xT) (dupT (cdrT xT))))
    Worlds.Rev.qNil

/-- ACL2's `LEN` is a BUILTIN (`EvalOpt.builtinNames`), so it never enters
    `w.defs` — the decode reads it through `callBuiltin`/`Logic.len` rather
    than through a definition unfold (the `TRUE-LISTP` precedent in
    `Imported/Rev.lean`). This is the corresponding enc-image fact: the
    builtin's value on an encoded list IS that list's Lean length. -/
theorem logic_len_enc (xs : List SExpr) :
    Logic.len (enc xs) = intRep.enc (xs.length : Int) := by
  induction xs with
  | nil => rfl
  | cons a t ih =>
    show SExpr.atom (.number (.int (Logic.toInt (Logic.len (enc t)) + 1)))
      = intRep.enc (((a :: t).length : Nat) : Int)
    rw [ih]
    show SExpr.atom (.number (.int (Logic.toInt (intRep.enc (t.length : Int)) + 1)))
      = SExpr.atom (.number (.int (((a :: t).length : Nat) : Int)))
    simp [intRep, Logic.toInt, List.length_cons]

/-- `dup`'s body as a total Lean function (measure `(ACL2-COUNT X)`,
    measured formal `X` — index 0) — GENERATED. -/
derive_exec% dupExec corr dup_exec_corr for dup_sym
  formals [xS] body dupBody measured 0

/-- `dup`'s native reading: THE ALIGNED ONE — the recursion of the exec
    itself. Says nothing about lengths. -/
def dupL : List SExpr → List SExpr
  | [] => []
  | a :: t => a :: a :: dupL t

/-- Stage 2 for `DUP`: the exec on encoded lists computes `dupL` —
    GENERATED (`derive_sim%`). -/
derive_sim% dupExec_enc for "DUP"
  vars (xs : list)
  exec [xs]
  native (enc (dupL xs))
  simp [dupL]
  induct structural xs

/-! ## The replayed statement's formula + the decode

Read off the theorem's root `Goal` clause (a one-literal clause, so
`disjoinTerm` is the literal itself):

    :INPUTCLAUSE ((IF (EQUAL (LEN (APP X Y)) (BINARY-+ (LEN X) (LEN Y)))
                      (EQUAL (LEN (DUP Z)) (BINARY-+ (LEN Z) (LEN Z)))
                      'NIL))
-/

/-- The NESTED-INDUCTION replayed-statement formula — the macroexpanded
    conjunction ACL2 emits. -/
def nested_inductionFormula : SExpr :=
  andT (equalT (lenT (Worlds.Rev.appT xT yT)) (plusT (lenT xT) (lenT yT)))
       (equalT (lenT (dupT zT)) (plusT (lenT zT) (lenT zT)))

/-- NESTED-INDUCTION, at the waypoint layer: BOTH conjuncts natively —
    append adds lengths, and duplication doubles them. Parameterized by
    the replayed statement, which is consumed at exactly ONE point (the
    seam) and split there by `Lifting.native_of_replayed_and`. -/
theorem nested_induction_native_of_replayed (w : World)
    (h_app : w.defs.get? Worlds.Rev.app_sym
      = some ([Worlds.Rev.xS, Worlds.Rev.yS], Worlds.Rev.appBody))
    (h_dup : w.defs.get? dup_sym = some ([xS], dupBody))
    (h_no_len : w.defs.get? ({ name := "LEN" } : Symbol) = none)
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env nested_inductionFormula = some v ∧ v ≠ SExpr.nil)
    (xs ys zs : List SExpr) :
    (((xs ++ ys).length : Int) = (xs.length : Int) + (ys.length : Int)) ∧
    (((dupL zs).length : Int) = (zs.length : Int) + (zs.length : Int)) := by
  let e : Env :=
    ((({} : Env).insert zS (enc zs)).insert yS (enc ys)).insert xS (enc xs)
  have he : e = ((({} : Env).insert zS (enc zs)).insert yS (enc ys)).insert xS
      (enc xs) := rfl
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [he, Env.get?_insert, if_pos (by decide)])
  have hy : ∃ N, ∀ f ≥ N, evalOpt f w e yT = some (enc ys) :=
    re_val_var_get w e { name := "Y" } (enc ys) (by
      show e.get? yS = some (enc ys)
      rw [he, Env.get?_insert, if_neg (by decide), Env.get?_insert,
        if_pos (by decide)])
  have hz : ∃ N, ∀ f ≥ N, evalOpt f w e zT = some (enc zs) :=
    re_val_var_get w e { name := "Z" } (enc zs) (by
      show e.get? zS = some (enc zs)
      rw [he, Env.get?_insert, if_neg (by decide), Env.get?_insert,
        if_neg (by decide), Env.get?_insert, if_pos (by decide)])
  have hlen : ∀ (t : SExpr) (l : List SExpr),
      (∃ N, ∀ f ≥ N, evalOpt f w e t = some (enc l)) →
      ∃ N, ∀ f ≥ N, evalOpt f w e (lenT t)
        = some (intRep.enc (l.length : Int)) := by
    intro t l ht
    have h := conv_builtin1 w e { name := "LEN" } t (enc l)
      (Logic.len (enc l)) (by decide) h_no_len ht (callBuiltin_len _)
    rwa [logic_len_enc] at h
  have happ : ∀ (t u : SExpr) (l m : List SExpr),
      (∃ N, ∀ f ≥ N, evalOpt f w e t = some (enc l)) →
      (∃ N, ∀ f ≥ N, evalOpt f w e u = some (enc m)) →
      ∃ N, ∀ f ≥ N, evalOpt f w e (Worlds.Rev.appT t u)
        = some (enc (l ++ m)) := by
    intro t u l m ht hu
    have h := Worlds.Rev.app_exec_corr w h_app h_no_consp h_no_car h_no_cdr
      h_no_cons e t u (enc l) (enc m) ht hu
    rwa [Worlds.Rev.appExec_enc] at h
  have hdup : ∀ (t : SExpr) (l : List SExpr),
      (∃ N, ∀ f ≥ N, evalOpt f w e t = some (enc l)) →
      ∃ N, ∀ f ≥ N, evalOpt f w e (dupT t) = some (enc (dupL l)) := by
    intro t l ht
    have h := dup_exec_corr w h_dup h_no_consp h_no_car h_no_cdr h_no_cons
      e t (enc l) ht
    rwa [dupExec_enc] at h
  exact native_of_replayed_and w e intRep intRep
    (lenT (Worlds.Rev.appT xT yT)) (plusT (lenT xT) (lenT yT))
    (lenT (dupT zT)) (plusT (lenT zT) (lenT zT))
    ((xs ++ ys).length : Int) ((xs.length : Int) + (ys.length : Int))
    ((dupL zs).length : Int) ((zs.length : Int) + (zs.length : Int))
    h_no_equal
    (hlen _ _ (happ _ _ _ _ hx hy))
    (conv_plus_int w e (lenT xT) (lenT yT) (xs.length : Int)
      (ys.length : Int) h_no_plus (hlen _ _ hx) (hlen _ _ hy))
    (hlen _ _ (hdup _ _ hz))
    (conv_plus_int w e (lenT zT) (lenT zT) (zs.length : Int)
      (zs.length : Int) h_no_plus (hlen _ _ hz) (hlen _ _ hz))
    (hreplayed e)

end ACL2.Worlds.Nested
