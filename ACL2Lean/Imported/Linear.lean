import ACL2Lean.Imported.LiftingRel

/-! # Imported: the 03-linear book — the LEN2-NONNEG / LEN2-CDR-SMALLER
    decodes (the first COMPARISON-concluded waypoints)

World-parametric (invariant L3) support for lifting the driver's
LEN2-NONNEG and LEN2-CDR-SMALLER replayed statements to the waypoint
statements

    `(0 : Int) ≤ (xs.length : Int)`
    `(t.length : Int) < ((a :: t).length : Int)`

The book (`acl2_samples/recon-tests/03-linear.proof-log`), verbatim:

    (:DEFUN LEN2 :FORMALS (X)
      :BODY (IF (CONSP X) (BINARY-+ '1 (LEN2 (CDR X))) '0) …)
    (:DEFTHM LEN2-NONNEG
      :FORMULA (<= 0 (LEN2 X))  :TFORMULA (NOT (< (LEN2 X) '0)))
    (:DEFTHM LEN2-CDR-SMALLER
      :FORMULA  (IMPLIES (CONSP X) (< (LEN2 (CDR X)) (LEN2 X)))
      :TFORMULA (IMPLIES (CONSP X) (< (LEN2 (CDR X)) (LEN2 X))))

WHY THESE WERE BLOCKED, and what unblocked them. Nothing here needed a
new SIMULATION: `LEN2`'s emitted body is EXACTLY `Lifting.lenBody "LEN2"`
— the name-generic length shape — so `Lifting.corr_len_enc` instantiates
at this world by `decide`, with no exec kit at all. What was missing was
the ENDER: the decode family was EQUAL-only, and both of this book's
usable rows conclude in a COMPARISON. `Imported/LiftingRel.lean` supplies
them (`native_of_replayed_le` for the `(NOT (< … '0))` shape ACL2's `<=`
macroexpands to, `native_of_replayed_lt_of_implies` for the conditional
`<` row); this module is their first consumer.

(The catalog's standing `.pending "len2 dischargers"` reason was STALE in
the same way 02-rev's was — R0 item 7's finding. Both rows' `cond[…]`
labels sit inside `[DISCHARGE: …]`, i.e. on the informational DP probe,
not on the row; the driver emits both replayed statements
UNCONDITIONAL.)

THE STATEMENTS ARE HONESTLY WEAK AT THE NATIVE SIDE — `0 ≤ length` and
`tail-shorter` are facts core Lean would give for free, since `enc`
lands only on genuine lists and `List.length` is a `Nat`. What they
establish is the ROUTE: a comparison-concluded ACL2 theorem decoded
through the interpreter with no equational disguise. Read the mirror
question (is there a product worth showing here?) as OPEN — no spec
`Prop` is proposed off this book. -/

open ACL2 ACL2.Replay ACL2.Lifting

namespace ACL2.Worlds.Linear

/-! ## The defun, exactly as the log-derived world carries it -/

def xS : Symbol := { package := "ACL2", name := "X" }

private def xT : SExpr := .atom (.symbol { name := "X" })

abbrev len2T (x : SExpr) : SExpr := app1 "LEN2" x

def len2_sym : Symbol := { package := "ACL2", name := "LEN2" }

/-- `(defun len2 (x) …)`, macroexpanded — the emitted `:BODY`. It IS the
    name-generic length body, which is the whole reason this book needs no
    exec kit. -/
abbrev len2Body : SExpr := lenBody "LEN2"

/-! ## The replayed statements' formulas + the decodes

Each formula is read off its theorem's root `Goal` clause in
`03-linear.proof-log` (a one-literal clause in both cases, so
`disjoinTerm` is the literal itself):

    :INPUTCLAUSE ((NOT (< (LEN2 X) '0)))
    :INPUTCLAUSE ((IMPLIES (CONSP X) (< (LEN2 (CDR X)) (LEN2 X))))
-/

/-- The LEN2-NONNEG replayed-statement formula. -/
def len2_nonnegFormula : SExpr := notT (ltT (len2T xT) (qInt 0))

/-- The LEN2-CDR-SMALLER replayed-statement formula. -/
def len2_cdr_smallerFormula : SExpr :=
  impliesT (conspT xT) (ltT (len2T (cdrT xT)) (len2T xT))

/-- LEN2-NONNEG, at the waypoint layer: a length is never negative.
    Parameterized by the replayed statement — consumed at exactly ONE
    point (the seam), through `native_of_replayed_le`. -/
theorem len2_nonneg_native_of_replayed (w : World)
    (h_len2 : w.defs.get? len2_sym = some ([xS], len2Body))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_lt : w.defs.get? ({ name := "<" } : Symbol) = none)
    (h_no_not : w.defs.get? ({ name := "NOT" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env len2_nonnegFormula = some v ∧ v ≠ SExpr.nil)
    (xs : List SExpr) :
    (0 : Int) ≤ (xs.length : Int) := by
  let e : Env := ({} : Env).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = ({} : Env).insert xS (enc xs) from rfl, Env.get?_insert,
        if_pos (by decide)])
  exact native_of_replayed_le w e (len2T xT) (qInt 0) (xs.length : Int) 0
    h_no_lt h_no_not
    (corr_len_enc w "LEN2" (by decide) h_len2 h_no_consp h_no_plus h_no_cdr
      xs e xT hx)
    (conv_qInt w e 0) (hreplayed e)

/-- LEN2-CDR-SMALLER, at the waypoint layer: a proper tail is strictly
    shorter. Parameterized by the replayed statement; the `(CONSP X)`
    antecedent is discharged at the encoded instance — a CONS list's
    encoding is a cons, so `Logic.consp` of it is `t` by computation. -/
theorem len2_cdr_smaller_native_of_replayed (w : World)
    (h_len2 : w.defs.get? len2_sym = some ([xS], len2Body))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_lt : w.defs.get? ({ name := "<" } : Symbol) = none)
    (h_no_implies : w.defs.get? ({ name := "IMPLIES" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env len2_cdr_smallerFormula = some v ∧ v ≠ SExpr.nil)
    (a : SExpr) (t : List SExpr) :
    (t.length : Int) < ((a :: t).length : Int) := by
  let e : Env := ({} : Env).insert xS (enc (a :: t))
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc (a :: t)) :=
    re_val_var_get w e { name := "X" } (enc (a :: t)) (by
      show e.get? xS = some (enc (a :: t))
      rw [show e = ({} : Env).insert xS (enc (a :: t)) from rfl,
        Env.get?_insert, if_pos (by decide)])
  have hconsp : ∃ N, ∀ f ≥ N, evalOpt f w e (conspT xT) = some SExpr.t := by
    have h := conv_builtin1 w e { name := "CONSP" } xT (enc (a :: t))
      (Logic.consp (enc (a :: t))) (by decide) h_no_consp hx
      (callBuiltin_consp _)
    -- v4.33 (4.31 #13636): `simpa using h` closes at reducible transparency;
    -- name the plain-`def` `app1` under `conspT`/`cdrT` explicitly.
    simpa [enc, Logic.consp, app1] using h
  have hcdr : ∃ N, ∀ f ≥ N, evalOpt f w e (cdrT xT) = some (enc t) := by
    have h := conv_builtin1 w e { name := "CDR" } xT (enc (a :: t))
      (Logic.cdr (enc (a :: t))) (by decide) h_no_cdr hx (callBuiltin_cdr _)
    simpa [enc, Logic.cdr, app1] using h
  exact native_of_replayed_lt_of_implies w e (conspT xT)
    (len2T (cdrT xT)) (len2T xT) (t.length : Int) ((a :: t).length : Int)
    h_no_lt h_no_implies hconsp
    (corr_len_enc w "LEN2" (by decide) h_len2 h_no_consp h_no_plus h_no_cdr
      t e (cdrT xT) hcdr)
    (corr_len_enc w "LEN2" (by decide) h_len2 h_no_consp h_no_plus h_no_cdr
      (a :: t) e xT hx)
    (hreplayed e)

end ACL2.Worlds.Linear
