import ACL2Lean.Imported.SimGen

/-! # Imported: the 14-accumulator book — the REV-ACC kit and the
    LEN-REV-ACC decode

World-parametric (invariant L3) support for lifting the driver's
LEN-REV-ACC replayed statement to the waypoint statement

    `(revAccL xs acc).length = xs.length + acc.length`

The book (`acl2_samples/recon-tests/14-accumulator.proof-log`), verbatim:

    (:DEFUN REV-ACC :FORMALS (X ACC)
      :BODY (IF (CONSP X) (REV-ACC (CDR X) (CONS (CAR X) ACC)) ACC)
      :MEASURE (ACL2-COUNT X) :WFREL O< :MEASURED (X) …)
    (:DEFTHM LEN-REV-ACC
      :FORMULA (EQUAL (LEN (REV-ACC X ACC)) (+ (LEN X) (LEN ACC)))
      :TFORMULA (EQUAL (LEN (REV-ACC X ACC))
                       (BINARY-+ (LEN X) (LEN ACC))))

THE TEMPLATE GATE'S DECISIVE CASE (the accumulator ambiguity the
thin-Lean ruling designed `derive_sim%` to adjudicate): `REV-ACC` admits
two candidate native readings — the ALIGNED one below, defined by the
exec's own recursion, and the REASSOCIATING one
(`fun xs acc => xs.reverse ++ acc`) whose correspondence would smuggle
in exactly the bridging fact ACL2 states as a book theorem
(`(equal (rev-acc x acc) (append (rev x) acc))`). Only the aligned
reading is supplied here; the reassociating one was run as a deliberate
probe and reverted (see the arc report).

`LEN` is a BUILTIN (`builtinNames`), so it never enters `w.defs` — the
decode reads it through `callBuiltin`/`Logic.len` rather than through a
`corr_len_enc` instance (the `InterleaveSpike` precedent). -/

open ACL2 ACL2.Replay ACL2.Lifting ACL2.ExecGen

namespace ACL2.Worlds.RevAcc

/-! ## The defun, exactly as the log-derived world carries it -/

def xS : Symbol := { package := "ACL2", name := "X" }
def accS : Symbol := { package := "ACL2", name := "ACC" }

private def xT : SExpr := .atom (.symbol { name := "X" })
private def accT : SExpr := .atom (.symbol { name := "ACC" })

abbrev revAccT (x acc : SExpr) : SExpr := app2 "REV-ACC" x acc
abbrev lenT (x : SExpr) : SExpr := app1 "LEN" x
private abbrev ifT (c t e : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "IF" })) (.cons c (.cons t (.cons e .nil)))

/-- `(defun rev-acc (x acc) …)`, macroexpanded — the emitted `:BODY`. -/
def revAccBody : SExpr :=
  ifT (conspT xT) (revAccT (cdrT xT) (consT (carT xT) accT)) accT

def rev_acc_sym : Symbol := { package := "ACL2", name := "REV-ACC" }

/-- `rev-acc`'s body as a total Lean function (measure `(ACL2-COUNT X)`,
    measured formal `X` — index 0) — GENERATED. -/
derive_exec% revAccExec corr rev_acc_exec_corr for rev_acc_sym
  formals [xS, accS] body revAccBody measured 0

/-- `rev-acc`'s native reading: THE ALIGNED ONE — the accumulator
    recursion of the exec itself, argument for argument. -/
def revAccL : List SExpr → List SExpr → List SExpr
  | [], acc => acc
  | a :: t, acc => revAccL t (a :: acc)

/-- Stage 2: `revAccExec` on encoded lists computes `revAccL` —
    GENERATED (`derive_sim%`); the iso is proved by the fixed template
    off `revAccL`'s own recursion. -/
derive_sim% revAccExec_enc for "REV-ACC"
  vars (xs : list) (acc : list)
  exec [xs, acc]
  native (enc (revAccL xs acc))
  simp [revAccL]
  induct functional (revAccL xs acc)

/-! ## The `LEN` builtin's reading

`LEN` is world-absent (a `builtinNames` member, excluded from
`Development.toWorld`), so a `(LEN t)` call dispatches to the
trusted-core `Logic.len`. This is the SIM step for it: on an encoded
list the primitive computes the list's length. -/

theorem logic_len_enc :
    ∀ xs : List SExpr, Logic.len (enc xs) = .atom (.number (.int xs.length))
  | [] => rfl
  | a :: t => by
    show (SExpr.atom (.number (.int (Logic.toInt (Logic.len (enc t)) + 1))))
      = .atom (.number (.int ((a :: t).length : Int)))
    rw [logic_len_enc t]
    simp [Logic.toInt, List.length_cons]

/-! ## The replayed statement's formula + the decode -/

/-- The LEN-REV-ACC replayed-statement formula, read off the log's root
    Goal clause: `(EQUAL (LEN (REV-ACC X ACC)) (BINARY-+ (LEN X) (LEN ACC)))`. -/
def len_rev_accFormula : SExpr :=
  equalT (lenT (revAccT xT accT)) (plusT (lenT xT) (lenT accT))

/-- LEN-REV-ACC, at the waypoint layer: the accumulating reverse's length
    is the sum of the lengths. Parameterized by the replayed statement —
    consumed at exactly ONE point (the seam). -/
theorem len_rev_acc_native_of_replayed (w : World)
    (h_revacc : w.defs.get? rev_acc_sym = some ([xS, accS], revAccBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_len : w.defs.get? ({ name := "LEN" } : Symbol) = none)
    (h_no_plus : w.defs.get? ({ name := "BINARY-+" } : Symbol) = none)
    (h_no_equal : w.defs.get? ({ name := "EQUAL" } : Symbol) = none)
    (hreplayed : ∀ env : Env, ∃ N, ∀ f, f ≥ N → ∃ v,
      evalOpt f w env len_rev_accFormula = some v ∧ v ≠ SExpr.nil)
    (xs acc : List SExpr) :
    (revAccL xs acc).length = xs.length + acc.length := by
  let e : Env := (({} : Env).insert accS (enc acc)).insert xS (enc xs)
  have hx : ∃ N, ∀ f ≥ N, evalOpt f w e xT = some (enc xs) :=
    re_val_var_get w e { name := "X" } (enc xs) (by
      show e.get? xS = some (enc xs)
      rw [show e = (({} : Env).insert accS (enc acc)).insert xS (enc xs)
            from rfl, Env.get?_insert, if_pos (by decide)])
  have hacc : ∃ N, ∀ f ≥ N, evalOpt f w e accT = some (enc acc) :=
    re_val_var_get w e { name := "ACC" } (enc acc) (by
      show e.get? accS = some (enc acc)
      rw [show e = (({} : Env).insert accS (enc acc)).insert xS (enc xs)
            from rfl, Env.get?_insert, if_neg (by decide), Env.get?_insert,
          if_pos (by decide)])
  -- the program value: (REV-ACC X ACC) ⇒ enc (revAccL xs acc)
  have hprog : ∃ N, ∀ f ≥ N, evalOpt f w e (revAccT xT accT)
      = some (enc (revAccL xs acc)) := by
    have h := rev_acc_exec_corr w h_revacc h_no_consp h_no_car h_no_cdr
      h_no_cons e xT accT (enc xs) (enc acc) hx hacc
    rwa [revAccExec_enc] at h
  -- the three LEN calls, through the builtin dispatch
  have hlen : ∀ (t : SExpr) (l : List SExpr),
      (∃ N, ∀ f ≥ N, evalOpt f w e t = some (enc l)) →
      ∃ N, ∀ f ≥ N, evalOpt f w e (lenT t)
        = some (.atom (.number (.int l.length))) := by
    intro t l ht
    have h := conv_builtin1 w e { name := "LEN" } t (enc l)
      (Logic.len (enc l)) (by decide) h_no_len ht (callBuiltin_len _)
    rwa [logic_len_enc] at h
  have hL := hlen _ _ hprog
  have hLx := hlen _ _ hx
  have hLacc := hlen _ _ hacc
  have hR : ∃ N, ∀ f ≥ N, evalOpt f w e (plusT (lenT xT) (lenT accT))
      = some (.atom (.number (.int ((xs.length : Int) + (acc.length : Int))))) := by
    have h := conv_builtin2 w e { name := "BINARY-+" } (lenT xT) (lenT accT)
      (.atom (.number (.int (xs.length : Int))))
      (.atom (.number (.int (acc.length : Int)))) _ (by decide) h_no_plus
      hLx hLacc (callBuiltin_plus _ _)
    rwa [logic_plus_int] at h
  have hint : ((revAccL xs acc).length : Int)
      = (xs.length : Int) + (acc.length : Int) :=
    native_of_replayed_equal w e intRep (lenT (revAccT xT accT))
      (plusT (lenT xT) (lenT accT)) ((revAccL xs acc).length : Int)
      ((xs.length : Int) + (acc.length : Int)) h_no_equal hL hR (hreplayed e)
  omega

end ACL2.Worlds.RevAcc
