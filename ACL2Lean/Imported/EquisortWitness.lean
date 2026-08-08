import ACL2Lean.Imported.Sorting

/-! # Equisort WITNESS exec kits + TP dischargers (close-out queue item 1)

The equisort scopes' `:LOCAL-WITNESS` defuns are insertion-sort clones
(`SORTFN1-INSERT`/`SORTFN1` and the `SS` pair differ from the isort
book's `INSERT`/`ISORT` only in their self-call names).  The witness TP
corollaries (`tp:SORTFN1-INSERT` — `(CONSP …)`; `tp:SORTFN1` — the
consp-or-nil `IF`) are the `proveTp` return-path-CONS frontier class
kept on the equisort constraint rows and blocking the AtCanonical
constants' full non-vacuity (deferral D1).  This module builds their
exec kits and `derive_exec_tp%` dischargers on the established
hand-mirror pattern — bodies transcribed from the emitted `(:DEFUN …)`
events (equisort.proof-log lines 123/127/13674/13678). -/

namespace ACL2.Worlds.Sorting

open ACL2

private def eT : SExpr := .atom (.symbol { name := "E" })
private def xT : SExpr := .atom (.symbol { name := "X" })
private def eS : Symbol := { package := "ACL2", name := "E" }
private def xS : Symbol := { package := "ACL2", name := "X" }
private def qNil : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" })) (.cons .nil .nil)
private def app1 (n : String) (a : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := n })) (.cons a .nil)
private def app2 (n : String) (a b : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := n })) (.cons a (.cons b .nil))
private def app3 (n : String) (a b c : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := n }))
    (.cons a (.cons b (.cons c .nil)))

private def sortfn1_insert_sym : Symbol :=
  { package := "ACL2", name := "SORTFN1-INSERT" }
private def sortfn1_sym : Symbol :=
  { package := "ACL2", name := "SORTFN1" }
private def ssortfn1_insert_sym : Symbol :=
  { package := "ACL2", name := "SSORTFN1-INSERT" }
private def ssortfn1_sym : Symbol :=
  { package := "ACL2", name := "SSORTFN1" }

/-- `(defun sortfn1-insert (e x) …)` — the emitted witness body. -/
def sortfn1InsertBody : SExpr :=
  app3 "IF" (app1 "CONSP" xT)
    (app3 "IF" (app2 "LEXORDER" eT (app1 "CAR" xT))
      (app2 "CONS" eT xT)
      (app2 "CONS" (app1 "CAR" xT)
        (app2 "SORTFN1-INSERT" eT (app1 "CDR" xT))))
    (app2 "CONS" eT xT)

/-- `(defun sortfn1 (x) …)` — the emitted witness body. -/
def sortfn1Body : SExpr :=
  app3 "IF" (app1 "CONSP" xT)
    (app2 "SORTFN1-INSERT" (app1 "CAR" xT)
      (app1 "SORTFN1" (app1 "CDR" xT)))
    qNil

/-- `(defun ssortfn1-insert (e x) …)` — the emitted witness body. -/
def ssortfn1InsertBody : SExpr :=
  app3 "IF" (app1 "CONSP" xT)
    (app3 "IF" (app2 "LEXORDER" eT (app1 "CAR" xT))
      (app2 "CONS" eT xT)
      (app2 "CONS" (app1 "CAR" xT)
        (app2 "SSORTFN1-INSERT" eT (app1 "CDR" xT))))
    (app2 "CONS" eT xT)

/-- `(defun ssortfn1 (x) …)` — the emitted witness body. -/
def ssortfn1Body : SExpr :=
  app3 "IF" (app1 "CONSP" xT)
    (app2 "SSORTFN1-INSERT" (app1 "CAR" xT)
      (app1 "SSORTFN1" (app1 "CDR" xT)))
    qNil

derive_exec% sortfn1InsertExec corr sortfn1_insert_exec_corr
  for sortfn1_insert_sym formals [eS, xS] body sortfn1InsertBody
  measured 1

derive_exec% sortfn1Exec corr sortfn1_exec_corr
  for sortfn1_sym formals [xS] body sortfn1Body measured 0

derive_exec% ssortfn1InsertExec corr ssortfn1_insert_exec_corr
  for ssortfn1_insert_sym formals [eS, xS] body ssortfn1InsertBody
  measured 1

derive_exec% ssortfn1Exec corr ssortfn1_exec_corr
  for ssortfn1_sym formals [xS] body ssortfn1Body measured 0

theorem sortfn1InsertExec_consp (e x : SExpr) :
    Logic.consp (sortfn1InsertExec e x) = SExpr.t := by
  rw [sortfn1InsertExec.eq_def]
  split
  · split <;> rfl
  · rfl

theorem ssortfn1InsertExec_consp (e x : SExpr) :
    Logic.consp (ssortfn1InsertExec e x) = SExpr.t := by
  rw [ssortfn1InsertExec.eq_def]
  split
  · split <;> rfl
  · rfl

theorem sortfn1Exec_consp_or_nil (x : SExpr) :
    Logic.consp (sortfn1Exec x) = SExpr.t ∨ sortfn1Exec x = SExpr.nil := by
  rw [sortfn1Exec.eq_def]
  split
  · exact Or.inl (sortfn1InsertExec_consp _ _)
  · exact Or.inr rfl

theorem ssortfn1Exec_consp_or_nil (x : SExpr) :
    Logic.consp (ssortfn1Exec x) = SExpr.t
      ∨ ssortfn1Exec x = SExpr.nil := by
  rw [ssortfn1Exec.eq_def]
  split
  · exact Or.inl (ssortfn1InsertExec_consp _ _)
  · exact Or.inr rfl

/-- `tp:SORTFN1-INSERT` — the emitted `(CONSP (SORTFN1-INSERT E X))`. -/
derive_exec_tp% dis_sortfn1_insert_tp for "SORTFN1-INSERT"
  (v => Logic.consp v = SExpr.t)
  ending exact sortfn1InsertExec_consp u0 u1

/-- `tp:SORTFN1` — the emitted consp-or-nil `IF` corollary. -/
derive_exec_tp% dis_sortfn1_tp for "SORTFN1"
  (v => (bif Logic.toBool (Logic.consp v) then SExpr.t
     else Logic.equal v SExpr.nil) = SExpr.t)
  ending
    rcases sortfn1Exec_consp_or_nil u0 with hc | hn
    · rw [hc]; rfl
    · rw [hn]; rfl

/-- `tp:SSORTFN1-INSERT` — the emitted `(CONSP (SSORTFN1-INSERT E X))`. -/
derive_exec_tp% dis_ssortfn1_insert_tp for "SSORTFN1-INSERT"
  (v => Logic.consp v = SExpr.t)
  ending exact ssortfn1InsertExec_consp u0 u1

/-- `tp:SSORTFN1` — the emitted consp-or-nil `IF` corollary. -/
derive_exec_tp% dis_ssortfn1_tp for "SSORTFN1"
  (v => (bif Logic.toBool (Logic.consp v) then SExpr.t
     else Logic.equal v SExpr.nil) = SExpr.t)
  ending
    rcases ssortfn1Exec_consp_or_nil u0 with hc | hn
    · rw [hc]; rfl
    · rw [hn]; rfl

end ACL2.Worlds.Sorting
