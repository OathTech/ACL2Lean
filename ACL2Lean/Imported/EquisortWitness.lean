import ACL2Lean.Imported.Sorting

/-! # Equisort WITNESS exec kits + TP dischargers (close-out queue item 1)

The equisort scopes' `:LOCAL-WITNESS` defuns are insertion-sort clones
(`SORTFN1-INSERT`/`SORTFN1` and the `SS` pair differ from the isort
book's `INSERT`/`ISORT` only in their self-call names).  The witness TP
corollaries (`tp:SORTFN1-INSERT` — `(CONSP …)`; `tp:SORTFN1` — the
consp-or-nil `IF`) are the `proveTp` return-path-CONS frontier class
kept on the equisort constraint rows and blocking the AtCanonical
constants' full non-vacuity (deferral D1).  This module builds their
exec kits and (formerly `derive_exec_tp%`-generated) TP dischargers on
the established
hand-mirror pattern — bodies transcribed from the emitted `(:DEFUN …)`
events (equisort.proof-log lines 123/127/13674/13678).

Thin-Lean ruling (2026-08-11): the four TP dischargers below keep their
STATEMENTS (live consumers in `Mirrors/EquisortParametric`) but their
Lean-side proofs are retired to `sorry` — see the per-theorem
FORBIDDEN-DEBT markers. -/

namespace ACL2.Worlds.Sorting

open ACL2

-- `eT`/`xT`/`eS`/`xS` come from `Imported/Sorting.lean` (same namespace,
-- identical definitions): the local private copies were removed when the
-- book layer's split-out modules needed them (mirror wave 2026-08-11).
-- `qNil` joined them in the demo-build split (2026-08-11): it became a
-- non-private constant of `Imported/Sorting/Sims.lean` (the layer split
-- needs it across modules), and the local copy — byte-identical — would
-- now shadow it.
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

/-- FORBIDDEN-DEBT (thin-Lean ruling 2026-08-11): this establishes
    `tp:SORTFN1-INSERT` — the emitted `(CONSP (SORTFN1-INSERT E X))`
    corollary — Lean-side; content ACL2 derives. Statement kept as the
    named premise; proof retired to `sorry`. UNLOCK: TP-replay
    discharge for the witness fns. -/
theorem dis_sortfn1_insert_tp (w : World)
    (h_sortfn1_insert : w.defs.get? sortfn1_insert_sym
      = some ([eS, xS], sortfn1InsertBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (e' : Env) (a0 a1 v : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e'
      (SExpr.cons (SExpr.atom (Atom.symbol sortfn1_insert_sym))
        (SExpr.cons a0 (SExpr.cons a1 SExpr.nil))) = some v) :
    Logic.consp v = SExpr.t := by
  sorry

/-- FORBIDDEN-DEBT (thin-Lean ruling 2026-08-11): this establishes
    `tp:SORTFN1` — the emitted consp-or-nil `IF` corollary — Lean-side;
    content ACL2 derives. Statement kept as the named premise; proof
    retired to `sorry`. UNLOCK: TP-replay discharge for the witness
    fns. -/
theorem dis_sortfn1_tp (w : World)
    (h_sortfn1_insert : w.defs.get? sortfn1_insert_sym
      = some ([eS, xS], sortfn1InsertBody))
    (h_sortfn1 : w.defs.get? sortfn1_sym = some ([xS], sortfn1Body))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (e' : Env) (a0 v : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e'
      (SExpr.cons (SExpr.atom (Atom.symbol sortfn1_sym))
        (SExpr.cons a0 SExpr.nil)) = some v) :
    (bif Logic.toBool (Logic.consp v) then SExpr.t
      else Logic.equal v SExpr.nil) = SExpr.t := by
  sorry

/-- FORBIDDEN-DEBT (thin-Lean ruling 2026-08-11): this establishes
    `tp:SSORTFN1-INSERT` — the emitted `(CONSP (SSORTFN1-INSERT E X))`
    corollary — Lean-side; content ACL2 derives. Statement kept as the
    named premise; proof retired to `sorry`. UNLOCK: TP-replay
    discharge for the witness fns. -/
theorem dis_ssortfn1_insert_tp (w : World)
    (h_ssortfn1_insert : w.defs.get? ssortfn1_insert_sym
      = some ([eS, xS], ssortfn1InsertBody))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (e' : Env) (a0 a1 v : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e'
      (SExpr.cons (SExpr.atom (Atom.symbol ssortfn1_insert_sym))
        (SExpr.cons a0 (SExpr.cons a1 SExpr.nil))) = some v) :
    Logic.consp v = SExpr.t := by
  sorry

/-- FORBIDDEN-DEBT (thin-Lean ruling 2026-08-11): this establishes
    `tp:SSORTFN1` — the emitted consp-or-nil `IF` corollary — Lean-side;
    content ACL2 derives. Statement kept as the named premise; proof
    retired to `sorry`. UNLOCK: TP-replay discharge for the witness
    fns. -/
theorem dis_ssortfn1_tp (w : World)
    (h_ssortfn1_insert : w.defs.get? ssortfn1_insert_sym
      = some ([eS, xS], ssortfn1InsertBody))
    (h_ssortfn1 : w.defs.get? ssortfn1_sym = some ([xS], ssortfn1Body))
    (h_no_consp : w.defs.get? ({ name := "CONSP" } : Symbol) = none)
    (h_no_car : w.defs.get? ({ name := "CAR" } : Symbol) = none)
    (h_no_cdr : w.defs.get? ({ name := "CDR" } : Symbol) = none)
    (h_no_cons : w.defs.get? ({ name := "CONS" } : Symbol) = none)
    (h_no_lexorder : w.defs.get? ({ name := "LEXORDER" } : Symbol) = none)
    (e' : Env) (a0 v : SExpr)
    (h : ∃ N, ∀ f ≥ N, evalOpt f w e'
      (SExpr.cons (SExpr.atom (Atom.symbol ssortfn1_sym))
        (SExpr.cons a0 SExpr.nil)) = some v) :
    (bif Logic.toBool (Logic.consp v) then SExpr.t
      else Logic.equal v SExpr.nil) = SExpr.t := by
  sorry

end ACL2.Worlds.Sorting
