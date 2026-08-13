import ACL2Lean.Imported.Sorting

/-! # Equisort WITNESS exec kits + TP dischargers (close-out queue item 1)

The equisort scopes' `:LOCAL-WITNESS` defuns are insertion-sort clones
(`SORTFN1-INSERT`/`SORTFN1` and the `SS` pair differ from the isort
book's `INSERT`/`ISORT` only in their self-call names).  This module
builds their exec kits — bodies transcribed from the emitted
`(:DEFUN …)` events (equisort.proof-log lines 123/127/13674/13678).

All four witness TP dischargers are now RETIRED in favour of the
driver's TP prover: `tp:SORTFN1-INSERT`/`tp:SSORTFN1-INSERT` with the
CONS return-path shape (TP-replay arc increment 2) and
`tp:SORTFN1`/`tp:SSORTFN1` with the CALLEE-TP shape (increment 3) — see
the retirement notes below. -/

namespace ACL2.Worlds.Sorting

open ACL2

-- `eT`/`xT`/`eS`/`xS` come from `Imported/Sorting.lean` (same namespace,
-- identical definitions): the local private copies were removed when the
-- book layer's split-out modules needed them (mirror wave 2026-08-11).
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

/-! `dis_sortfn1_insert_tp` is RETIRED (TP-replay arc increment 2,
2026-08-13): `(CONSP (SORTFN1-INSERT E X))` now arrives from the
driver's TP prover, off the fn's own emitted `:TYPE-PRESCRIPTION`
corollary + `:LEAVES` (all three emitted leaves are `CONS`es, verdict
`3072` = `*ts-cons*`). -/

/-! `dis_sortfn1_tp` is RETIRED (TP-replay arc increment 3, 2026-08-13):
`tp:SORTFN1` — the emitted consp-or-nil `IF` corollary
`(IF (CONSP (SORTFN1 X)) 'T (EQUAL (SORTFN1 X) 'NIL))`, `:BASICTS 3200`
= `*ts-cons*` ∪ `*ts-nil*` — now arrives from the driver's TP prover.
Its two emitted leaves are `'NIL` (verdict `128`, the quote arm) and
`(SORTFN1-INSERT (CAR X) (SORTFN1 (CDR X)))` (verdict `3072`, inside
3200): a CALLEE call whose own emitted `(CONSP (SORTFN1-INSERT E X))`
corollary — itself proved by the same prover since increment 2 —
supplies the leaf, lifted across the class gap by the registered
`CONSP` ⇒ consp-or-nil implication. -/

/-! `dis_ssortfn1_insert_tp` is RETIRED (TP-replay arc increment 2,
2026-08-13): same route as its SORTFN1 twin — the emitted
`(CONSP (SSORTFN1-INSERT E X))` corollary + `:LEAVES` (three `CONS`
leaves, verdict `3072`). -/

/-! `dis_ssortfn1_tp` is RETIRED (TP-replay arc increment 3,
2026-08-13): the SORTFN1 route exactly, on the SSORTFN1 clone — same
emitted corollary class, same leaf verdicts, same callee-TP step. -/

end ACL2.Worlds.Sorting
