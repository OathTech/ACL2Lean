; Differential corpus: LAMBDA APPLICATIONS — ACL2's internal binding form.
; `let`/`mv-let` TRANSLATE to ((LAMBDA (formals) body) actuals), and the
; replay path consumes translated terms, so the interpreter's lambda
; semantics are load-bearing for every replayed statement over a world whose
; defun bodies bind locals (S2 arc, 2026-07-24). Raw lambda applications are
; legal ACL2 top-level input, so the semantics pin differentially.
; SEMANTICS (header corrected per S2 audit F5/F6, 2026-07-25): our arm
; evaluates the actuals in the OUTER env and the body in the outer env
; EXTENDED by formals↦values. ACL2's own ev-rec uses a FRESH alist
; (translate.lisp: (pairlis$ formals args)) — but ACL2 only ever sees
; TRANSLATED lambdas, which lambda-to-let/make-lambda-term CLOSE over
; their lexical scope ("lambdas must be closed in ACL2"). We consume the
; surface form WITHOUT translating, so an open inner body IS observable
; to us, and the extension is what reproduces translate's closure: the
; nested entry below is exactly the discriminating pin (extension ⇒ 15,
; matching ACL2 after ITS translate closes the inner lambda; a fresh env
; gives 10). The other entries have closed bodies and pass under either
; semantics — the nested pin is the one carrying the decision.

;@ match
((lambda (y) (binary-* y y)) '3)

;@ match
((lambda (x y) (cons x y)) '1 '2)

;@ match
((lambda (y) y) 'a)

; parallel binding: both actuals see the outer scope, not each other
;@ match
((lambda (x y) (cons y x)) '1 '2)

; nested lambda application (let inside let after translation)
;@ match
((lambda (y) ((lambda (z) (binary-+ y z)) (binary-* y '2))) '5)

; formal shadows a builtin fn name in VALUE position (namespaces are
; separate: CAR the formal vs car the function)
;@ match
((lambda (car) (cons car car)) '7)

; the surface macro and its translation agree
;@ match
(let ((y '3)) (binary-* y y))

;@ match
(let ((x '1) (y '2)) (cons x y))

; quoted lambda-looking constant is NOT an application — stays inert data
;@ match
(quote (lambda (y) y))

; DUPLICATE bound variable (BUG-018, S2 audit 2026-07-25): ACL2's translate
; REFUSES both spellings ("improper let expression … binds X, which occurs
; more than once"); we evaluate — and the two spellings of ACL2's ONE
; construct even disagree (lambda arm first-formal-wins ⇒ 1; surface LET
; fold last-binding-wins ⇒ 2).
;@ known-bug bug:BUG-018 lean 1
((lambda (x x) x) '1 '2)
;@ known-bug bug:BUG-018 lean 2
(let ((x '1) (x '2)) x)

; lambda carrying a DECLARE form: legal ACL2 (lambda-to-let accepts length
; ≥ 3), unmodeled by our exact-3-shape arm — masquerade gap, documented
;@ unsupported
((lambda (x) (declare (ignore x)) 'a) '1)
