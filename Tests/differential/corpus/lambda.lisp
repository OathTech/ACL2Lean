; Differential corpus: LAMBDA APPLICATIONS — ACL2's internal binding form.
; `let`/`mv-let` TRANSLATE to ((LAMBDA (formals) body) actuals), and the
; replay path consumes translated terms, so the interpreter's lambda
; semantics are load-bearing for every mirror statement over a world whose
; defun bodies bind locals (S2 arc, 2026-07-24). Raw lambda applications are
; legal ACL2 top-level input, so the semantics pin differentially.
; ACL2's ev: actuals evaluated in the OUTER env; the body evaluated in a
; FRESH env binding exactly the formals (translate enforces body closure, so
; a legal input can never observe the difference from an extending env —
; the fresh env mirrors ev's (pairlis$ formals args)).

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
