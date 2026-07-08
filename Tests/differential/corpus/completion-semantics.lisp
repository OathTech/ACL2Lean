; Differential corpus: COMPLETION-AXIOM semantics — how the modeled primitives
; behave on OUT-OF-DOMAIN inputs (ACL2's total/logical semantics, the axioms
; completion-of-* in axioms.lisp). This is the fidelity-critical trust-anchor
; behavior: evalOpt must match ACL2's totalization exactly. All `match` — these
; validate that our fix-coercion / default rules agree with the axioms.

; completion-of-< : a non-number compares as if it were 0 (default-<-1/-2).
;   (< non-num y) = (< 0 y) ; (< x non-num) = (< x 0)
;@ match
(< 'nil 'nil)
;@ match
(< 'abc '-5)
;@ match
(< '-5 'abc)
;@ match
(< 'nil '-1)
;@ match
(< '-1 'nil)
;@ match
(< 'foo 'bar)

; completion-of-+ / -* : non-numbers coerce to 0
;@ match
(binary-+ 'abc 'def)
;@ match
(binary-* 'abc '5)

; completion-of-car / -cdr : non-cons → nil; cons-car-cdr on a non-cons →
; (cons nil nil)
;@ match
(car 'abc)
;@ match
(cdr 'abc)
;@ match
(equal (cons (car '5) (cdr '5)) (cons 'nil 'nil))
