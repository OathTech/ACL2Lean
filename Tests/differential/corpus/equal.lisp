; Differential corpus: equal / eql, incl. a KNOWN DIVERGENCE.

;@ match
(equal '(1 2) '(1 2))
;@ match
(equal '(1 2) '(1 3))
;@ match
(equal '3 '3)
;@ match
(equal 'a 'a)
;@ match
(equal 'a 'b)
;@ match
(equal 'nil '())
;@ match
(equal '(1 (2 3)) '(1 (2 3)))
;@ match
(eql '5 '5)
;@ match
(eql '5 '6)
;@ match
(equal '5 'a)
;@ match
(equal 'nil '(1))

; Number normalization: ACL2's reader normalizes a denominator-1 rational to
; the integer — 5/1 IS 5 — so (equal '5 '5/1) is T. This was a known divergence
; (the parser built a distinct .rational 5/1); FIXED 2026-07-07 by routing the
; parser through Logic.mkNumber. Now `match`. See number-normalization.lisp.
;@ match
(equal '5 '5/1)
;@ match
(integerp '5/1)
