; Differential corpus: NUMERATOR / DENOMINATOR / REALPART / IMAGPART /
; COMPLEX-RATIONALP (sorting-completion arc, 2026-07-28) — the head set of
; ACL2-COUNT's emitted ground-zero body with no defun snapshot of their own
; (axiomatic primitives), so every admission (termination) waterfall that
; unfolds ACL2-COUNT demands them (qsort's termination replay + the msort
; ACL2-COUNT-EVENS-* rows surfaced the frontier). Guard-off oracle
; semantics: rationals are stored canonically (lowest terms, positive
; denominator, sign on the numerator) — ACL2's own convention — so
; numerator/denominator read the stored component; non-rationals complete
; to 0 / 1. The value space has NO complex numbers (#c is a pinned
; unsupported reader class), so on representable values realpart is the
; number itself (0 for non-numbers), imagpart is 0, complex-rationalp is
; NIL. All entries verified against acl2/saved_acl2 by the harness; the
; 6/4 entries also pin reader canonicalization.

;@ match
(numerator '5)
;@ match
(numerator '-5)
;@ match
(numerator '0)
;@ match
(numerator '3/4)
;@ match
(numerator '-3/4)
;@ match
(numerator '6/4)
;@ match
(numerator 'a)
;@ match
(numerator nil)
;@ match
(numerator "ab")
;@ match
(numerator #\a)
;@ match
(realpart '5)
;@ match
(realpart '-5)
;@ match
(realpart '3/4)
;@ match
(realpart 'a)
;@ match
(realpart nil)
;@ match
(realpart "ab")
;@ match
(imagpart '5)
;@ match
(imagpart '-3/4)
;@ match
(imagpart 'a)
;@ match
(imagpart nil)
;@ match
(complex-rationalp '5)
;@ match
(complex-rationalp '3/4)
;@ match
(complex-rationalp 'a)
;@ match
(complex-rationalp nil)
;@ match
(complex-rationalp "ab")
;@ match
(complex-rationalp #\a)
;@ match
(denominator '5)
;@ match
(denominator '-5)
;@ match
(denominator '3/4)
;@ match
(denominator '-3/4)
;@ match
(denominator '6/4)
;@ match
(denominator 'a)
;@ match
(denominator nil)
;@ match
(denominator "ab")
;@ match
(denominator #\a)
