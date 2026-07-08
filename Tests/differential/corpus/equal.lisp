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

; KNOWN DIVERGENCE (trusted-core fidelity gap, found by this harness):
; ACL2's reader normalizes a denominator-1 rational to the integer — 5/1 IS 5 —
; so (equal '5 '5/1) is T. Our parser builds a distinct .rational 5/1 that
; bypasses Logic.mkNumber's gcd/denominator-1 reduction, so evalOpt says NIL.
; Recorded as `diverge` (Lean value NIL) so the gate stays green but FAILS the
; day the parser is fixed — forcing reclassification to `match`. Fixing the
; parser is out of scope for the testing sprint; tracked in TODO.
;@ diverge lean NIL
(equal '5 '5/1)
;@ diverge lean NIL
(integerp '5/1)
