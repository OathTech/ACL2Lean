; Differential corpus: the BUG-021 primitives (evenp/oddp/expt/
; string-append), fixed + wired 2026-07-26. Guard-off oracle semantics:
; evenp = (integerp (* x 1/2)) with * coercing non-numbers to 0;
; expt follows ACL2's cond order (zip exponent -> 1, zero/non-numeric
; base -> 0, exact rational power otherwise); string-append coerces
; PER-ARG. All entries verified against acl2/saved_acl2 by the harness.

;@ match
(evenp nil)
;@ match
(evenp 'abc)
;@ match
(evenp "abc")
;@ match
(evenp '3)
;@ match
(evenp '-4)
;@ match
(evenp '3/2)
;@ match
(oddp '3/2)
;@ match
(oddp '4)
;@ match
(oddp nil)
;@ match
(expt '1/2 '2)
;@ match
(expt '2 '-2)
;@ match
(expt '-1/2 '3)
;@ match
(expt '-2 '-3)
;@ match
(expt 'a '2)
;@ match
(expt 'a '0)
;@ match
(expt '0 '-1)
;@ match
(expt '5 'b)
;@ match
(string-append "ab" "cd")
;@ match
(string-append "ab" 'c)
;@ match
(string-append 'c "ab")
;@ match
(string-append 'a 'b)
