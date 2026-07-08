; Differential corpus: rational arithmetic (modeled — exercises mkNumber
; gcd-normalization and sign handling).

;@ match
(binary-+ '1/2 '1/2)
;@ match
(binary-+ '1/3 '1/6)
;@ match
(binary-+ '1/3 '2/3)
;@ match
(binary-* '1/2 '4)
;@ match
(binary-* '2/3 '3/4)
;@ match
(unary-/ '4)
;@ match
(binary-+ '1/6 '1/6)
;@ match
(unary-/ '5)
;@ match
(unary-/ '1/3)
;@ match
(binary-* '1/2 '2/3)
; rationals that reduce to integers, and sign normalization
;@ match
(binary-* '3 '1/3)
;@ match
(binary-+ '-1/2 '-1/2)
;@ match
(binary-* '-1/2 '-1/2)
;@ match
(unary-/ '-3)
