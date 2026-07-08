; Differential corpus: integer arithmetic (modeled surface — all `match`).
; Format: Tests/differential/README.md. Each test = one `;@ <class>` line then
; one form. Evaluated in the empty world.

;@ match
(binary-+ '2 '3)
;@ match
(binary-+ '-5 '5)
;@ match
(binary-+ '-2 '-3)
;@ match
(binary-* '3 '4)
;@ match
(binary-* '-2 '6)
;@ match
(unary-- '7)
;@ match
(binary-+ (binary-+ '1 '2) '3)
;@ match
(- '10 '3)
;@ match
(- '3 '10)
;@ match
(- '7)
;@ match
(* '6 '7)
;@ match
(* '-3 '-4)
;@ match
(1+ '41)
;@ match
(1- '0)
;@ match
(binary-+ '0 '0)
;@ match
(binary-* '0 '99)

; boundary / large integers (evalOpt uses Int/Nat — no overflow; pin it)
;@ match
(binary-* '1000000 '1000000)
;@ match
(binary-+ '999999999999 '1)
;@ match
(unary-- '-2147483648)
; deeply nested arithmetic (evalOpt recursion / fuel)
;@ match
(binary-+ (binary-+ (binary-+ (binary-+ '1 '2) '3) '4) '5)
