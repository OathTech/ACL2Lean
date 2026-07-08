; Differential corpus: fix-coercion of non-numbers (the total, logical
; semantics evalOpt models — ACL2 under (set-guard-checking nil), which the
; differential session sets). Non-numbers coerce to 0 in arithmetic.

;@ match
(binary-+ 'nil '3)
;@ match
(binary-+ 't '3)
;@ match
(binary-+ '(1 2) '5)
;@ match
(fix '5)
;@ match
(fix 'nil)
;@ match
(fix 't)
;@ match
(1+ 'nil)
;@ match
(binary-* 'nil '5)
;@ match
(binary-* '(a b) '3)
;@ match
(< 'nil '1)
;@ match
(< 'abc 'def)
;@ match
(- 'nil '3)
;@ match
(1+ '(1 2))
;@ match
(< '0 'nil)
