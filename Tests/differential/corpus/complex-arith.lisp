; NS1 / BUG-009: exact complex-rational values and guard-off completion.
; Uses ACL2's primitive arithmetic heads, also understood by the empty-world
; Lean evaluator; ordinary library definitions remain world-resolved.
;@ match
(equal '#C(2/4 0/3) '1/2)
;@ match
(equal '#c(0 1) '#C(0 1))
;@ match
'#C(2/4 -6/8)
;@ match
(list (acl2-numberp '#C(2 3)) (rationalp '#C(2 3)) (integerp '#C(2 3)) (complex-rationalp '#C(2 3)))
;@ match
(list (realpart '#C(2/3 -4/5)) (imagpart '#C(2/3 -4/5)))
;@ match
(list (numerator '#C(2/3 4/5)) (denominator '#C(2/3 4/5)))
;@ match
(list (complex 'foo 2) (complex 3 'foo) (complex '#C(1 2) '#C(3 4)))
;@ match
(list (fix '#C(1 2)) (ifix '#C(1 2)) (nfix '#C(1 2)))
;@ match
(binary-+ '#C(2/3 -4/5) '#C(1/3 4/5))
;@ match
(unary-- '#C(2/3 -4/5))
;@ match
(binary-* '#C(2 3) '#C(4 -5))
;@ match
(unary-/ '#C(2 3))
;@ match
(binary-* '#C(2 3) (unary-/ '#C(4 -5)))
;@ match
(binary-* '#C(2 3) (unary-/ 0))
;@ match
(list (binary-+ '#C(2 3) 'foo) (binary-* '#C(2 3) 'foo) (unary-/ 'foo) (unary-- 'foo))
;@ match
(list (evenp '#C(2 3)) (oddp '#C(2 3)))
;@ match
(list (expt '#C(0 1) 2) (expt '#C(0 1) -1) (expt '#C(2 3) 0) (expt '#C(2 3) 'foo))
;@ match
(expt '#C(0 2) -3)
;@ match
(list (< '#C(0 1) 0) (< 0 '#C(0 1)) (< '#C(0 -1) 0) (< '#C(-2 100) -1) (< '#C(2 3) '#C(2 4)))
;@ match
(list (lexorder 100 '#C(-2 3)) (lexorder '#C(-2 3) 100) (lexorder '#C(2 3) '#C(2 4)) (lexorder '#C(2 3) #\A))
;@ match
(list (lexorder '#C(1 2) '#C(1 2)) (lexorder '#C(1 3) '#C(1 2)) (lexorder '#C(-1 100) '#C(0 -100)))
