; NS1: predefined REALFIX, axioms.lisp's (IF (RATIONALP X) X '0).
; The actual complex-elimination child unfolds it on both components.
;@ match
(realfix 0)
;@ match
(realfix -7)
;@ match
(realfix 1/3)
;@ match
(realfix -6/8)
;@ match
(realfix '#C(3/4 0))
;@ match
(realfix '#C(3/4 1))
;@ match
(realfix '#C(0 -1))
;@ match
(list (realfix nil) (realfix t) (realfix 'foo) (realfix :foo) (realfix "foo") (realfix #\A) (realfix '(1 . 2)))
;@ match
(binary-+ (realfix (realpart '#C(2/3 -4/5))) (binary-* '#C(0 1) (realfix (imagpart '#C(2/3 -4/5)))))
;@ match
(realfix (binary-+ '#C(1/2 3/4) '#C(1/2 -3/4)))
;@ refuse
(realfix)
;@ refuse
(realfix 1 2)
