; Differential corpus: user-defined recursive functions, evaluated in the
; `simple` book world (my-len, my-app). Exercises the ;@world directive and
; defun evaluation in both interpreters.
;@world simple

;@ match
(my-len '(1 2 3))
;@ match
(my-len 'nil)
;@ match
(my-len '7)
;@ match
(my-app '(1 2) '(3 4))
;@ match
(my-app 'nil '(1 2))
;@ match
(my-app '(a b) '(c d e))
;@ match
(my-len (my-app '(1 2 3) '(4 5)))
;@ match
(binary-+ (my-len '(1 2)) (my-len '(3 4 5)))
;@ match
(my-len (my-app '(1 2 3) 'nil))
; deeper composition
;@ match
(my-app (my-app '(1) '(2)) '(3))
;@ match
(len (my-app '(1 2) '(3 4 5)))
;@ match
(equal (my-app '(1 2) '(3)) '(1 2 3))
;@ match
(if (consp '(1)) (my-len '(1 2)) '0)
;@ match
(binary-+ (len '(a b)) (my-len '(c d e)))
