(in-package "ACL2")

; Wild anchor: BVCHOP-UPPER-BOUND's EXPT survives if-interp's call-stack.
; Axis: an interpreter builtin that is an ordinary ACL2 defun.
(defthm expt-choice
  (equal (expt 2 (if p 0 1)) (if p 1 2))
  :hints (("Goal" :in-theory '((:executable-counterpart expt)))))

; Axis: primitive CAR's guard succeeds on '(3), fails on '0.
; The failed-guard application survives cons-term and is executed later.
(defthm car-choice
  (equal (car (if p 0 '(3))) (if p nil 3))
  :hints (("Goal" :in-theory '((:executable-counterpart car)))))
