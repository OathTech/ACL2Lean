(in-package "ACL2")

; PROBE/beta-equiv (S2 audit 2026-07-25, reviewer artifact iff.lisp):
; a lambda application in an IF test — the body rewrites under the
; ambient IFF geneqv (bar-true is an :EQUIV IFF step), while the
; emitted :LAMBDA-BODY beta step asserts :EQUIV EQUAL for the same
; replacement. PINS the false-equiv emission defect (next fork batch:
; emit the real relation; L2 says R is never an enum).

(defstub foo (x) t)
(defstub bar (x) t)

(defaxiom bar-true (iff (bar x) t))

(defun p (a)
  (if (let ((y (foo a)))
        (if (consp y) (bar y) (bar y)))
      'yes 'no))

(defthm probe-iff
  (equal (p a) 'yes)
  :rule-classes nil)
