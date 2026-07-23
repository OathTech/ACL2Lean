(in-package "ACL2")

; COVERAGE/quirk backlog — :TYPESET-decode probes (driver inventory
; [rederive] entry 6): recognizer verdicts across DISTINCT type-set
; bit patterns; the emitted :TYPESET/:TRUETS integers are the
; principled data the replay should decode instead of re-deriving.

(defun probe (x)
  (cond ((integerp x) 0)
        ((rationalp x) 1)
        ((symbolp x) 2)
        ((consp x) 3)
        ((stringp x) 4)
        (t 5)))

(defthm probe-of-positive
  (implies (and (integerp x) (< 0 x))
           (equal (probe x) 0)))

(defthm probe-of-ratio
  (implies (and (rationalp x) (not (integerp x)))
           (equal (probe x) 1)))

(defthm probe-of-cons
  (equal (probe (cons a b)) 3))
