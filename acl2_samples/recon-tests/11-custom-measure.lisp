(in-package "ACL2")

;; FEATURE: a function with an EXPLICIT, non-acl2-count measure that gets inducted
;; on in a proof.  Exercises that the emitted :MEASURE is the DECLARED measure
;; (nfix n), not acl2-count, and that the step substitutes n:=(- n 2) (not a cdr).
;; The property is a VALUE bound (not a type fact), so ACL2 must unroll by
;; induction rather than read it off cd2's type-prescription.

(defun cd2 (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (if (equal n 1)
        0
      (+ 1 (cd2 (- n 2))))))

;; inducts on cd2's scheme (measure (nfix n)); step case substitutes n:=(- n 2).
(defthm cd2-bound
  (<= (cd2 n) (nfix n))
  :rule-classes nil)
