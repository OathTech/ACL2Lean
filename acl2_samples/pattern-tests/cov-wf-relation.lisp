(in-package "ACL2")

; COVERAGE/:well-founded-relation (rule classes — UNCOVERED): a
; user-defined well-founded relation (trivial o< image) + a defun
; admitted under it. Pins the wf-relation rule shape and the
; admission's justification fields (:REL should name MY-LT).

(defun my-mp (x) (o-p x))
(defun my-lt (x y) (o< x y))

(defthm my-lt-is-well-founded
  (and (implies (my-mp x) (o-p (identity x)))
       (implies (and (my-mp x) (my-mp y) (my-lt x y))
                (o< (identity x) (identity y))))
  :rule-classes :well-founded-relation)

(defun cnt-down (n)
  (declare (xargs :well-founded-relation my-lt :measure (nfix n)))
  (if (zp n) 0 (cnt-down (- n 1))))

(defthm cnt-down-zero
  (equal (cnt-down n) 0))
