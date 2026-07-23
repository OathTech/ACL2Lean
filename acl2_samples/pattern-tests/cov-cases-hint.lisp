(in-package "ACL2")

; COVERAGE/:cases hint (map frame: hints — UNCOVERED): pins the
; emitted structure of a :cases split.

(defun sgn (n)
  (cond ((not (integerp n)) 0)
        ((< n 0) -1)
        ((equal n 0) 0)
        (t 1)))

(defthm sgn-square-nonneg
  (<= 0 (* (sgn n) (sgn n)))
  :hints (("Goal" :cases ((< n 0) (equal n 0)))))
