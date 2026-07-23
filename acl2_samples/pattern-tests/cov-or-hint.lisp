(in-package "ACL2")

; COVERAGE/:or hint (gap audit A2 — *top-hint-keywords*): forks the
; proof attempt into disjunctive branches (Goal.1/Goal.2 clause-id
; shapes expected).

(defun fw (x) (if (consp x) (fw (cdr x)) 0))

(defthm fw-zero
  (equal (fw x) 0)
  :hints (("Goal" :or ((:induct (fw x))
                       (:in-theory (enable fw))))))
