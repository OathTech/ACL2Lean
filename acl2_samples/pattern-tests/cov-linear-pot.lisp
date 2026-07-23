(in-package "ACL2")

; COVERAGE/linear-pot integration (rewriter situations): iteration 2 —
; the first version was proved whole by (:EXECUTABLE-COUNTERPART
; TAU-SYSTEM) (probe finding: tau grabs simple linear goals before the
; pot list is consulted). Tau disabled here to expose the linear
; machinery.

(defun szl (x) (if (consp x) (+ 1 (szl (cdr x))) 0))

(defthm szl-linear
  (<= 0 (szl x))
  :rule-classes :linear)

(defthm szl-bound
  (< (szl x) (+ 1 (szl x) (szl y)))
  :hints (("Goal" :in-theory (disable (:executable-counterpart tau-system)))))
