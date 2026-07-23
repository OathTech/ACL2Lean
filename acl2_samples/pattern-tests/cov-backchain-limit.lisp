(in-package "ACL2")

; COVERAGE/backchain limits (rewriter situations — UNCOVERED): a rule
; with :backchain-limit-lst 0 (hyp relievable only by type-set). Pins
; the stored rule's limit field and a limit-constrained application.

(defun bfn (x) (declare (ignore x)) 0)

(defthm bfn-rule
  (implies (integerp x) (equal (bfn x) 0))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(in-theory (disable bfn))

(defthm bfn-use
  (implies (integerp n) (equal (bfn n) 0)))
