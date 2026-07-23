(in-package "ACL2")

; COVERAGE/verify-guards (event forms — UNCOVERED): deferred guard
; verification — pins whether/how guard obligations appear in the log
; (they are proofs too).

(defun gplus (x)
  (declare (xargs :guard (integerp x) :verify-guards nil))
  (+ x 1))

(verify-guards gplus)

(defthm gplus-adds
  (implies (integerp x) (equal (gplus x) (+ 1 x))))
