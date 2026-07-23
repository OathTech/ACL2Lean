(in-package "ACL2")

; COVERAGE/verify-guards (event forms): iteration 2 (S1) — the first
; version's guard obligation was trivial and left ZERO log events; this
; one forces a real guard proof (car/cdr/+ guards under integer-listp)
; so whatever the guard prover emits (or fails to emit) is pinned.

(defun gsum (x)
  (declare (xargs :guard (integer-listp x) :verify-guards nil))
  (if (consp x)
      (+ (car x) (gsum (cdr x)))
    0))

(verify-guards gsum)

(defthm gsum-of-nil
  (equal (gsum nil) 0)
  :rule-classes nil)
