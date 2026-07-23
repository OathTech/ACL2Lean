(in-package "ACL2")

; COVERAGE/encapsulate (map frame: event forms — UNCOVERED): a
; constrained function via encapsulate + a theorem proved from the
; constraint alone. Pins what the instrumentation emits for
; encapsulate/local/constraint events.

(encapsulate
 (((cf *) => *))
 (local (defun cf (x) (declare (ignore x)) 0))
 (defthm cf-numberp (acl2-numberp (cf x))))

(defthm cf-plus-comm
  (equal (+ (cf a) (cf b)) (+ (cf b) (cf a))))
