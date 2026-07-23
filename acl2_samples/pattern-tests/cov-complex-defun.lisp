(in-package "ACL2")

; COVERAGE/complex minimal repro variant (frontier follow-up to
; cov-complex, which halted at its FIRST event — a defthm): does a
; DEFUN whose body carries a #c literal halt the instrumentation the
; same way, or is the halt defthm-specific? Isolates the capture
; frontier's boundary.

(defun cplus (x) (+ x #c(0 1)))

(defthm cplus-type
  (acl2-numberp (cplus 3)))
