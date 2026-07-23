(in-package "ACL2")

; COVERAGE/quirk backlog — the rewrite-equal NIL-form shapes
; (rewrite.lisp:18089-98, driver inventory [bridge] entry 1): a
; theorem whose literals put (EQUAL x 'NIL) against its (IF x 'NIL 'T)
; normal form, pinning which orientation the log records.

(defun z1 (x) (equal x nil))

(defthm z1-is-not
  (equal (z1 x) (not x)))

(defthm z1-decides
  (implies (not (z1 x)) x)
  :rule-classes nil)
