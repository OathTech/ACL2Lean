(in-package "ACL2")

; COVERAGE/guard-vs-logic distinction (value surface — UNCOVERED): a
; guarded fn applied OUTSIDE its guard in a theorem — logic-mode
; reasoning ignores guards entirely (car nil = nil). Pins that guards
; leave no trace in the proof surface.

(defun gsub (x)
  (declare (xargs :guard (consp x)))
  (car x))

(defthm gsub-of-nil
  (equal (gsub nil) nil))
