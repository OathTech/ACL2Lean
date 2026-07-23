(in-package "ACL2")

; COVERAGE/theory events (gap audit A6): deftheory + in-theory EVENTS
; (not hints) changing later proofs' rule availability.

(defun dtf (x) (if (consp x) (dtf (cdr x)) 0))

(defthm dtf-opens
  (equal (dtf (cons a x)) (dtf x)))

(deftheory my-th '(dtf dtf-opens))

(in-theory (disable my-th))

(defthm dtf-two
  (equal (dtf (cons a (cons b nil))) 0)
  :hints (("Goal" :in-theory (enable my-th))))
