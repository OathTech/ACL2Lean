(in-package "ACL2")

; COVERAGE/:congruence + :equivalence (map frame: rule classes —
; UNCOVERED): defequiv + defcong — user equivalence relations, the L2
; lane's native constructs. Pins the emitted shapes of the generated
; equivalence obligations and a congruence-driven rewrite.

(defun same-len (x y) (equal (len x) (len y)))

(defequiv same-len)

(defcong same-len equal (len x) 1)

(defthm same-len-cdr-cons
  (same-len (cons a (cdr (cons b x))) (cons c x)))
