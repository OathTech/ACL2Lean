(in-package "ACL2")

; COVERAGE/:type-set-inverter (gap audit A3 — the other missing
; rule-class token; defthm.lisp:7485). The documented shape inverts a
; type-set into a predicate.

(defun my-natp (x)
  (and (integerp x) (<= 0 x)))

(defthm my-natp-inverts
  (equal (and (integerp x) (not (< x 0)))
         (my-natp x))
  :rule-classes :type-set-inverter)
