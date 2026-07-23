(in-package "ACL2")

; COVERAGE/:linear (map frame: rule classes — UNCOVERED as authored
; subject): a :linear rule + a theorem whose proof consults the linear
; arithmetic database. Pins how linear-rule application appears (or
; does not appear) in the log.

(defun sz (x)
  (if (consp x) (+ 1 (sz (cdr x))) 0))

(defthm sz-nonneg
  (<= 0 (sz x))
  :rule-classes :linear)

(defthm sz-cons-grows
  (< (sz x) (sz (cons a x))))
