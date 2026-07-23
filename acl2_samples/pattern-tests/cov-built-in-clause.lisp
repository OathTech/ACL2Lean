(in-package "ACL2")

; COVERAGE/:built-in-clause (rule classes — UNCOVERED): a clause ACL2
; may recognize as true during clausification. Pins the rule's
; admission shape (and any bic hits in later proofs).

(defun szb (x)
  (if (consp x) (+ 1 (szb (cdr x))) 0))

(defthm szb-nonneg-bic
  (<= 0 (szb x))
  :rule-classes :built-in-clause)

(defthm szb-plus-nonneg
  (<= 0 (+ (szb x) (szb y))))
