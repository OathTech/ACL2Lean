(in-package "ACL2")

; COVERAGE/:generalize (rule classes — UNCOVERED): a :generalize rule
; that restricts generalization of szg terms, + a theorem whose proof
; generalizes. Pins the generalize-rule pickup in the log.

(defun szg (x)
  (if (consp x) (+ 1 (szg (cdr x))) 0))

(defthm szg-type-gen
  (and (integerp (szg x)) (<= 0 (szg x)))
  :rule-classes :generalize)

(defun dup (x)
  (if (consp x) (cons (car x) (cons (car x) (dup (cdr x)))) nil))

(defthm szg-dup
  (equal (szg (dup x)) (* 2 (szg x))))
