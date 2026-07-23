(in-package "ACL2")

; COVERAGE/:rewrite-quoted-constant (rule classes). S1 CORRECTION
; (2026-07-23): the original form was rejected — the conclusion must be
; a NON-EQUAL equivalence: Form [1] between two quoted constants, or
; Form [2] (fn var) ~ var for monadic fn (error inhibited). Form [1]
; via IFF below.

(defun qnorm (x)
  (if (integerp x) x 0))

(defthm qnorm-idempotent
  (equal (qnorm (qnorm x)) (qnorm x)))

(defthm zero-iff-t
  (iff '0 't)
  :rule-classes :rewrite-quoted-constant)
